const std = @import("std");

const ir = @import("../ir.zig");
const rega = @import("../rega.zig");
const sema = @import("../sema.zig");

pub const any_register = 0xFF;

pub const backends = struct {
    pub const aarch64 = @import("aarch64.zig");
    pub const x86_64 = @import("x86_64.zig");
};

pub const Backend = struct {
    elf_machine: std.elf.EM,
    pointer_type: ir.InstrType,
    register_name: *const fn(u8) []const u8,

    reg_alloc: *const fn(ir.DeclIndex.Index, *rega.ParamReplacement) anyerror!void,
    write_decl: *const fn(
        writer: *Writer,
        decl_idx: ir.DeclIndex.Index,
        uf: rega.UnionFind,
        regs_to_save: []const u8,
    ) anyerror!?ir.BlockIndex.Index,

    optimizations: Optimizations,
    gprs: []const u8,
};

pub const Os = struct {
    default_abi: *const Abi,
    syscall_return_reg: u8,
    syscall_param_regs: []const u8,
    syscall_clobbers: []const u8,
};

pub const Abi = struct {
    return_regs: []const u8,
    param_regs: []const u8,
    ptr_param_regs: []const u8,
    caller_saved_regs: []const u8,
};

pub const Optimizations = struct {
    has_nonzero_constant_store: bool,
    has_divide_constant: bool,
    has_modulus_constant: bool,
    has_inplace_ops: bool,
};

pub var current_backend: *const Backend = undefined;
pub var current_os: *const Os = undefined;
pub var current_default_abi: *const Abi = undefined;

pub const RelocationType = enum {
    rel8_post_0,
    rel32_post_0,
    imm19_div4_shift5,
    imm26_div4,

    pub fn byteSize(self: @This()) usize {
        return switch(self) {
            .rel8_post_0 => 1,
            .rel32_post_0 => 4,
            else => unreachable,
        };
    }

    pub fn minDisplacement(self: @This()) isize {
        return switch(self) {
            .rel8_post_0 => -0x80,
            .rel32_post_0 => -0x80000000,
            .imm19_div4_shift5 => -(1 << 20),
            .imm26_div4 => -(1 << 27),
        };
    }

    pub fn maxDisplacement(self: @This()) usize {
        return switch(self) {
            .rel8_post_0 => 0x7F,
            .rel32_post_0 => 0x7FFFFFFF,
            .imm19_div4_shift5 => (1 << 20) - 4,
            .imm26_div4 => (1 << 27) - 4,
        };
    }
};

const Relocation = struct {
    relocation_type: RelocationType,
    output_offset: usize,

    fn resolve(self: @This(), output_bytes: []u8, relocation_target_offset: usize) void {
        switch(self.relocation_type) {
            .rel8_post_0 => {
                const rel = relocation_target_offset -% (self.output_offset +% 1);
                output_bytes[self.output_offset..][0..1].* = std.mem.toBytes(@as(i8, @intCast(@as(i64, @bitCast(rel)))));
            },
            .rel32_post_0 => {
                const rel = relocation_target_offset -% (self.output_offset +% 4);
                output_bytes[self.output_offset..][0..4].* = std.mem.toBytes(@as(i32, @intCast(@as(i64, @bitCast(rel)))));
            },
            .imm19_div4_shift5 => {
                const rel = @as(i19, @intCast(@as(i64, @bitCast(relocation_target_offset -% self.output_offset)) >> 2));
                std.mem.bytesAsValue(u32, output_bytes[self.output_offset..][0..4]).* |= @as(u32, @as(u19, @bitCast(rel))) << 5;
            },
            .imm26_div4 => {
                const rel = @as(i26, @intCast(@as(i64, @bitCast(relocation_target_offset -% self.output_offset)) >> 2));
                std.mem.bytesAsValue(u32, output_bytes[self.output_offset..][0..4]).* |= @as(u32, @as(u26, @bitCast(rel)));
            },
        }
    }
};

pub const Writer = struct {
    allocator: std.mem.Allocator = std.heap.page_allocator,
    output_bytes: std.ArrayListUnmanaged(u8) = .{},
    enqueued_blocks: std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, std.ArrayListUnmanaged(Relocation)) = .{},
    placed_blocks: std.AutoHashMapUnmanaged(ir.BlockIndex.Index, usize) = .{},
    enqueued_functions: std.AutoArrayHashMapUnmanaged(sema.InstantiatedFunction, std.ArrayListUnmanaged(Relocation)) = .{},
    placed_functions: std.AutoHashMapUnmanaged(sema.InstantiatedFunction, usize) = .{},
    function_sizes: std.AutoHashMapUnmanaged(sema.InstantiatedFunction, usize) = .{},

    pub fn attemptInlineEdge(self: *@This(), edge: ir.BlockEdgeIndex.Index) !?ir.BlockIndex.Index {
        const target_block = ir.edges.get(edge).target_block;
        if(self.placed_blocks.get(target_block)) |_| {
            return null;
        }
        if(!self.placed_blocks.contains(target_block)) {
            _ = try self.enqueued_blocks.getOrPutValue(self.allocator, target_block, .{});
        }
        return target_block;
    }

    pub fn currentOffset(self: *const @This()) usize {
        return self.output_bytes.items.len;
    }

    pub fn blockOffset(self: *const @This(), edge: ir.BlockEdgeIndex.Index) ?usize {
        const target = ir.edges.get(edge).target_block;
        return self.placed_blocks.get(target);
    }

    pub fn pickSmallestRelocationType(
        self: *const @This(),
        edge: ir.BlockEdgeIndex.Index,
        comptime types: []const std.meta.Tuple(&.{usize, RelocationType}),
    ) ?RelocationType {
        if(self.blockOffset(edge)) |offset| {
            inline for(types) |t| {
                const instr_size = t[1].byteSize() + t[0];
                const disp: isize = @bitCast(offset -% (self.currentOffset() + instr_size));
                if(disp >= t[1].minDisplacement() and disp <= t[1].maxDisplacement()) return t[1];
            }
        }
        return null;
    }

    pub fn addRelocation(self: *@This(), edge: ir.BlockEdgeIndex.Index, reloc: Relocation) !void {
        const reloc_target = ir.edges.get(edge).target_block;
        if(self.placed_blocks.get(reloc_target)) |offset| {
            reloc.resolve(self.output_bytes.items, offset);
        } else if(self.enqueued_blocks.getPtr(reloc_target)) |q| {
            try q.append(self.allocator, reloc);
        } else {
            var queue: std.ArrayListUnmanaged(Relocation) = .{};
            try queue.append(self.allocator, reloc);
            try self.enqueued_blocks.put(self.allocator, reloc_target, queue);
        }
    }

    pub fn addFunctionRelocation(self: *@This(), function: sema.InstantiatedFunction, reloc: Relocation) !void {
        if(self.placed_functions.get(function)) |offset| {
            reloc.resolve(self.output_bytes.items, offset);
        } else if(self.enqueued_functions.getPtr(function)) |q| {
            try q.append(self.allocator, reloc);
        } else {
            var queue: std.ArrayListUnmanaged(Relocation) = .{};
            try queue.append(self.allocator, reloc);
            try self.enqueued_functions.put(self.allocator, function, queue);
        }
    }

    pub fn writeRelocatedValue(self: *@This(), edge: ir.BlockEdgeIndex.Index, reloc_type: RelocationType) !void {
        try self.output_bytes.appendNTimes(self.allocator, 0xCC, reloc_type.byteSize());
        return self.addRelocation(edge, .{
            .output_offset = self.currentOffset() - reloc_type.byteSize(),
            .relocation_type = reloc_type,
        });
    }

    pub fn writeRelocatedFunction(self: *@This(), function: sema.InstantiatedFunction, reloc_type: RelocationType) !void {
        try self.output_bytes.appendNTimes(self.allocator, 0xCC, reloc_type.byteSize());
        return self.addFunctionRelocation(function, .{
            .output_offset = self.currentOffset() - reloc_type.byteSize(),
            .relocation_type = reloc_type,
        });
    }

    pub fn write(self: *@This(), bytes: []const u8) !void {
        try self.output_bytes.appendSlice(self.allocator, bytes);
    }

    pub fn writeInt(self: *@This(), comptime T: type, value: T) !void {
        try self.output_bytes.appendSlice(self.allocator, &std.mem.toBytes(value));
    }

    pub fn writeIntWithRelocation(
        self: *@This(),
        comptime T: type,
        value: T,
        edge: ir.BlockEdgeIndex.Index,
        reloc_type: RelocationType,
    ) !void {
        try self.writeInt(T, value);
        return self.addRelocation(edge, .{
            .output_offset = self.currentOffset() - @sizeOf(T),
            .relocation_type = reloc_type,
        });
    }

    pub fn writeIntWithFunctionRelocation(
        self: *@This(),
        comptime T: type,
        value: T,
        function: sema.InstantiatedFunction,
        reloc_type: RelocationType,
    ) !void {
        try self.writeInt(T, value);
        return self.addFunctionRelocation(function, .{
            .output_offset = self.currentOffset() - @sizeOf(T),
            .relocation_type = reloc_type,
        });
    }

    fn writeBlock(self: *@This(), bidx: ir.BlockIndex.Index, uf: rega.UnionFind, used_registers: []const u8) !?ir.BlockIndex.Index {
        var block = ir.blocks.get(bidx);
        var current_instr = block.first_decl;

        try self.placed_blocks.put(self.allocator, bidx, self.currentOffset());
        while(ir.decls.getOpt(current_instr)) |instr| {
            const next_block: ?ir.BlockIndex.Index = try current_backend.write_decl(self, ir.decls.getIndex(instr), uf, used_registers);
            if(next_block) |nb| return nb;
            current_instr = instr.next;
        }
        return null;
    }

    fn writeBlocks(self: *@This(), head_block: ir.BlockIndex.Index, uf: rega.UnionFind, used_registers: []const u8) !void {
        try self.enqueued_blocks.put(self.allocator, head_block, .{});
        var preferred_block: ?ir.BlockIndex.Index = null;

        while(true) {
            var current_block: ir.BlockIndex.Index = undefined;
            var block_relocs: std.ArrayListUnmanaged(Relocation) = undefined;

            if(preferred_block) |blk| {
                current_block = blk;
                block_relocs = self.enqueued_blocks.fetchSwapRemove(current_block).?.value;
                preferred_block = null;
            } else {
                const block = self.enqueued_blocks.popOrNull() orelse break;
                current_block = block.key;
                block_relocs = block.value;
            }

            for(block_relocs.items) |reloc| {
                reloc.resolve(self.output_bytes.items, self.currentOffset());
            }
            block_relocs.deinit(self.allocator);

            preferred_block = try self.writeBlock(current_block, uf, used_registers);
        }
    }

    fn writeSingleFunction(self: *@This(), function_c: sema.InstantiatedFunction) !void {
        var function = function_c; // Workaround for zig miscompilation :zany_face:
        const head_block = try ir.writeFunction(function);
        try ir.optimizeFunction(head_block);

        var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        const func_blocks = try ir.allBlocksReachableFrom(arena.allocator(), head_block);
        const uf = try rega.doRegAlloc(arena.allocator(), &func_blocks);

        var used_registers: std.BoundedArray(u8, 256) = .{};
        for(func_blocks.items) |blk_idx| {
            const blk = ir.blocks.get(blk_idx);
            var curr_decl = blk.first_decl;
            while(ir.decls.getOpt(curr_decl)) |decl| : (curr_decl = decl.next) {
                for(decl.reg_alloc_value) |oreg| {
                    if(oreg) |reg| {
                        if(std.mem.indexOfScalar(u8, used_registers.slice(), reg) == null) {
                            used_registers.appendAssumeCapacity(reg);
                        }
                    }
                }
            }

            try ir.dumpBlock(blk_idx, uf);
        }

        const function_offset = self.currentOffset();
        try self.placed_functions.put(self.allocator, function, function_offset);
        if(self.enqueued_functions.fetchSwapRemove(function)) |kv| {
            for(kv.value.items) |reloc| {
                reloc.resolve(self.output_bytes.items, function_offset);
            }
            var value_copy = kv.value;
            value_copy.deinit(self.allocator);
        }
        try self.writeBlocks(head_block, uf, used_registers.slice());
        try self.function_sizes.put(self.allocator, function, self.currentOffset() - function_offset);
    }

    pub fn writeFunction(self: *@This(), function: sema.InstantiatedFunction) !void {
        try self.writeSingleFunction(function);
        while(self.enqueued_functions.keys().len > 0) {
            try self.writeSingleFunction(self.enqueued_functions.keys()[0]);
        }
    }
};

pub var writer = Writer{};

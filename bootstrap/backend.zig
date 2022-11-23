const std = @import("std");

const ir = @import("ir.zig");
const rega = @import("rega.zig");
const sema = @import("sema.zig");

pub const aarch64 = @import("aarch64.zig");
pub const x86_64 = @import("x86_64.zig");

pub const current_backend = x86_64;

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
                output_bytes[self.output_offset..][0..1].* = std.mem.toBytes(@intCast(i8, @bitCast(i64, rel)));
            },
            .rel32_post_0 => {
                const rel = relocation_target_offset -% (self.output_offset +% 4);
                output_bytes[self.output_offset..][0..4].* = std.mem.toBytes(@intCast(i32, @bitCast(i64, rel)));
            },
            .imm19_div4_shift5 => {
                const rel = @intCast(i19, @bitCast(i64, (relocation_target_offset -% self.output_offset)) >> 2);
                std.mem.bytesAsValue(u32, output_bytes[self.output_offset..][0..4]).* |= @as(u32, @bitCast(u19, rel)) << 5;
            },
            .imm26_div4 => {
                const rel = @intCast(i26, @bitCast(i64, (relocation_target_offset -% self.output_offset)) >> 2);
                std.mem.bytesAsValue(u32, output_bytes[self.output_offset..][0..4]).* |= @as(u32, @bitCast(u26, rel));
            },
        }
    }
};

pub fn Writer(comptime Platform: type) type {
    return struct {
        allocator: std.mem.Allocator = std.heap.page_allocator,
        output_bytes: std.ArrayListUnmanaged(u8) = .{},
        enqueued_blocks: std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, std.ArrayListUnmanaged(Relocation)) = .{},
        placed_blocks: std.AutoHashMapUnmanaged(ir.BlockIndex.Index, usize) = .{},
        enqueued_functions: std.AutoArrayHashMapUnmanaged(sema.ValueIndex.Index, std.ArrayListUnmanaged(Relocation)) = .{},
        placed_functions: std.AutoHashMapUnmanaged(sema.ValueIndex.Index, usize) = .{},

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
                    const disp = @bitCast(isize, offset -% (self.currentOffset() + instr_size));
                    if(disp >= t[1].minDisplacement() and disp <= t[1].maxDisplacement()) return t[1];
                }
            }
            return null;
        }

        fn addRelocation(self: *@This(), edge: ir.BlockEdgeIndex.Index, reloc: Relocation) !void {
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

        fn addFunctionRelocation(self: *@This(), function: sema.ValueIndex.Index, reloc: Relocation) !void {
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
                .output_offset = self.output_bytes.items.len - reloc_type.byteSize(),
                .relocation_type = reloc_type,
            });
        }

        pub fn writeRelocatedFunction(self: *@This(), function: sema.ValueIndex.Index, reloc_type: RelocationType) !void {
            try self.output_bytes.appendNTimes(self.allocator, 0xCC, reloc_type.byteSize());
            return self.addFunctionRelocation(function, .{
                .output_offset = self.output_bytes.items.len - reloc_type.byteSize(),
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
                .output_offset = self.output_bytes.items.len - @sizeOf(T),
                .relocation_type = reloc_type,
            });
        }

        pub fn writeIntWithFunctionRelocation(
            self: *@This(),
            comptime T: type,
            value: T,
            function: sema.ValueIndex.Index,
            reloc_type: RelocationType,
        ) !void {
            try self.writeInt(T, value);
            return self.addFunctionRelocation(function, .{
                .output_offset = self.output_bytes.items.len - @sizeOf(T),
                .relocation_type = reloc_type,
            });
        }

        fn writeBlock(self: *@This(), bidx: ir.BlockIndex.Index, uf: rega.UnionFind) !?ir.BlockIndex.Index {
            var block = ir.blocks.get(bidx);
            var current_instr = block.first_decl;

            try self.placed_blocks.put(self.allocator, bidx, self.output_bytes.items.len);
            while(ir.decls.getOpt(current_instr)) |instr| {
                const next_block: ?ir.BlockIndex.Index = try Platform.writeDecl(self, ir.decls.getIndex(instr), uf);
                if(next_block) |nb| return nb;
                current_instr = instr.next;
            }
            return null;
        }

        fn writeBlocks(self: *@This(), head_block: ir.BlockIndex.Index, uf: rega.UnionFind) !void {
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
                    reloc.resolve(self.output_bytes.items, self.output_bytes.items.len);
                }
                block_relocs.deinit(self.allocator);

                preferred_block = try self.writeBlock(current_block, uf);
            }
        }

        fn writeSingleFunction(self: *@This(), function: sema.ValueIndex.Index) !void {
            const head_block = try ir.ssaFunction(&sema.values.get(function).function);
            try ir.optimizeFunction(head_block);

            var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);

            const blocks_to_dump = try ir.allBlocksReachableFrom(arena.allocator(), head_block);

            for(blocks_to_dump.items) |bb| {
                try ir.dumpBlock(bb, null);
            }

            const uf = try rega.doRegAlloc(
                arena.allocator(),
                &blocks_to_dump,
                current_backend.registers.return_reg,
                &current_backend.registers.param_regs,
                &current_backend.registers.gprs,
                &current_backend.registers.caller_saved,
            );

            for(blocks_to_dump.items) |bb| {
                try ir.dumpBlock(bb, uf);
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
            try self.writeBlocks(head_block, uf);
        }

        pub fn writeFunction(self: *@This(), function: sema.ValueIndex.Index) !void {
            try self.writeSingleFunction(function);
            while(self.enqueued_functions.keys().len > 0) {
                try self.writeSingleFunction(self.enqueued_functions.keys()[0]);
            }
            std.debug.print("Output: {}\n", .{std.fmt.fmtSliceHexUpper(self.output_bytes.items)});
        }
    };
}

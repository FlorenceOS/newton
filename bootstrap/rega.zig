const std = @import("std");

const backends = @import("backends/backends.zig");
const ir = @import("ir.zig");

const DeclReg = enum(u32) {
    _,

    const reg_shift = 32 - @bitSizeOf(ir.RegIndex);

    pub fn encode(d: ir.DeclIndex.Index, r: ir.RegIndex) @This() {
        return @intToEnum(@This(), (@as(u32, r) << reg_shift) | @enumToInt(d));
    }

    pub fn decl(self: @This()) ir.DeclIndex.Index {
        return @intToEnum(ir.DeclIndex.Index, @enumToInt(self) & (1 << reg_shift) - 1);
    }

    pub fn reg(self: @This()) ir.RegIndex {
        return @truncate(ir.RegIndex, @enumToInt(self) >> reg_shift);
    }

    pub fn alloced_reg(self: @This()) ?u8 {
        return ir.decls.get(self.decl()).reg_alloc_value[self.reg()];
    }

    pub fn dump(self: @This()) void {
        if(ir.decls.get(self.decl()).instr.numValues() < 2) {
            std.debug.print(" ${d}", .{@enumToInt(self.decl())});
        } else {
            std.debug.print(" (${d}, #{r})", .{@enumToInt(self.decl()), self.reg()});
        }
    }
};

const RegSet = std.AutoArrayHashMapUnmanaged(DeclReg, void);

fn re_uf(value: DeclReg, uf: *const UnionFind) DeclReg {
    return DeclReg.encode(uf.find(value.decl()), value.reg());
}

fn copyInto(
    allocator: std.mem.Allocator,
    lhs: *RegSet,
    uf: *const UnionFind,
    set: *const RegSet,
) !void {
    var it = set.iterator();
    while(it.next()) |kv| {
        try lhs.put(allocator, re_uf(kv.key_ptr.*, uf), {});
    }
}

const Conflicts = std.AutoArrayHashMapUnmanaged(DeclReg, RegSet);
const Alives = std.AutoArrayHashMapUnmanaged(ir.DeclIndex.Index, RegSet);

fn tryAllocReg(
    decl_idx: ir.DeclIndex.Index,
    reg: u8,
    conflicts: *const RegSet,
) bool {
    const decl = ir.decls.get(decl_idx);
    if(decl.reg_alloc_value[0] != null) return false;

    var it = conflicts.iterator();
    while(it.next()) |conflict| {
        if(conflict.key_ptr.*.alloced_reg() == reg) {
            return false;
        }
    }
    decl.reg_alloc_value[0] = reg;
    return true;
}

fn allocAnyReg(
    decl_idx: ir.DeclIndex.Index,
    gprs: []const u8,
    conflicts: *const RegSet,
) !void {
    const decl = ir.decls.get(decl_idx);
    if(decl.reg_alloc_value[0] != null) return;

    for(gprs) |reg| {
        if(tryAllocReg(decl_idx, reg, conflicts)) return;
    }
    return error.OutOfRegisters;
}

pub const UnionFind = struct {
    e: std.AutoArrayHashMapUnmanaged(i32, i32) = .{},

    fn findI(self: @This(), x: i32) i32 {
        const ep = self.e.getPtr(x) orelse return x;
        if(ep.* < 0) {
            return x;
        } else {
            const root = self.findI(ep.*);
            ep.* = root;
            return root;
        }
    }

    pub fn find(self: @This(), decl: ir.DeclIndex.Index) ir.DeclIndex.Index {
        return @intToEnum(ir.DeclIndex.Index, @intCast(u32, self.findI(@intCast(i32, @enumToInt(decl)))));
    }

    pub fn findDecl(self: @This(), decl: ir.DeclIndex.Index) *ir.Decl {
        return ir.decls.get(self.find(decl));
    }

    pub fn findDeclByPtr(self: @This(), decl_ptr: *ir.Decl) *ir.Decl {
        return self.findDecl(ir.decls.getIndex(decl_ptr));
    }

    pub fn findReg(self: @This(), decl: ir.DeclIndex.Index) ?u8 {
        const d = self.findDecl(decl);
        return d.reg_alloc_value[0];
    }

    pub fn findRegByPtr(self: @This(), decl_ptr: *ir.Decl) ?u8 {
        return self.findReg(ir.decls.getIndex(decl_ptr));
    }

    fn join(self: @This(), a_c: ir.DeclIndex.Index, b_c: ir.DeclIndex.Index) bool {
        var a = self.findI(@intCast(i32, @enumToInt(a_c)));
        var b = self.findI(@intCast(i32, @enumToInt(b_c)));
        if(a == b) return false;
        if(self.e.get(a).? > self.e.get(b).?) std.mem.swap(i32, &a, &b);
        const ebp = self.e.getPtr(b).?;
        self.e.getPtr(a).?.* += ebp.*;
        ebp.* = a;
        return true;
    }
};

fn isDeclInReg(decl_idx: ir.DeclIndex.Index) bool {
    const decl = ir.decls.get(decl_idx);
    return decl.instr.numValues() >= 1 and !decl.instr.isFlagsValue();
}

pub fn allocateRegsForInstr(
    decl_idx: ir.DeclIndex.Index,
    max_memory_operands: usize,
    return_regs: []const u8,
    param_regs: []const u8,
    clobbers: []const u8,
    illegal_input_regs: []const u8,
    allocate_gprs: bool,
    param_replacement: *ParamReplacement,
) !void {
    const decl = ir.decls.get(decl_idx);
    if(ir.DeclIndex.unwrap(decl.next)) |next_instr| {
        if(decl.instr.numValues() == 1) {
            if(return_regs.len > 0 and return_regs[0] != backends.any_register) {
                decl.reg_alloc_value[0] = return_regs[0];
                const copy = try ir.insertBefore(next_instr, .{.copy = decl_idx});
                try param_replacement.put(.{decl_idx, 0}, copy);
            }
        } else {
            for(return_regs[0..decl.instr.numValues()], 0..) |reg, i| {
                if(reg != backends.any_register) {
                    const ri = @intCast(ir.RegIndex, i);
                    decl.reg_alloc_value[i] = reg;
                    const pick = try ir.insertBefore(next_instr, .{.pick = .{
                        .src = decl_idx,
                        .idx = ri,
                    }});
                    try param_replacement.put(.{decl_idx, ri}, pick);
                }
            }
        }
    }
    var memory_operands: usize = 0;
    var register_operands: usize = 0;
    var iter = decl.instr.operands();
    while(iter.next()) |op| {
        if(ir.decls.get(op.*).instr.memoryReference()) |mr| {
            if(memory_operands == max_memory_operands) {
                op.* = try ir.insertBefore(decl_idx, mr.load());
            } else {
                memory_operands += 1;
            }
        }
        if(ir.decls.get(op.*).instr.memoryReference() == null) {
            if(register_operands == param_regs.len) {
                if(allocate_gprs) break;
                @panic("Ran out of param regs");
            }
            if(param_regs[register_operands] == backends.any_register) {
                register_operands += 1;
                continue;
            }
            op.* = try ir.insertBefore(decl_idx, .{.copy = op.*});
            ir.decls.get(op.*).reg_alloc_value[0] = param_regs[register_operands];
            register_operands += 1;
        }
    }
    if(ir.DeclIndex.unwrap(decl.next)) |next_instr| {
        for(clobbers) |clob_reg| {
            const clob1 = try ir.insertBefore(next_instr, .{ .clobber = decl_idx });
            ir.decls.get(clob1).reg_alloc_value[0] = clob_reg;
            const clob2 = try ir.insertBefore(next_instr, .{ .clobber = clob1 });
            ir.decls.get(clob2).reg_alloc_value[0] = clob_reg;
        }
    }
    for(illegal_input_regs) |clob_reg| {
        const clob1 = try ir.insertBefore(decl_idx, .{ .clobber = ir.DeclIndex.unwrap(decl.prev).? });
        ir.decls.get(clob1).reg_alloc_value[0] = clob_reg;
        const clob2 = try ir.insertBefore(decl_idx, .{ .clobber = clob1 });
        ir.decls.get(clob2).reg_alloc_value[0] = clob_reg;
    }
}

pub const ParamReplacement = std.AutoArrayHashMap(std.meta.Tuple(&.{ir.DeclIndex.Index, ir.RegIndex}), ir.DeclIndex.Index);

pub fn doRegAlloc(
    allocator: std.mem.Allocator,
    block_list: *const std.ArrayListUnmanaged(ir.BlockIndex.Index),
) !UnionFind {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var param_replacement = ParamReplacement.init(arena.allocator());
    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            const decl_idx = ir.decls.getIndex(instr);
            switch(instr.instr) {
                .phi => {
                    var pop = instr.instr.phi;
                    while(ir.phi_operands.getOpt(pop)) |op| : (pop = op.next) {
                        const edge = ir.edges.get(op.edge);
                        const source_instr = ir.blocks.get(edge.source_block).last_decl;
                        const new_op = try ir.insertBefore(ir.DeclIndex.unwrap(source_instr).?, .{
                            .copy = op.decl,
                        });
                        op.decl = new_op;
                    }
                },
                .param_ref => |pr| try allocateRegsForInstr(
                    decl_idx,
                    0,
                    &.{backends.current_default_abi.param_regs[pr.param_idx]},
                    &.{},
                    &.{},
                    &.{},
                    false,
                    &param_replacement,
                ),
                .function_call => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    backends.current_default_abi.return_regs,
                    backends.current_default_abi.param_regs,
                    backends.current_default_abi.caller_saved_regs,
                    &.{},
                    false,
                    &param_replacement,
                ),
                .tail_call => try allocateRegsForInstr(decl_idx, 0, &.{}, backends.current_default_abi.param_regs, &.{}, &.{}, false, &param_replacement),
                .syscall => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    &.{backends.current_os.syscall_return_reg},
                    backends.current_os.syscall_param_regs,
                    backends.current_os.syscall_clobbers,
                    &.{},
                    false,
                    &param_replacement,
                ),
                .leave_function => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    &.{},
                    backends.current_default_abi.return_regs,
                    &.{},
                    &.{},
                    false,
                    &param_replacement,
                ),
                else => try backends.current_backend.reg_alloc(decl_idx, &param_replacement),
            }
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            switch(instr.instr) {
                .clobber => continue,
                .pick => |*p| {
                    const replacement = param_replacement.get(.{p.src, p.idx}) orelse continue;
                    instr.instr = .{.copy = replacement};
                },
                else => {
                    var it = instr.instr.operands();
                    while(it.next()) |op| {
                        const replacement = param_replacement.get(.{op.*, 0}) orelse continue;
                        if(replacement != ir.decls.getIndex(instr)) {
                            op.* = replacement;
                        }
                    }
                },
            }
        }
    }

    var uf = UnionFind{};
    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            const i = @intCast(i32, @enumToInt(ir.decls.getIndex(instr)));
            try uf.e.put(allocator, i, -1);
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            if(instr.instr != .phi) continue;
            const i = ir.decls.getIndex(instr);
            var ops_it = instr.instr.operands();
            while(ops_it.next()) |op| {
                // Join phi nodes into its params
                _ = uf.join(op.*, i);
            }
        }
    }

    {
        var fuck = uf.e.iterator();
        while(fuck.next()) |fit| {
            const iidx = @intToEnum(ir.DeclIndex.Index, @intCast(u32, fit.key_ptr.*));
            const replacement = uf.find(iidx);
            std.debug.print("Union: ${d} => ${d}\n", .{@enumToInt(iidx), @enumToInt(replacement)});
            const decl = ir.decls.get(iidx);
            if(decl.instr == .phi) {
                std.debug.assert(iidx != replacement);
                ir.removeDecl(iidx);
            } else {
                var ops_it = decl.instr.operands();
                while(ops_it.next()) |op| {
                    op.* = uf.find(op.*); // Replace all operands that were phi nodes before
                }
            }
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            if(instr.instr != .reference_wrap) continue;
            const i = ir.decls.getIndex(instr);
            var ops_it = instr.instr.operands();
            while(ops_it.next()) |op| {
                // Join deref nodes into its params
                _ = uf.join(op.*, i);
            }
        }
    }

    const BlockData = struct {
        defs: RegSet,
        uses: RegSet,
        ins: RegSet,
        outs: RegSet,
    };
    var blocks = std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, BlockData){};
    var block_work_list = std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, void){};
    var reg_work_list = RegSet{};

    // First it's time to do lifetime analysis.
    for(block_list.items) |blk_idx| {
        var defs = RegSet{};
        var uses = RegSet{};

        var curr_instr = ir.blocks.get(blk_idx).first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            const iidx = ir.decls.getIndex(instr);

            // Anything used before it's defined is a use
            switch(instr.instr) {
                .pick => |p| {
                    const opr = DeclReg.encode(p.src, p.idx);
                    if(!defs.contains(opr)) {
                        try uses.put(arena.allocator(), opr, {});
                    }
                },
                else => {
                    var ops_it = instr.instr.operands();
                    while(ops_it.next()) |op| {
                        const opr = DeclReg.encode(uf.find(op.*), 0);
                        if(!defs.contains(opr)) {
                            try uses.put(arena.allocator(), opr, {});
                        }
                    }
                },
            }

            // Find everything that's defined
            for(0..instr.instr.numValues()) |v| {
                const reg = DeclReg.encode(uf.find(iidx), @truncate(ir.RegIndex, v));
                try defs.put(arena.allocator(), reg, {});
                if(instr.instr.isFlagsValue()) break;
                if(instr.reg_alloc_value[v] == null) {
                    try reg_work_list.put(arena.allocator(), reg, {});
                }
            }
        }

        try block_work_list.put(arena.allocator(), blk_idx, {});
        try blocks.put(arena.allocator(), blk_idx, .{
            .defs = defs,
            .uses = uses,
            .ins = .{},
            .outs = .{},
        });
    }

    // Block level ins/outs
    {
        var new_in = RegSet{};
        while(block_work_list.popOrNull()) |work| {
            new_in.clearRetainingCapacity();
            const blk_idx = work.key;
            const bd = blocks.getPtr(blk_idx).?;

            try copyInto(arena.allocator(), &new_in, &uf, &bd.outs);

            var it = bd.defs.iterator();
            while(it.next()) |value| {
                _ = new_in.swapRemove(re_uf(value.key_ptr.*, &uf));
            }

            try copyInto(arena.allocator(), &new_in, &uf, &bd.uses);

            if(new_in.count() > bd.ins.count()) {
                try copyInto(arena.allocator(), &bd.ins, &uf, &new_in);
                var pred_edge = ir.blocks.get(blk_idx).first_predecessor;
                while(ir.edges.getOpt(pred_edge)) |pe| : (pred_edge = pe.next) {
                    const pred = pe.source_block;
                    try copyInto(arena.allocator(), &blocks.getPtr(pred).?.outs, &uf, &new_in);
                    try block_work_list.put(arena.allocator(), pred, {});
                }
            }
        }
    }

    // Decl level ins/outs
    const DeclData = struct {
        ins: RegSet,
        outs: RegSet,
        conflicts: [ir.InstrMaxRegs]RegSet,
    };
    var decls = std.AutoArrayHashMapUnmanaged(ir.DeclIndex.Index, DeclData){};
    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.last_decl;
        var alive = try blocks.get(blk_idx).?.outs.clone(arena.allocator());
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.prev) {
            const iidx = ir.decls.getIndex(instr);
            
            const outs = try alive.clone(arena.allocator());

            for(0..instr.instr.numValues()) |v| {
                if(instr.instr.isFlagsValue()) break;
                const reg = DeclReg.encode(uf.find(iidx), @truncate(ir.RegIndex, v));
                if(instr.reg_alloc_value[v] == null) {
                    _ = alive.swapRemove(reg);
                }
            }

            switch(instr.instr) {
                .pick => |p| {
                    try alive.put(arena.allocator(), DeclReg.encode(p.src, p.idx), {});
                },
                else => {
                    var ops_it = instr.instr.operands();
                    while(ops_it.next()) |op| {
                        const opr = DeclReg.encode(uf.find(op.*), 0);
                        try alive.put(arena.allocator(), opr, {});
                    }
                },
            }

            try decls.put(arena.allocator(), iidx, .{
                .ins = try alive.clone(arena.allocator()),
                .outs = outs,
                .conflicts = [1]RegSet{.{}} ** ir.InstrMaxRegs,
            });
        }
    }

    {
        var fuck = decls.iterator();
        while(fuck.next()) |point| {
            {
                var outer_it = point.value_ptr.ins.iterator();
                while(outer_it.next()) |outer| {
                    var inner_it = point.value_ptr.ins.iterator();
                    while(inner_it.next()) |inner| {
                        const oruf = re_uf(outer.key_ptr.*, &uf);
                        if(oruf == re_uf(inner.key_ptr.*, &uf)) continue;
                        const outer_decl = ir.decls.get(outer.key_ptr.*.decl());
                        const inner_decl = ir.decls.get(inner.key_ptr.*.decl());
                        if(outer_decl.instr == .copy and outer_decl.instr.copy == inner.key_ptr.*.decl()) continue;
                        if(inner_decl.instr == .copy and inner_decl.instr.copy == outer.key_ptr.*.decl()) continue;

                        try decls.getPtr(oruf.decl()).?.conflicts[oruf.reg()].put(arena.allocator(), re_uf(inner.key_ptr.*, &uf), {});
                    }
                }
            }

            {
                var outer_it = point.value_ptr.outs.iterator();
                while(outer_it.next()) |outer| {
                    var inner_it = point.value_ptr.outs.iterator();
                    while(inner_it.next()) |inner| {
                        const oruf = re_uf(outer.key_ptr.*, &uf);
                        if(oruf == re_uf(inner.key_ptr.*, &uf)) continue;
                        const outer_decl = ir.decls.get(outer.key_ptr.*.decl());
                        const inner_decl = ir.decls.get(inner.key_ptr.*.decl());
                        if(outer_decl.instr == .copy and outer_decl.instr.copy == inner.key_ptr.*.decl()) continue;
                        if(inner_decl.instr == .copy and inner_decl.instr.copy == outer.key_ptr.*.decl()) continue;

                        try decls.getPtr(oruf.decl()).?.conflicts[oruf.reg()].put(arena.allocator(), re_uf(inner.key_ptr.*, &uf), {});
                    }
                }
            }
        }
    }


    {
        var fuck = decls.iterator();
        while(fuck.next()) |di| {
            std.debug.print("${d}\tins:", .{@enumToInt(di.key_ptr.*)});
            var in_it = di.value_ptr.ins.iterator();
            while(in_it.next()) |in_value| {
                in_value.key_ptr.dump();
            }
            
            std.debug.print("\n\touts:", .{});
            var out_it = di.value_ptr.outs.iterator();
            while(out_it.next()) |out_value| {
                out_value.key_ptr.dump();
            }
            for(di.value_ptr.conflicts[0..ir.decls.get(di.key_ptr.*).instr.numValues()], 0..) |set, reg| {
                std.debug.print("\n\tvalue #{d} conflicts:", .{reg});
                var cit_it = set.iterator();
                while(cit_it.next()) |c_value| {
                    c_value.key_ptr.dump();
                }    
            }
            std.debug.print("\n", .{});
        }
    }

    errdefer |err| {
        if(err == error.OutOfRegisters) {
            for(block_list.items) |blk_idx| {
                ir.dumpBlock(blk_idx, uf) catch { };
            }
        }
    }

    var reg_retries = RegSet{};
    while(reg_work_list.count() > 0 or reg_retries.count() > 0) {
        // See if we can reuse any registers
        while(reg_work_list.popOrNull()) |rw| {
            var output = rw.key;
            std.debug.assert(output.reg() == 0);
            const instr = ir.decls.get(output.decl());
            std.debug.assert(instr.instr.numValues() == 1);
            std.debug.assert(instr.reg_alloc_value[0] == null);
            const conflicts = &decls.getPtr(output.decl()).?.conflicts[output.reg()];
            if(switch(instr.instr) {
                .pick => |p| blk: {
                    break :blk tryAllocReg(output.decl(), instr.reg_alloc_value[p.idx] orelse break :blk false, conflicts);
                },
                else => blk: {
                    var it = instr.instr.operands();
                    while(it.next()) |op| {
                        const opr = DeclReg.encode(uf.find(op.*), 0);
                        if(tryAllocReg(output.decl(), opr.alloced_reg() orelse continue, conflicts)) {
                            break :blk true;
                        }
                    }
                    break :blk false;
                },
            }) {
                // Retry all registers with reuse again
                try copyInto(arena.allocator(), &reg_work_list, &uf, &reg_retries);
                reg_retries.clearRetainingCapacity();
            } else {
                // This one failed.
                try reg_retries.put(arena.allocator(), rw.key, {});
            }
        }

        // Allocate one register arbitrarily when we can't reuse registers
        const rr = (reg_retries.popOrNull() orelse break).key;
        std.debug.assert(rr.reg() == 0);
        try allocAnyReg(rr.decl(), backends.current_backend.gprs, &decls.getPtr(rr.decl()).?.conflicts[rr.reg()]);

        // Retry all registers with reuse again
        try copyInto(arena.allocator(), &reg_work_list, &uf, &reg_retries);
        reg_retries.clearRetainingCapacity();
    }

    return uf;
}

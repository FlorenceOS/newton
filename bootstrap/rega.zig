const std = @import("std");

const backends = @import("backends/backends.zig");
const ir = @import("ir.zig");

const DeclSet = std.AutoArrayHashMapUnmanaged(ir.DeclIndex.Index, void);

fn copyInto(
    allocator: std.mem.Allocator,
    lhs: *DeclSet,
    uf: *const UnionFind,
    set: *const DeclSet,
) !void {
    var it = set.iterator();
    while(it.next()) |kv| {
        try lhs.put(allocator, uf.find(kv.key_ptr.*), {});
    }
}

fn setEq(
    lhs: *const DeclSet,
    rhs_opt: ?*const DeclSet,
) bool {
    if(rhs_opt) |rhs| {
        if(rhs.keys().len != lhs.keys().len) return false;
        var it = lhs.iterator();
        while(it.next()) |kv| {
            if(!rhs.contains(kv.key_ptr.*)) return false;
        }
        return true;
    } else {
        return lhs.keys().len == 0;
    }
}

const DeclSetMap = std.AutoArrayHashMapUnmanaged(ir.DeclIndex.Index, DeclSet);

fn tryAllocReg(
    decl_idx: ir.DeclIndex.Index,
    reg: u8,
    conflicts: *const DeclSetMap,
) bool {
    const decl = ir.decls.get(decl_idx);
    if(decl.reg_alloc_value != null) return false;

    var it = conflicts.getPtr(decl_idx).?.iterator();
    while(it.next()) |conflict| {
        const cdecl = ir.decls.get(conflict.key_ptr.*);
        if(cdecl.reg_alloc_value == reg) return false;
    }
    decl.reg_alloc_value = reg;
    return true;
}

fn allocAnyReg(
    decl_idx: ir.DeclIndex.Index,
    gprs: []const u8,
    conflicts: *const DeclSetMap,
) void {
    const decl = ir.decls.get(decl_idx);
    if(decl.reg_alloc_value != null) return;

    for(gprs) |reg| {
        if(tryAllocReg(decl_idx, reg, conflicts)) return;
    }
    @panic("Couldn't find a free reg!");
}

pub const UnionFind = struct {
    e: std.AutoArrayHashMapUnmanaged(i32, i32) = .{},

    fn findI(self: @This(), x: i32) i32 {
        const ep = self.e.getPtr(x).?;
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
        return self.findDecl(decl).reg_alloc_value;
    }

    pub fn findRegByPtr(self: @This(), decl_ptr: *ir.Decl) ?u8 {
        return self.findDeclByPtr(decl_ptr).reg_alloc_value;
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
    return decl.instr.isValue() and !decl.instr.isFlagsValue();
}

pub fn allocateRegsForInstr(
    decl_idx: ir.DeclIndex.Index,
    max_memory_operands: usize,
    return_reg: ?u8,
    param_regs: []const u8,
    clobbers: []const u8,
    allocate_gprs: bool,
    param_replacement: *ParamReplacement,
) !void {
    const decl = ir.decls.get(decl_idx);
    const next = ir.DeclIndex.unwrap(decl.next) orelse return;
    if(return_reg) |reg| {
        decl.reg_alloc_value = reg;
        const ret_copy = try ir.insertBefore(next, .{
            .copy = decl_idx,
        });
        try param_replacement.put(decl_idx, ret_copy);
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
        } else {
            op.* = try ir.insertBefore(decl_idx, .{.copy = op.*});
        }
        if(ir.decls.get(op.*).instr.memoryReference() == null) {
            if(register_operands == param_regs.len) {
                if(allocate_gprs) break;
                @panic("Ran out of param regs");
            }
            ir.decls.get(op.*).reg_alloc_value = param_regs[register_operands];
            register_operands += 1;
        }
    }
    for(clobbers) |clob_reg| {
        if(return_reg == clob_reg) continue;
        const clob1 = try ir.insertBefore(next, .{
            .clobber = decl_idx,
        });
        ir.decls.get(clob1).reg_alloc_value = clob_reg;
        const clob2 = try ir.insertBefore(next, .{
            .clobber = clob1,
        });
        ir.decls.get(clob2).reg_alloc_value = clob_reg;
    }
}

pub const ParamReplacement = std.AutoArrayHashMap(ir.DeclIndex.Index, ir.DeclIndex.Index);

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
                    backends.current_default_abi.param_regs[pr.param_idx],
                    &.{},
                    &.{},
                    false,
                    &param_replacement,
                ),
                .function_call => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    backends.current_default_abi.return_reg,
                    backends.current_default_abi.param_regs,
                    backends.current_default_abi.caller_saved_regs,
                    false,
                    &param_replacement,
                ),
                .syscall => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    backends.current_os.syscall_return_reg,
                    backends.current_os.syscall_param_regs,
                    backends.current_os.syscall_clobbers,
                    false,
                    &param_replacement,
                ),
                .leave_function => try allocateRegsForInstr(
                    decl_idx,
                    0,
                    null,
                    &.{backends.current_default_abi.return_reg},
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
            var it = instr.instr.operands();
            while(it.next()) |op| {
                const replacement = param_replacement.get(op.*) orelse continue;
                if(replacement != ir.decls.getIndex(instr))
                    op.* = replacement;
            }
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            const max_memory_operands = backends.current_backend.optimizations.max_memory_operands_fn(instr);
            var memory_operands: usize = 0;
            var it = instr.instr.operands();
            while(it.next()) |op| {
                if(ir.decls.get(op.*).instr.memoryReference()) |mr| {
                    memory_operands += 1;
                    if(memory_operands > max_memory_operands) {
                        op.* = try ir.insertBefore(ir.decls.getIndex(instr), mr.load());
                    }
                }
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

    var ins = DeclSetMap{};
    var out = DeclSetMap{};

    var conflicts = DeclSetMap{};

    var any_changed = true;
    while(any_changed) {
        any_changed = false;

        for(block_list.items) |blk_idx| {
            const blk = ir.blocks.get(blk_idx);

            var curr_instr = blk.first_decl;
            while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
                const iidx = ir.decls.getIndex(instr);
                try conflicts.put(arena.allocator(), uf.find(iidx), .{});
                const curr_in = ins.getPtr(iidx);
                const curr_out = out.getPtr(iidx);

                var new_in = DeclSet{};
                blk: {
                    try copyInto(arena.allocator(), &new_in, &uf, curr_out orelse break :blk);
                }
                _ = new_in.swapRemove(uf.find(iidx));
                var ops_it = instr.instr.operands();
                while(ops_it.next()) |op| {
                    try new_in.put(arena.allocator(), uf.find(op.*), {});
                }

                var new_out = DeclSet{};
                if(ir.decls.getOpt(instr.next)) |succi| blk: {
                    try copyInto(arena.allocator(), &new_out, &uf, ins.getPtr(ir.decls.getIndex(succi)) orelse break :blk);
                } else {
                    const out_edges = instr.instr.outEdges();
                    for(out_edges.slice()) |edge_idx| {
                        const edge = ir.edges.get(edge_idx.*);
                        const target_block = ir.blocks.get(edge.target_block);
                        if(ir.decls.getOpt(target_block.first_decl)) |succi| {
                            try copyInto(arena.allocator(), &new_out, &uf, ins.getPtr(ir.decls.getIndex(succi)) orelse continue);
                        }
                    }
                }

                if(!any_changed and (!setEq(&new_in, curr_in) or !setEq(&new_out, curr_out))) {
                    any_changed = true;
                }

                if(curr_in) |ci| {
                    //ci.deinit(arena.allocator());
                    ci.* = new_in;
                } else {
                    try ins.put(arena.allocator(), iidx, new_in);
                }

                if(curr_out) |co| {
                    //co.deinit(arena.allocator());
                    co.* = new_out;
                } else {
                    try out.put(arena.allocator(), iidx, new_out);
                }
            }
        }
    }

    {
        var fuck = ins.iterator();
        while(fuck.next()) |decl_set| {
            var outer_it = decl_set.value_ptr.iterator();
            while(outer_it.next()) |outer| {
                var inner_it = decl_set.value_ptr.iterator();
                while(inner_it.next()) |inner| {
                    if(uf.find(outer.key_ptr.*) == uf.find(inner.key_ptr.*)) continue;
                    try conflicts.getPtr(uf.find(outer.key_ptr.*)).?.put(arena.allocator(), uf.find(inner.key_ptr.*), {});
                }
            }
        }
    }

    {
        var fuck = out.iterator();
        while(fuck.next()) |decl_set| {
            var outer_it = decl_set.value_ptr.iterator();
            while(outer_it.next()) |outer| {
                var inner_it = decl_set.value_ptr.iterator();
                while(inner_it.next()) |inner| {
                    if(uf.find(outer.key_ptr.*) == uf.find(inner.key_ptr.*)) continue;
                    try conflicts.getPtr(uf.find(outer.key_ptr.*)).?.put(arena.allocator(), uf.find(inner.key_ptr.*), {});
                }
            }
        }
    }

    {
        var i: usize = 0;
        while(i < conflicts.keys().len) {
            const k = conflicts.keys()[i];
            if(isDeclInReg(k)) {
                const decl_set = &conflicts.values()[i];
                var j: usize = 0;
                while(j < decl_set.keys().len) {
                    const conflict_decl = ir.decls.get(decl_set.keys()[j]);
                    if(isDeclInReg(ir.decls.getIndex(conflict_decl))) {
                        j += 1;
                    } else {
                        decl_set.swapRemoveAt(j);
                    }
                }
                i += 1;
            } else {
                conflicts.swapRemoveAt(i);
            }
        }
    }

    while(blk: {
        var fuck = conflicts.iterator();
        while(fuck.next()) |decl_node| {
            const iidx = decl_node.key_ptr.*;
            const decl = ir.decls.get(iidx);
            if(decl.reg_alloc_value == null) {
                break :blk true;
            }
        }
        break :blk false;
    }) {
        var allocated_same_anywhere = true;
        while(allocated_same_anywhere) {
            allocated_same_anywhere = false;

            for(block_list.items) |blk_idx| {
                const blk = ir.blocks.get(blk_idx);
                var curr_instr = blk.first_decl;
                while(ir.decls.getOpt(curr_instr)) |decl| : (curr_instr = decl.next) {
                    if(!isDeclInReg(ir.decls.getIndex(decl))) continue;
                    const adecl = uf.findDecl(ir.decls.getIndex(decl));
                    var ops_it = decl.instr.operands();
                    if(adecl.reg_alloc_value) |reg| {
                        while(ops_it.next()) |op| {
                            if(!isDeclInReg(op.*)) continue;
                            if(tryAllocReg(uf.find(op.*), reg, &conflicts)) {
                                allocated_same_anywhere = true;
                            }
                        }
                    } else {
                        while(ops_it.next()) |op| {
                            if(!isDeclInReg(op.*)) continue;
                            const oadecl = uf.findDecl(op.*);
                            if(oadecl.reg_alloc_value) |reg| {
                                if(tryAllocReg(uf.find(ir.decls.getIndex(decl)), reg, &conflicts)) {
                                    allocated_same_anywhere = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }

        // Okay, just allocate something...
        var fuck = conflicts.iterator();
        while(fuck.next()) |decl_node| {
            const iidx = decl_node.key_ptr.*;
            const decl = ir.decls.get(iidx);
            if(decl.reg_alloc_value == null) {
                allocAnyReg(iidx, backends.current_backend.gprs, &conflicts);
                break;
            }
        }
    }

    return uf;
}

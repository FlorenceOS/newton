const std = @import("std");

const ir = @import("ir.zig");

const SuccessorBlocks = std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, std.ArrayListUnmanaged(ir.BlockIndex.Index));

fn findPredBlocks(
    allocator: std.mem.Allocator,
    arena: std.mem.Allocator,
    succ_block: ir.BlockIndex.Index,
    succ_dict: *SuccessorBlocks,
    num_blks: usize,
) !void {
    var visited = std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, void){};
    defer visited.deinit(allocator);
    try visited.ensureTotalCapacity(allocator, num_blks);
    var queue = try std.ArrayListUnmanaged(ir.BlockIndex.Index).initCapacity(allocator, num_blks);
    defer queue.deinit(allocator);
    queue.appendAssumeCapacity(succ_block);

    while(queue.items.len > 0) {
        const blk_idx = queue.swapRemove(0);
        const blk = ir.blocks.get(blk_idx);

        var curr_pred = blk.first_predecessor;
        while(ir.edges.getOpt(curr_pred)) |edge| : (curr_pred = edge.next) {
            if(!visited.contains(edge.source_block)) {
                visited.putAssumeCapacity(edge.source_block, {});
                queue.appendAssumeCapacity(edge.source_block);
                try succ_dict.getPtr(edge.source_block).?.append(arena, succ_block);
            }
        }
    }
}

fn findSuccessorBlocks(
    allocator: std.mem.Allocator,
    arena: std.mem.Allocator,
    block_list: *const std.ArrayListUnmanaged(ir.BlockIndex.Index),
) !SuccessorBlocks {
    var result = SuccessorBlocks{};
    try result.ensureTotalCapacity(allocator, block_list.items.len);
    for(block_list.items) |blk_idx| {
        result.putAssumeCapacity(blk_idx, .{});
    }
    for(block_list.items) |blk_idx| {
        try findPredBlocks(allocator, arena, blk_idx, &result, block_list.items.len);
    }
    return result;
}

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

pub fn doRegAlloc(
    allocator: std.mem.Allocator,
    block_list: *const std.ArrayListUnmanaged(ir.BlockIndex.Index),
    return_reg: u8,
    param_regs: []const u8,
    gprs: []const u8,
) !UnionFind {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    var succ = try findSuccessorBlocks(allocator, arena.allocator(), block_list);

    var it = succ.iterator();
    while(it.next()) |succ_src| {
        for(succ_src.value_ptr.items) |succ_blk| {
            std.debug.print("{d} is a successor of {d}\n", .{@enumToInt(succ_blk), @enumToInt(succ_src.key_ptr.*)});
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |instr| : (curr_instr = instr.next) {
            if(instr.instr == .phi) {
                var pop = instr.instr.phi;
                while(ir.phi_operands.getOpt(pop)) |op| : (pop = op.next) {
                    const edge = ir.edges.get(op.edge);
                    const source_instr = ir.blocks.get(edge.source_block).last_decl;
                    const new_op = try ir.insertBefore(ir.DeclIndex.unwrap(source_instr).?, .{
                        .copy = op.decl,
                    });
                    op.decl = new_op;
                }
            }
        }
    }

    for(block_list.items) |blk_idx| {
        try ir.dumpBlock(blk_idx, null);
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
        while(fuck.next()) |decl_ins| {
            std.debug.print("${d} has the following ins:", .{@enumToInt(decl_ins.key_ptr.*)});
            var in_it = decl_ins.value_ptr.iterator();
            while(in_it.next()) |in_value| {
                std.debug.print(" ${d}", .{@enumToInt(in_value.key_ptr.*)});
            }
            std.debug.print("\n", .{});
        }
    }

    {
        var fuck = out.iterator();
        while(fuck.next()) |decl_out| {
            std.debug.print("${d} has the following out:", .{@enumToInt(decl_out.key_ptr.*)});
            var out_it = decl_out.value_ptr.iterator();
            while(out_it.next()) |out_value| {
                std.debug.print(" ${d}", .{@enumToInt(out_value.key_ptr.*)});
            }
            std.debug.print("\n", .{});
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
                std.debug.print("${d} has the following conflicts:", .{@enumToInt(k)});
                const decl_set = &conflicts.values()[i];
                var j: usize = 0;
                while(j < decl_set.keys().len) {
                    const conflict_decl = ir.decls.get(decl_set.keys()[j]);
                    if(isDeclInReg(ir.decls.getIndex(conflict_decl))) {
                        std.debug.print(" ${d}", .{@enumToInt(ir.decls.getIndex(conflict_decl))});
                        j += 1;
                    } else {
                        decl_set.swapRemoveAt(j);
                    }
                }
                std.debug.print("\n", .{});
                i += 1;
            } else {
                conflicts.swapRemoveAt(i);
            }
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |decl| : (curr_instr = decl.next) {
            const adecl = uf.findDecl(ir.decls.getIndex(decl));
            switch(decl.instr) {
                .param_ref => |pr| adecl.reg_alloc_value = param_regs[pr],
                else => {},
            }
        }
    }

    for(block_list.items) |blk_idx| {
        const blk = ir.blocks.get(blk_idx);
        var curr_instr = blk.first_decl;
        while(ir.decls.getOpt(curr_instr)) |decl| : (curr_instr = decl.next) {
            switch(decl.instr) {
                .@"return" => |ret| {
                    const adecl = uf.findDecl(ret.value);
                    if(adecl.reg_alloc_value == null and isDeclInReg(ret.value)) {
                        adecl.reg_alloc_value = return_reg;
                    }
                },
                else => {},
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
                allocAnyReg(iidx, gprs, &conflicts);
                break;
            }
        }
    }

    return uf;
}

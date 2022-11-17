const std = @import("std");

const backend = @import("backend.zig");
const indexed_list = @import("indexed_list.zig");
const sema = @import("sema.zig");

pub const DeclIndex = indexed_list.Indices(u32, .{});
pub const BlockIndex = indexed_list.Indices(u32, .{});
pub const BlockEdgeIndex = indexed_list.Indices(u32, .{});
pub const PhiOperandIndex = indexed_list.Indices(u32, .{});

// Based on
// "Simple and Efficient Construction of Static Single Assignment Form"
// https://pp.info.uni-karlsruhe.de/uploads/publikationen/braun13cc.pdf
// by
// Matthias Braun, Sebastian Buchwald, Sebastian Hack, Roland Leißa, Christoph Mallon and Andreas Zwinkau

pub const Bop = struct {
    lhs: DeclIndex.Index,
    rhs: DeclIndex.Index,
};

pub const VariableConstantBop = struct {
    lhs: DeclIndex.Index,
    rhs: u64,
};

const DeclInstr = union(enum) {
    param_ref: u8,
    load_int_constant: u64,
    load_bool_constant: bool,
    @"undefined",

    add: Bop,
    add_mod: Bop,
    sub: Bop,
    sub_mod: Bop,
    multiply: Bop,
    multiply_mod: Bop,
    divide: Bop,
    modulus: Bop,
    shift_left: Bop,
    shift_right: Bop,
    bit_and: Bop,
    bit_or: Bop,
    bit_xor: Bop,
    less: Bop,
    less_equal: Bop,
    equals: Bop,
    not_equal: Bop,

    add_constant: VariableConstantBop,
    add_mod_constant: VariableConstantBop,
    sub_constant: VariableConstantBop,
    sub_mod_constant: VariableConstantBop,
    multiply_constant: VariableConstantBop,
    multiply_mod_constant: VariableConstantBop,
    divide_constant: VariableConstantBop,
    modulus_constant: VariableConstantBop,
    shift_left_constant: VariableConstantBop,
    shift_right_constant: VariableConstantBop,
    bit_and_constant: VariableConstantBop,
    bit_or_constant: VariableConstantBop,
    bit_xor_constant: VariableConstantBop,

    less_constant: VariableConstantBop,
    less_equal_constant: VariableConstantBop,
    greater_constant: VariableConstantBop,
    greater_equal_constant: VariableConstantBop,
    equals_constant: VariableConstantBop,
    not_equal_constant: VariableConstantBop,

    incomplete_phi: DeclIndex.OptIndex, // Holds the next incomplete phi node in the same block
    copy: DeclIndex.Index, // Should be eliminated during optimization
    @"if": struct {
        condition: DeclIndex.Index,
        taken: BlockEdgeIndex.Index,
        not_taken: BlockEdgeIndex.Index,
    },
    @"return": DeclIndex.Index,
    goto: BlockEdgeIndex.Index,
    phi: PhiOperandIndex.Index,

    const OperandIterator = struct {
        value: union(enum) {
            bounded_iterator: std.BoundedArray(*DeclIndex.Index, 2),
            phi_iterator: ?*PhiOperand,
        },

        fn next(self: *@This()) ?*DeclIndex.Index {
            switch(self.value) {
                .bounded_iterator => |*list| return list.popOrNull(),
                .phi_iterator => |*curr_opt| {
                    if(curr_opt.*) |curr| {
                        curr_opt.* = phi_operands.getOpt(curr.next);
                        return &curr.decl;
                    } else {
                        return null;
                    }
                },
            }
        }
    };

    fn operands(self: *@This()) OperandIterator {
        var bounded_result = OperandIterator{.value = .{.bounded_iterator = .{}}};

        switch(self.*) {
            .incomplete_phi => unreachable,

            .phi => |p| return OperandIterator{.value = .{.phi_iterator = phi_operands.get(p)}},

            .add, .add_mod, .sub, .sub_mod,
            .multiply, .multiply_mod, .divide, .modulus,
            .shift_left, .shift_right, .bit_and, .bit_or, .bit_xor,
            .less, .less_equal, .equals, .not_equal,
            => |*bop| {
                bounded_result.value.bounded_iterator.appendAssumeCapacity(&bop.lhs);
                bounded_result.value.bounded_iterator.appendAssumeCapacity(&bop.rhs);
            },

            .add_constant, .add_mod_constant, .sub_constant, .sub_mod_constant,
            .multiply_constant, .multiply_mod_constant, .divide_constant, .modulus_constant,
            .shift_left_constant, .shift_right_constant, .bit_and_constant, .bit_or_constant, .bit_xor_constant,
            .less_constant, .less_equal_constant, .greater_constant, .greater_equal_constant,
            .equals_constant, .not_equal_constant => |*bop| {
                bounded_result.value.bounded_iterator.appendAssumeCapacity(&bop.lhs);
            },

            .copy => |*c| bounded_result.value.bounded_iterator.appendAssumeCapacity(c),
            .@"if" => |*instr| bounded_result.value.bounded_iterator.appendAssumeCapacity(&instr.condition),
            .@"return" => |*value| bounded_result.value.bounded_iterator.appendAssumeCapacity(value),
            .param_ref, .load_int_constant, .load_bool_constant, .@"undefined", .goto,
            => {}, // No operands
        }

        return bounded_result;
    }

    fn isVolatile(self: *@This()) bool {
        switch(self.*) {
            .incomplete_phi => unreachable,
            .@"if", .@"return", .goto => return true,
            else => return false,
        }
    }

    fn isValue(self: *@This()) bool {
        switch(self.*) {
            .incomplete_phi => unreachable,
            .@"if", .@"return", .goto => return false,
            else => return true,
        }
    }

    fn outEdges(self: *@This()) std.BoundedArray(*BlockEdgeIndex.Index, 2) {
        var result = std.BoundedArray(*BlockEdgeIndex.Index, 2){};
        switch(self.*) {
            .incomplete_phi => unreachable,
            .@"if" => |*instr| {
                result.appendAssumeCapacity(&instr.taken);
                result.appendAssumeCapacity(&instr.not_taken);
            },
            .goto => |*out| result.appendAssumeCapacity(out),
            else => {}, // No out edges
        }
        return result;
    }
};

pub const Decl = struct {
    next: DeclIndex.OptIndex = .none,
    prev: DeclIndex.OptIndex = .none,
    block: BlockIndex.Index,

    sema_decl: sema.DeclIndex.OptIndex,
    instr: DeclInstr,
    reg_alloc_value: ?u8 = null,
};

const InstructionToBlockEdge = struct {
    source_block: BlockIndex.Index,
    target_block: BlockIndex.Index,
    next: BlockEdgeIndex.OptIndex,
};

const PhiOperand = struct {
    edge: BlockEdgeIndex.Index,
    decl: DeclIndex.Index,
    next: PhiOperandIndex.OptIndex = .none,
};

pub const BasicBlock = struct {
    is_sealed: bool = false,
    is_filled: bool = false,
    first_incomplete_phi_node: DeclIndex.OptIndex = .none,
    first_predecessor: BlockEdgeIndex.OptIndex = .none,
    first_decl: DeclIndex.OptIndex = .none,
    last_decl: DeclIndex.OptIndex = .none,

    pub fn seal(self: *@This()) !void {
        while(decls.getOpt(self.first_incomplete_phi_node)) |decl| {
            self.first_incomplete_phi_node = decl.instr.incomplete_phi;
            _ = try addPhiOperands(
                sema.DeclIndex.unwrap(decl.sema_decl).?,
                blocks.getIndex(self),
                decls.getIndex(decl),
                false,
            );
        }
        self.is_sealed = true;
    }

    pub fn filled(self: *@This()) !void {
        self.is_filled = true;
    }
};

pub var decls: DeclIndex.List(Decl) = undefined;
pub var blocks: BlockIndex.List(BasicBlock) = undefined;
pub var edges: BlockEdgeIndex.List(InstructionToBlockEdge) = undefined;
pub var phi_operands: PhiOperandIndex.List(PhiOperand) = undefined;

// Name from paper
fn readVariable(block_idx: BlockIndex.Index, decl: sema.DeclIndex.Index) anyerror!DeclIndex.Index {
    const odecl = sema.DeclIndex.toOpt(decl);
    // Look backwards to find value in current basic block
    var pred_idx = blocks.get(block_idx).last_decl;
    while(decls.getOpt(pred_idx)) |pred| {
        if(pred.sema_decl == odecl) return decls.getIndex(pred);
        pred_idx = pred.prev;
    }
    return readVariableRecursive(block_idx, decl);
}

// Name from paper
fn readVariableRecursive(block_idx: BlockIndex.Index, decl: sema.DeclIndex.Index) !DeclIndex.Index {
    const odecl = sema.DeclIndex.toOpt(decl);
    const block = blocks.get(block_idx);
    if(!block.is_sealed) {
        const new_phi = try appendToBlock(block_idx, odecl, .{
            .incomplete_phi = block.first_incomplete_phi_node,
        });
        block.first_incomplete_phi_node = DeclIndex.toOpt(new_phi);
        return new_phi;
    } else {
        const first_predecessor = block.first_predecessor;
        const first_edge = edges.getOpt(first_predecessor).?;

        if(edges.getOpt(first_edge.next)) |_| {
            // Block gets new phi node
            const new_phi = try appendToBlock(block_idx, odecl, .{
                .incomplete_phi = undefined,
            });
            return addPhiOperands(decl, block_idx, new_phi, true);
        } else {
            std.debug.assert(blocks.get(first_edge.source_block).is_filled);
            return readVariable(first_edge.source_block, decl);
        }
    }
}

// Name from paper
fn addPhiOperands(sema_decl: sema.DeclIndex.Index, block_idx: BlockIndex.Index, phi_idx: DeclIndex.Index, delete: bool) !DeclIndex.Index {
    const block = blocks.get(block_idx);
    var current_pred_edge = block.first_predecessor;
    var init_operand = PhiOperandIndex.OptIndex.none;

    while(edges.getOpt(current_pred_edge)) |edge| {
        const eidx = edges.getIndex(edge);

        const new_operand = try phi_operands.insert(.{
            .edge = eidx,
            .decl = try readVariable(edge.source_block, sema_decl),
            .next = init_operand,
        });

        init_operand = PhiOperandIndex.toOpt(new_operand);
        current_pred_edge = edge.next;
    }

    decls.get(phi_idx).instr = .{
        .phi = PhiOperandIndex.unwrap(init_operand).?,
    };

    return tryRemoveTrivialPhi(phi_idx, delete);
}

fn removeDecl(decl_idx: DeclIndex.Index) void {
    const decl = decls.get(decl_idx);
    const block = blocks.get(decl.block);

    if(decls.getOpt(decl.prev)) |prev| {
        prev.next = decl.next;
    } else {
        block.first_decl = decl.next;
    }
    if(decls.getOpt(decl.next)) |next| {
        next.prev = decl.prev;
    } else {
        block.last_decl = decl.prev;
    }
    decls.free(decl_idx);
}

/// Name from paper
fn tryRemoveTrivialPhi(phi_decl: DeclIndex.Index, delete: bool) DeclIndex.Index {
    if(checkTrivialPhi(phi_decl)) |trivial_decl| {
        if(trivial_decl) |trivial_idx| {
            if(delete) {
                removeDecl(phi_decl);
                return trivial_idx;
            } else {
                decls.get(phi_decl).instr = .{.copy = trivial_idx};
            }
        } else {
            // This is zero operand phi node. What does it meme?
            decls.get(phi_decl).instr = .{.@"undefined" = {}};
        }
    }

    return phi_decl;
}

// Name from paper
fn checkTrivialPhi(phi_decl: DeclIndex.Index) ??DeclIndex.Index {
    var current_operand = PhiOperandIndex.toOpt(decls.get(phi_decl).instr.phi);
    var only_decl: ?DeclIndex.Index = null;

    while(phi_operands.getOpt(current_operand)) |op| {
        if(only_decl) |only| {
            if(only != op.decl) return null;
        } else {
            only_decl = op.decl;
        }
        current_operand = op.next;
    }

    return only_decl;
}

// Assumes an arena allocator is passed
const DiscoverContext = struct {
    to_visit: std.ArrayList(BlockIndex.Index),
    visited: std.AutoArrayHashMap(BlockIndex.Index, void),

    fn init(allocator: std.mem.Allocator, first_block: BlockIndex.Index) !@This() {
        var result: @This() = undefined;
        result.to_visit = std.ArrayList(BlockIndex.Index).init(allocator);
        try result.to_visit.append(first_block);
        result.visited = std.AutoArrayHashMap(BlockIndex.Index, void).init(allocator);
        try result.visited.put(first_block, {});
        return result;
    }

    fn nextBlock(self: *@This()) ?*BasicBlock {
        if(self.to_visit.items.len > 0) {
            return blocks.get(self.to_visit.swapRemove(0));
        } else {
            return null;
        }
    }

    fn edge(self: *@This(), eidx: BlockEdgeIndex.Index) !void {
        const target_idx = edges.get(eidx).target_block;
        if(self.visited.get(target_idx) == null) {
            try self.to_visit.append(target_idx);
            try self.visited.put(target_idx, {});
        }
    }

    fn finalize(self: *@This()) []BlockIndex.Index {
        return self.visited.keys();
    }
};

const BlockList = std.ArrayListUnmanaged(BlockIndex.Index);

// Assumes an arena allocator is passed
fn allBlocksReachableFrom(allocator: std.mem.Allocator, head_block: BlockIndex.Index) !BlockList {
    var context = try DiscoverContext.init(allocator, head_block);

    while(context.nextBlock()) |block| {
        var current_decl = block.first_decl;
        while(decls.getOpt(current_decl)) |decl| {
            const decl_block_edges = decl.instr.outEdges();
            for(decl_block_edges.slice()) |edge| {
                try context.edge(edge.*);
            }
            current_decl = decl.next;
        }
    }

    const elements = context.finalize();
    return BlockList{.items = elements, .capacity = elements.len};
}

const function_optimizations = .{
    eliminateCopies,
    eliminateUnreferenced,
    eliminateDeadBlocks,
};

const peephole_optimizations = .{
    eliminateTrivialPhis,
    eliminateConstantIfs,
    eliminateRedundantIfs,
    eliminateIndirectBranches,
    inlineConstants,
    eliminateTrivialArithmetic,
    eliminateConstantExpressions,
};

var optimization_allocator = std.heap.GeneralPurposeAllocator(.{}){.backing_allocator = std.heap.page_allocator};

fn optimizeFunction(head_block: BlockIndex.Index) !void {
    var arena = std.heap.ArenaAllocator.init(optimization_allocator.allocator());
    defer arena.deinit();
    var fn_blocks = try allBlocksReachableFrom(arena.allocator(), head_block);

    while(true) {
        var did_something = false;
        for(fn_blocks.items) |block| {
            var current_decl = blocks.get(block).first_decl;
            while(decls.getOpt(current_decl)) |decl| {
                current_decl = decl.next;
                inline for(peephole_optimizations) |pass| {
                    if(try pass(decls.getIndex(decl))) did_something = true;
                }
            }
        }
        inline for(function_optimizations) |pass| {
            var pass_allocator = std.heap.ArenaAllocator.init(optimization_allocator.allocator());
            defer pass_allocator.deinit();
            if(try pass(pass_allocator.allocator(), &fn_blocks)) did_something = true;
        }
        if(!did_something) return;
    }
}

fn eliminateCopyChain(
    decl_idx: DeclIndex.Index,
    copy_dict: *std.AutoHashMap(DeclIndex.Index, DeclIndex.Index)
) !DeclIndex.Index {
    if(copy_dict.get(decl_idx)) |retval| { // Copy decl has already been removed
        return retval;
    }
    const decl = decls.get(decl_idx);
    if(decl.instr == .copy) {
        const retval = try eliminateCopyChain(decl.instr.copy, copy_dict);
        try copy_dict.put(decl_idx, retval);
        decl.instr = .{.@"undefined" = {}};
        return retval;
    }
    return decl_idx;
}

fn eliminateCopyOperands(
    operand: *DeclIndex.Index,
    copy_dict: *std.AutoHashMap(DeclIndex.Index, DeclIndex.Index)
) !void {
    operand.* = try eliminateCopyChain(operand.*, copy_dict);
}

fn eliminateDeadBlocks(alloc: std.mem.Allocator, fn_blocks: *BlockList) !bool {
    const new_blocks = try allBlocksReachableFrom(alloc, fn_blocks.items[0]);
    if(new_blocks.items.len == fn_blocks.items.len) return false;
    std.mem.copy(BlockIndex.Index, fn_blocks.items, new_blocks.items);
    fn_blocks.shrinkRetainingCapacity(new_blocks.items.len);
    return true;
}

fn eliminateCopies(alloc: std.mem.Allocator, fn_blocks: *BlockList) !bool {
    var copy_dict = std.AutoHashMap(DeclIndex.Index, DeclIndex.Index).init(alloc);
    var did_something = false;

    for(fn_blocks.items) |block| {
        var current_decl = blocks.get(block).first_decl;
        while(decls.getOpt(current_decl)) |decl| {
            current_decl = decl.next;
            var ops = decl.instr.operands();
            while(ops.next()) |op| {
                try eliminateCopyOperands(op, &copy_dict);
            }
            if(decls.getIndex(decl) != try eliminateCopyChain(decls.getIndex(decl), &copy_dict)) {
                did_something = true;
            }
        }
    }

    return did_something;
}

fn eliminateUnreferenced(alloc: std.mem.Allocator, fn_blocks: *BlockList) !bool {
    var unreferenced = std.AutoHashMap(DeclIndex.Index, void).init(alloc);
    var referenced_undiscovered = std.AutoHashMap(DeclIndex.Index, void).init(alloc);

    for(fn_blocks.items) |block| {
        var current_decl = blocks.get(block).first_decl;
        while(decls.getOpt(current_decl)) |decl| {
            const idx = decls.getIndex(decl);
            current_decl = decl.next;
            if(!referenced_undiscovered.remove(idx) and !decl.instr.isVolatile()) {
                try unreferenced.put(idx, {});
            }

            var ops = decl.instr.operands();
            while(ops.next()) |op| {
                if(!unreferenced.remove(op.*)) {
                    try referenced_undiscovered.put(op.*, {});
                }
            }
        }
    }

    var it = unreferenced.keyIterator();
    var did_something = false;
    while(it.next()) |key| {
        removeDecl(key.*);
        did_something = true;
    }
    return did_something;
}

fn eliminateTrivialPhis(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    if(decl.instr == .phi) {
        _ = tryRemoveTrivialPhi(decl_idx, false);
        return decl.instr != .phi;
    }
    return false;
}

fn eliminateConstantIfs(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    if(decl.instr == .@"if") {
        const if_instr = decl.instr.@"if";
        const cond_decl = decls.get(if_instr.condition);

        switch(cond_decl.instr) {
            .load_bool_constant => |value| {
                decl.instr = .{.goto = if(value) if_instr.taken else if_instr.not_taken};
                return true;
            },
            else => {},
        }
    }
    return false;
}

fn eliminateRedundantIfs(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    if(decl.instr == .@"if") {
        const if_instr = decl.instr.@"if";
        const taken_edge = edges.get(if_instr.taken);
        const not_taken_edge = edges.get(if_instr.not_taken);
        if(taken_edge.target_block == not_taken_edge.target_block) {
            decl.instr = .{.goto = if_instr.taken};
            return true;
        }
    }
    return false;
}

fn eliminateIndirectBranches(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    var did_something = false;
    for(decl.instr.outEdges().slice()) |edge| {
        const target_edge = edges.get(edge.*);
        const target_block = blocks.get(target_edge.target_block);
        if(target_block.first_decl == target_block.last_decl) {
            const first_decl = decls.getOpt(target_block.first_decl) orelse continue;
            if(first_decl.instr == .goto) {
                edges.get(first_decl.instr.goto).source_block = decl.block;
                edge.* = first_decl.instr.goto;
                did_something = true;
            }
        }
    }
    return did_something;
}

fn inlineConstants(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    switch(decl.instr) {
        // Commutative ops
        inline
        .add, .add_mod, .multiply, .multiply_mod,
        .bit_and, .bit_or, .bit_xor, .equals, .not_equal
        => |bop, tag| {
            const lhs = decls.get(bop.lhs).instr;
            if(lhs == .load_int_constant) {
                decl.instr = @unionInit(DeclInstr, @tagName(tag) ++ "_constant", .{
                    .lhs = bop.rhs,
                    .rhs = lhs.load_int_constant,
                });
                return true;
            }
            const rhs = decls.get(bop.rhs).instr;
            if(rhs == .load_int_constant) {
                decl.instr = @unionInit(DeclInstr, @tagName(tag) ++ "_constant", .{
                    .lhs = bop.lhs,
                    .rhs = rhs.load_int_constant,
                });
               return true;
            }
        },

        // Noncommutative ops
        inline
        .less, .less_equal, .sub, .sub_mod, .divide, .modulus,
        .shift_left, .shift_right,
        => |bop, tag| {
            const swapped_tag: ?[]const u8 = comptime switch(tag) {
                .less => "greater_equal",
                .less_equal => "greater",
                else => null,
            };

            const lhs = decls.get(bop.lhs).instr;
            if(swapped_tag != null and lhs == .load_int_constant) {
                decl.instr = @unionInit(DeclInstr, swapped_tag.? ++ "_constant", .{
                    .lhs = bop.rhs,
                    .rhs = lhs.load_int_constant,
                });
            }

            const rhs = decls.get(bop.rhs).instr;
            if(rhs == .load_int_constant) {
                decl.instr = @unionInit(DeclInstr, @tagName(tag) ++ "_constant", .{
                    .lhs = bop.lhs,
                    .rhs = rhs.load_int_constant,
                });
               return true;
            }
        },

        else => {},
    }
    return false;
}

fn eliminateTrivialArithmetic(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    switch(decl.instr) {
        .add_constant, .add_mod_constant, .sub_constant, .sub_mod_constant,
        .shift_left_constant, .shift_right_constant,
        .bit_or_constant, .bit_xor_constant,
        => |bop| {
            if(bop.rhs == 0) {
                decl.instr = .{.copy = bop.lhs};
                return true;
            }
        },
        .multiply_constant, .multiply_mod_constant,
        => |bop| {
            if(bop.rhs == 1) {
                decl.instr = .{.copy = bop.lhs};
                return true;
            } else {
                const l2 = std.math.log2_int(u64, bop.rhs);
                if((@as(u64, 1) << l2) == bop.rhs) {
                    decl.instr = .{.shift_left_constant = .{.lhs = bop.lhs, .rhs = l2}};
                    return true;
                }
            }
        },
        .divide_constant => |bop| {
            if(bop.rhs == 0) {
                decl.instr = .{.@"undefined" = {}};
                return true;
            } else {
                const l2 = std.math.log2_int(u64, bop.rhs);
                if((@as(u64, 1) << l2) == bop.rhs) {
                    decl.instr = .{.shift_right_constant = .{.lhs = bop.lhs, .rhs = l2}};
                    return true;
                }
            }
        },
        .modulus_constant => |bop| {
            // TODO: check value against type size to optimize more
            if(bop.rhs == 0) {
                decl.instr = .{.@"undefined" = {}};
                return true;
            } else {
                const l2 = std.math.log2_int(u64, bop.rhs);
                if((@as(u64, 1) << l2) == bop.rhs) {
                    decl.instr = .{.bit_and_constant = .{.lhs = bop.lhs, .rhs = bop.rhs - 1}};
                    return true;
                }
            }
        },
        .bit_and_constant => |bop| {
            // TODO: check value against type size to optimize more
            if(bop.rhs == 0) {
                decl.instr = .{.load_int_constant = 0};
                return true;
            }
        },
        else => {},
    }

    return false;
}

fn eliminateConstantExpressions(decl_idx: DeclIndex.Index) !bool {
    const decl = decls.get(decl_idx);
    switch(decl.instr) {
        inline
        .add_constant, .add_mod_constant, .sub_constant, .sub_mod_constant,
        .multiply_constant, .multiply_mod_constant, .divide_constant, .modulus_constant,
        .shift_left_constant, .shift_right_constant, .bit_and_constant, .bit_or_constant, .bit_xor_constant,
        => |bop, tag| {
            const lhs = decls.get(bop.lhs);
            if(lhs.instr == .load_int_constant) {
                decl.instr = .{.load_int_constant = switch(tag) {
                    .add_constant => lhs.instr.load_int_constant + bop.rhs,
                    .add_mod_constant => lhs.instr.load_int_constant +% bop.rhs,
                    .sub_constant => lhs.instr.load_int_constant - bop.rhs,
                    .sub_mod_constant => lhs.instr.load_int_constant -% bop.rhs,
                    .multiply_constant => lhs.instr.load_int_constant * bop.rhs,
                    .multiply_mod_constant => lhs.instr.load_int_constant *% bop.rhs,
                    .divide_constant => lhs.instr.load_int_constant / bop.rhs,
                    .modulus_constant => lhs.instr.load_int_constant % bop.rhs,
                    .shift_left_constant => lhs.instr.load_int_constant << @intCast(u6, bop.rhs),
                    .shift_right_constant => lhs.instr.load_int_constant >> @intCast(u6, bop.rhs),
                    .bit_and_constant => lhs.instr.load_int_constant & bop.rhs,
                    .bit_or_constant => lhs.instr.load_int_constant | bop.rhs,
                    .bit_xor_constant => lhs.instr.load_int_constant ^ bop.rhs,
                    else => unreachable,
                }};
                return true;
            }
        },
        inline
        .less_constant, .less_equal_constant, .greater_constant, .greater_equal_constant,
        .equals_constant, .not_equal_constant,
        => |bop, tag| {
            const lhs = decls.get(bop.lhs);
            if(lhs.instr == .load_int_constant) {
                decl.instr = .{.load_bool_constant = switch(tag) {
                    .less_constant => lhs.instr.load_int_constant < bop.rhs,
                    .less_equal_constant => lhs.instr.load_int_constant <= bop.rhs,
                    .greater_constant => lhs.instr.load_int_constant > bop.rhs,
                    .greater_equal_constant => lhs.instr.load_int_constant >= bop.rhs,
                    .equals_constant => lhs.instr.load_int_constant == bop.rhs,
                    .not_equal_constant => lhs.instr.load_int_constant != bop.rhs,
                    else => unreachable,
                }};
                return true;
            }
        },
        else => {},
    }
    return false;
}

fn appendToBlock(block_idx: BlockIndex.Index, sema_decl: sema.DeclIndex.OptIndex, instr: DeclInstr) !DeclIndex.Index {
    const block = blocks.get(block_idx);

    var curr_instr = block.first_decl;
    while(decls.getOpt(curr_instr)) |inst| {
        if(std.meta.eql(inst.instr, instr)) return DeclIndex.unwrap(curr_instr).?;
        curr_instr = inst.next;
    }

    const retval = try decls.insert(.{
        .next = .none,
        .prev = .none,
        .block = block_idx,
        .instr = instr,
        .sema_decl = sema_decl,
    });
    const oretval = DeclIndex.toOpt(retval);

    if(decls.getOpt(block.last_decl)) |last| {
        last.next = oretval;
        decls.get(retval).prev = block.last_decl;
    }
    block.last_decl = oretval;

    if(block.first_decl == .none) {
        block.first_decl = oretval;
    }

    return retval;
}

fn addEdge(
    source_idx: BlockIndex.Index,
    target_idx: BlockIndex.Index,
) !BlockEdgeIndex.Index {
    const target_block = blocks.get(target_idx);

    std.debug.assert(!target_block.is_sealed);

    const retval = try edges.insert(.{
        .source_block = source_idx,
        .target_block = target_idx,
        .next = target_block.first_predecessor,
    });

    target_block.first_predecessor = BlockEdgeIndex.toOpt(retval);

    return retval;
}

fn doRegAlloc(
    allocator: std.mem.Allocator,
    block_list: *const BlockList,
    return_register: u8,
    arg_registers: []const u8,
    gprs: []const u8,
) !void {
    var to_visit = std.ArrayList(BlockIndex.Index).init(allocator);
    var has_visited = std.AutoHashMap(BlockIndex.Index, void).init(allocator);
    var is_alive = [_]bool{false} ** 256;

    for(block_list.items) |blk| {
        var current_decl = blocks.get(blk).last_decl;
        while(decls.getOpt(current_decl)) |decl| {
            // Is this a returning block?
            switch(decl.instr) {
                .param_ref => |pr| decl.reg_alloc_value = arg_registers[pr],
                .@"return" => {
                    try to_visit.append(blk);
                    try has_visited.put(blk, {});
                },
                else => {},
            }
            current_decl = decl.prev;
        }
    }

    while(to_visit.items.len > 0) {
        const blk_idx = to_visit.swapRemove(0);
        const blk = blocks.get(blk_idx);

        var current_edge = blk.first_predecessor;
        while(edges.getOpt(current_edge)) |edge| {
            if(has_visited.get(edge.source_block) == null) {
                try has_visited.put(edge.source_block, {});
                try to_visit.append(edge.source_block);
            }
            current_edge = edge.next;
        }

        var current_decl = blk.last_decl;
        while(decls.getOpt(current_decl)) |decl| {
            switch(decl.instr) {
                .@"return" => |op| {
                    if(decls.get(op).reg_alloc_value == null) {
                        is_alive[return_register] = true;
                        decls.get(op).reg_alloc_value = return_register;
                    }
                },
                else => {
                    if(decl.instr.isValue()) {
                        if(decl.reg_alloc_value) |reg| {
                            is_alive[reg] = false;
                        }
                    }

                    var operands = decl.instr.operands();
                    var first_operand = true;
                    while(operands.next()) |op_idx| {
                        const operand = decls.get(op_idx.*);
                        if(operand.reg_alloc_value == null) {
                            if(first_operand and decl.reg_alloc_value != null) {
                                const reg = decl.reg_alloc_value.?;
                                is_alive[reg] = true;
                                operand.reg_alloc_value = reg;
                            } else {
                                for(gprs) |reg| {
                                    if(!is_alive[reg]) {
                                        is_alive[reg] = true;
                                        operand.reg_alloc_value = reg;
                                        break;
                                    }
                                }
                            }
                        }
                        first_operand = false;
                    }
                },
            }
            current_decl = decl.prev;
        }
    }
}

fn ssaBlockStatementIntoBasicBlock(
    first_stmt: sema.StatementIndex.OptIndex,
    scope: sema.ScopeIndex.Index,
    basic_block: BlockIndex.Index,
) !BlockIndex.Index {
    _ = scope;
    var current_statement = first_stmt;
    var current_basic_block = basic_block;

    while(sema.statements.getOpt(current_statement)) |stmt| {
        switch(stmt.value) {
            .block => |b| {
                // A freestanding block statement is part of the same basic block but with a different scope
                // and TODO: a new break target location
                current_basic_block = try ssaBlockStatementIntoBasicBlock(b.first_stmt, b.scope, current_basic_block);
            },
            .declaration => |decl_idx| {
                const decl = sema.decls.get(decl_idx);
                const init_value = sema.values.get(decl.init_value);

                if(init_value.* == .runtime) {
                    const expr = init_value.runtime.expr;
                    _ = try ssaExpr(current_basic_block, sema.ExpressionIndex.unwrap(expr).?, sema.DeclIndex.toOpt(decl_idx));
                } else {
                    const value = try ssaValue(current_basic_block, decl.init_value, .none);
                    decls.get(value).sema_decl = sema.DeclIndex.toOpt(decl_idx);
                }
            },
            .expression => |expr_idx| {
                _ = try ssaExpr(current_basic_block, expr_idx, .none);
            },
            .if_statement => |if_stmt| {
                const condition_value = try ssaValue(current_basic_block, if_stmt.condition, .none);

                const if_branch = try appendToBlock(current_basic_block, .none, .{.@"if" = .{
                    .condition = condition_value,
                    .taken = undefined,
                    .not_taken = undefined,
                }});
                try blocks.get(current_basic_block).filled();

                const taken_entry = try blocks.insert(.{});
                const not_taken_entry = try blocks.insert(.{});
                decls.get(if_branch).instr.@"if".taken = try addEdge(current_basic_block, taken_entry);
                try blocks.get(taken_entry).seal();
                decls.get(if_branch).instr.@"if".not_taken = try addEdge(current_basic_block, not_taken_entry);
                try blocks.get(not_taken_entry).seal();

                const if_exit = try blocks.insert(.{});
                const taken_exit = try ssaBlockStatementIntoBasicBlock(
                    if_stmt.taken.first_stmt,
                    if_stmt.taken.scope,
                    taken_entry,
                );
                if(if_stmt.taken.reaches_end) {
                    const taken_exit_branch = try appendToBlock(taken_exit, .none, .{.goto = undefined});
                    decls.get(taken_exit_branch).instr.goto = try addEdge(taken_exit, if_exit);
                }
                try blocks.get(taken_exit).filled();

                const not_taken_exit = try ssaBlockStatementIntoBasicBlock(
                    if_stmt.not_taken.first_stmt,
                    if_stmt.not_taken.scope,
                    not_taken_entry,
                );
                if (if_stmt.not_taken.reaches_end) {
                    const not_taken_exit_branch = try appendToBlock(not_taken_exit, .none, .{.goto = undefined});
                    decls.get(not_taken_exit_branch).instr.goto = try addEdge(not_taken_exit, if_exit);
                }
                try blocks.get(not_taken_exit).filled();

                try blocks.get(if_exit).seal();

                current_basic_block = if_exit;
            },
            .loop_statement => |loop| {
                const loop_enter_branch = try appendToBlock(current_basic_block, .none, .{.goto = undefined});
                const loop_body_entry = try blocks.insert(.{});
                decls.get(loop_enter_branch).instr.goto = try addEdge(current_basic_block, loop_body_entry);
                try blocks.get(current_basic_block).filled();

                const exit_block = try blocks.insert(.{});
                stmt.ir_block = BlockIndex.toOpt(exit_block);
                const loop_body_end = try ssaBlockStatementIntoBasicBlock(
                    loop.body.first_stmt,
                    loop.body.scope,
                    loop_body_entry,
                );
                try blocks.get(exit_block).seal();
                if(loop.body.reaches_end) {
                    const loop_instr = try appendToBlock(loop_body_end, .none, .{.goto = undefined});
                    decls.get(loop_instr).instr.goto = try addEdge(loop_body_end, loop_body_entry);
                }
                try blocks.get(loop_body_end).filled();
                try blocks.get(loop_body_entry).seal();

                current_basic_block = exit_block;
            },
            .break_statement => |break_block| {
                const goto_block = BlockIndex.unwrap(sema.statements.get(break_block).ir_block).?;
                _ = try appendToBlock(current_basic_block, .none, .{.goto = try addEdge(current_basic_block, goto_block)});
            },
            .return_statement => |return_stmt| {
                var value = if(sema.ValueIndex.unwrap(return_stmt.value)) |sema_value| blk: {
                    break :blk try ssaValue(current_basic_block, sema_value, .none);
                } else blk: {
                    break :blk try appendToBlock(current_basic_block, .none, .{.@"undefined" = {}});
                };

                _ = try appendToBlock(current_basic_block, .none, .{.@"return" = value});
            },
        }
        current_statement = stmt.next;
    }
    return current_basic_block;
}

fn ssaValue(
    block_idx: BlockIndex.Index,
    value_idx: sema.ValueIndex.Index,
    update_with_value: DeclIndex.OptIndex,
) !DeclIndex.Index {
    switch(sema.values.get(value_idx).*) {
        .runtime => |rt| {
            // TODO: Reference assignment
            std.debug.assert(update_with_value == .none);
            return ssaExpr(block_idx, sema.ExpressionIndex.unwrap(rt.expr).?, .none);
        },
        .decl_ref => |decl_idx| {
            // TODO: Check if the decl has gotten its address taken.
            // If so, we need to do a memory load instead of an SSA passthrough.
            if(decls.getOpt(update_with_value)) |update| {
                return appendToBlock(block_idx, DeclIndex.toOpt(decl_idx), .{.copy = decls.getIndex(update)});
            } else {
                return readVariable(block_idx, decl_idx);
            }
        },
        .comptime_int => |value| {
            std.debug.assert(update_with_value == .none);
            return appendToBlock(block_idx, .none, .{.load_int_constant = @intCast(u64, value)});
        },
        .bool => |value| {
            std.debug.assert(update_with_value == .none);
            return appendToBlock(block_idx, .none, .{.load_bool_constant = value});
        },
        .unsigned_int => |value| {
            // TODO: Pass value bit width along too
            std.debug.assert(update_with_value == .none);
            return appendToBlock(block_idx, .none, .{.load_int_constant = @intCast(u64, value.value)});
        },
        else => |val| std.debug.panic("Unhandled ssaing of value {s}", .{@tagName(val)}),
    }
}

fn ssaExpr(block_idx: BlockIndex.Index, expr_idx: sema.ExpressionIndex.Index, update_decl: sema.DeclIndex.OptIndex) anyerror!DeclIndex.Index {
    switch(sema.expressions.get(expr_idx).*) {
        .value => |val_idx| return ssaValue(block_idx, val_idx, .none),
        .assign => |ass| {
            // Evaluate rhs first because it makes more lifetime sense for assignment ops
            const rhs = try ssaValue(block_idx, ass.rhs, .none);

            if(ass.lhs != .discard_underscore) {
                _ = try ssaValue(block_idx, ass.lhs, DeclIndex.toOpt(rhs));

                // TODO: Handle reference types on lhs
                return undefined;
            }

            return undefined;
        },
        inline
        .add, .add_mod, .sub, .sub_mod,
        .multiply, .multiply_mod, .divide, .modulus,
        .shift_left, .shift_right, .bit_and, .bit_or, .bit_xor,
        .less, .less_equal, .equals, .not_equal,
        => |bop, tag| {
            return appendToBlock(block_idx, update_decl, @unionInit(DeclInstr, @tagName(tag), .{
                .lhs = try ssaValue(block_idx, bop.lhs, .none),
                .rhs = try ssaValue(block_idx, bop.rhs, .none),
            }));
        },
        inline
        .add_eq, .add_mod_eq, .sub_eq, .sub_mod_eq,
        .multiply_eq, .multiply_mod_eq, .divide_eq, .modulus_eq,
        .shift_left_eq, .shift_right_eq, .bit_and_eq, .bit_or_eq, .bit_xor_eq,
        => |bop, tag| {
            const value = try appendToBlock(block_idx, .none, @unionInit(DeclInstr, @tagName(tag)[0..@tagName(tag).len - 3], .{
                .lhs = try ssaValue(block_idx, bop.lhs, .none),
                .rhs = try ssaValue(block_idx, bop.rhs, .none),
            }));
            return try ssaValue(block_idx, bop.lhs, DeclIndex.toOpt(value));
        },
        .greater => |bop| return appendToBlock(block_idx, update_decl, .{.less_equal = .{
            .lhs = try ssaValue(block_idx, bop.rhs, .none),
            .rhs = try ssaValue(block_idx, bop.lhs, .none),
        }}),
        .greater_equal => |bop| return appendToBlock(block_idx, update_decl, .{.less = .{
            .lhs = try ssaValue(block_idx, bop.rhs, .none),
            .rhs = try ssaValue(block_idx, bop.lhs, .none),
        }}),
        else => |expr| std.debug.panic("Unhandled ssaing of expr {s}", .{@tagName(expr)}),
    }
}

fn ssaFunction(func: *sema.Function) !BlockIndex.Index {
    const first_basic_block = try blocks.insert(.{});
    try blocks.get(first_basic_block).seal();

    // Loop over function params and add references to them
    var curr_param = sema.scopes.get(func.param_scope).first_decl;
    while(sema.decls.getOpt(curr_param)) |decl| {
        _ = try appendToBlock(first_basic_block, curr_param, .{
            .param_ref = decl.function_param_idx.?,
        });

        curr_param = decl.next;
    }

    const return_block = try ssaBlockStatementIntoBasicBlock(func.body.first_stmt, func.body.scope, first_basic_block);
    // TODO: Place implicit return statement here
    _ = return_block;
    return first_basic_block;
}

pub fn memes(thing: *sema.Value) !void {
    const bbidx = try ssaFunction(&thing.function);

    try optimizeFunction(bbidx);

    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);

    const curr_backend = backend.x86_64;
    const blocks_to_dump = try allBlocksReachableFrom(arena.allocator(), bbidx);

    try doRegAlloc(
        arena.allocator(),
        &blocks_to_dump,
        curr_backend.registers.return_reg,
        &curr_backend.registers.param_regs,
        &curr_backend.registers.gprs,
    );

    for(blocks_to_dump.items) |bb| {
        std.debug.print("Block#{d}:\n", .{@enumToInt(bb)});
        var current_decl = blocks.get(bb).first_decl;
        while(decls.getOpt(current_decl)) |decl| {
            std.debug.print("  ", .{});
            if(decl.instr.isValue()) {
                std.debug.print("${d}", .{@enumToInt(current_decl)});
                if(decl.reg_alloc_value) |reg| {
                    std.debug.print(" (reg #{d})", .{reg});
                }
                std.debug.print(" = ", .{});
            }
            switch(decl.instr) {
                .param_ref => |p| std.debug.print("@param({d})\n", .{p}),
                .load_int_constant => |value| std.debug.print("{d}\n", .{value}),
                .load_bool_constant => |b| std.debug.print("{}\n", .{b}),
                .@"undefined" => std.debug.print("undefined\n", .{}),
                inline
                .add, .add_mod, .sub, .sub_mod,
                .multiply, .multiply_mod, .divide, .modulus,
                .shift_left, .shift_right, .bit_and, .bit_or, .bit_xor,
                .less, .less_equal, .equals, .not_equal,
                => |bop, tag| std.debug.print("{s}(${d}, ${d})\n", .{@tagName(tag), @enumToInt(bop.lhs), @enumToInt(bop.rhs)}),
                inline
                .add_constant, .add_mod_constant, .sub_constant, .sub_mod_constant,
                .multiply_constant, .multiply_mod_constant, .divide_constant, .modulus_constant,
                .shift_left_constant, .shift_right_constant, .bit_and_constant, .bit_or_constant, .bit_xor_constant,
                .less_constant, .less_equal_constant, .greater_constant, .greater_equal_constant,
                .equals_constant, .not_equal_constant
                => |bop, tag| std.debug.print("{s}(${d}, #{d})\n", .{@tagName(tag)[0..@tagName(tag).len-9], @enumToInt(bop.lhs), bop.rhs}),
                .incomplete_phi => std.debug.print("<incomplete phi node>\n", .{}),
                .copy => |c| std.debug.print("@copy(${d})\n", .{@enumToInt(c)}),
                .@"if" => |if_instr| {
                    std.debug.print("if(${d}, Block#{d}, Block#{d})\n", .{
                        @enumToInt(if_instr.condition),
                        @enumToInt(edges.get(if_instr.taken).target_block),
                        @enumToInt(edges.get(if_instr.not_taken).target_block),
                    });
                },
                .@"return" => |value| std.debug.print("return ${d}\n", .{@enumToInt(value)}),
                .goto => |goto_edge| {
                    std.debug.print("goto(Block#{d})\n", .{@enumToInt(edges.get(goto_edge).target_block)});
                },
                .phi => |phi_index| {
                    var current_phi = PhiOperandIndex.toOpt(phi_index);
                    std.debug.print("phi(", .{});
                    while(phi_operands.getOpt(current_phi)) |phi| {
                        const edge = edges.get(phi.edge);
                        std.debug.print("[${d}, Block#{d}]", .{@enumToInt(phi.decl), @enumToInt(edge.source_block)});
                        if(phi.next != .none) {
                            std.debug.print(", ", .{});
                        }
                        current_phi = phi.next;
                    }
                    std.debug.print(")\n", .{});
                },
            }
            current_decl = decl.next;
        }
        std.debug.print("\n", .{});
    }

    var writer = backend.Writer(curr_backend){
        .allocator = optimization_allocator.allocator(),
    };
    try writer.writeFunction(bbidx);
}

pub fn init() !void {
    decls = try DeclIndex.List(Decl).init(std.heap.page_allocator);
    blocks = try BlockIndex.List(BasicBlock).init(std.heap.page_allocator);
    edges = try BlockEdgeIndex.List(InstructionToBlockEdge).init(std.heap.page_allocator);
    phi_operands = try PhiOperandIndex.List(PhiOperand).init(std.heap.page_allocator);
}

const indexed_list = @import("indexed_list.zig");

const std = @import("std");

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

const DeclInstr = union(enum) {
    param_ref: u8,
    load_bool_constant: bool,
    add: Bop,
    incomplete_phi: DeclIndex.OptIndex, // Holds the next incomplete phi node in the same block
    copy: DeclIndex.Index, // Should be eliminated during optimization
    @"if": struct {
        condition: DeclIndex.Index,
        taken: BlockEdgeIndex.Index,
        not_taken: BlockEdgeIndex.Index,
    },
    goto: BlockEdgeIndex.Index,
    phi: PhiOperandIndex.Index,
};

pub const Decl = struct {
    next: DeclIndex.OptIndex = .none,
    prev: DeclIndex.OptIndex = .none,
    //block: BlockIndex.Index,

    sema_decl: sema.DeclIndex.OptIndex,
    instr: DeclInstr,
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
fn addPhiOperands(sema_decl: sema.DeclIndex.Index, block_idx: BlockIndex.Index, decl_idx: DeclIndex.Index, delete: bool) !DeclIndex.Index {
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

    decls.get(decl_idx).instr = .{
        .phi = PhiOperandIndex.unwrap(init_operand).?,
    };

    _ = delete;
    return decl_idx;
}

fn appendToBlock(block_idx: BlockIndex.Index, sema_decl: sema.DeclIndex.OptIndex, instr: DeclInstr) !DeclIndex.Index {
    const block = blocks.get(block_idx);

    std.debug.assert(!block.is_filled);

    var curr_instr = block.first_decl;
    while(decls.getOpt(curr_instr)) |inst| {
        if(std.meta.eql(inst.instr, instr)) return DeclIndex.unwrap(curr_instr).?;
        curr_instr = inst.next;
    }

    const retval = try decls.insert(.{
        .next = .none,
        .prev = .none,
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
            .declaration, .expression => {
                switch(stmt.value) {
                    .declaration => |decl_idx| {
                        const decl = sema.decls.get(decl_idx);
                        const init_value = sema.values.get(decl.init_value);

                        if(init_value.* == .runtime) {
                            const expr = init_value.runtime.expr;
                            _ = try ssaExpr(current_basic_block, sema.ExpressionIndex.unwrap(expr).?, sema.DeclIndex.toOpt(decl_idx));
                        }
                    },
                    .expression => |expr_idx| {
                        _ = try ssaExpr(current_basic_block, expr_idx, .none);
                    },
                    else => unreachable,
                }
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
                const taken_exit_branch = try appendToBlock(taken_exit, .none, .{.goto = undefined});
                try blocks.get(taken_exit).filled();
                decls.get(taken_exit_branch).instr.goto = try addEdge(taken_exit, if_exit);

                const not_taken_exit = try ssaBlockStatementIntoBasicBlock(
                    if_stmt.not_taken.first_stmt,
                    if_stmt.not_taken.scope,
                    not_taken_entry,
                );
                const not_taken_exit_branch = try appendToBlock(not_taken_exit, .none, .{.goto = undefined});
                try blocks.get(not_taken_exit).filled();
                decls.get(not_taken_exit_branch).instr.goto = try addEdge(not_taken_exit, if_exit);

                try blocks.get(if_exit).seal();

                current_basic_block = if_exit;
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
        .bool => |value| {
            std.debug.assert(update_with_value == .none);
            return appendToBlock(block_idx, .none, .{.load_bool_constant = value});
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
        .plus => |bop| {
            return appendToBlock(block_idx, update_decl, .{.add = .{
                .lhs = try ssaValue(block_idx, bop.lhs, .none),
                .rhs = try ssaValue(block_idx, bop.rhs, .none),
            }});
        },
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

    var blocks_to_dump = try std.ArrayList(BlockIndex.Index).initCapacity(std.heap.page_allocator, 1024);
    var blocks_visited = std.AutoHashMap(BlockIndex.Index, void).init(std.heap.page_allocator);
    defer blocks_to_dump.deinit();
    defer blocks_visited.deinit();
    try blocks_to_dump.append(bbidx);

    while(blocks_to_dump.items.len > 0) {
        const bb = blocks_to_dump.swapRemove(0);
        std.debug.print("Block#{d}:\n", .{@enumToInt(bb)});
        var current_decl = blocks.get(bb).first_decl;
        while(decls.getOpt(current_decl)) |decl| {
            std.debug.print("  ${d} (decl #{d}) = ", .{@enumToInt(current_decl), @enumToInt(decl.sema_decl)});
            switch(decl.instr) {
                .param_ref => |p| std.debug.print("@param({d})\n", .{p}),
                .load_bool_constant => |b| std.debug.print("{}\n", .{b}),
                .add => |a| std.debug.print("${d} + ${d}\n", .{@enumToInt(a.lhs), @enumToInt(a.rhs)}),
                .incomplete_phi => std.debug.print("<incomplete phi node>\n", .{}),
                .copy => |c| std.debug.print("@copy(${d})\n", .{@enumToInt(c)}),
                .@"if" => |if_instr| {
                    const taken_edge = edges.get(if_instr.taken);
                    const not_taken_edge = edges.get(if_instr.not_taken);
                    if(!blocks_visited.contains(taken_edge.target_block)) {
                        try blocks_to_dump.append(taken_edge.target_block);
                        try blocks_visited.put(taken_edge.target_block, {});
                    }
                    if(!blocks_visited.contains(not_taken_edge.target_block)) {
                        try blocks_to_dump.append(not_taken_edge.target_block);
                        try blocks_visited.put(not_taken_edge.target_block, {});
                    }
                    std.debug.print("if(${d}, Block#{d}, Block#{d})\n", .{
                        @enumToInt(if_instr.condition),
                        @enumToInt(taken_edge.target_block),
                        @enumToInt(not_taken_edge.target_block),
                    });
                },
                .goto => |goto_edge| {
                    const edge = edges.get(goto_edge);
                    if(!blocks_visited.contains(edge.target_block)) {
                        try blocks_to_dump.append(edge.target_block);
                        try blocks_visited.put(edge.target_block, {});
                    }
                    std.debug.print("goto(Block#{d})\n", .{@enumToInt(edge.target_block)});
                },
                .phi => |phi_index| {
                    var current_phi = PhiOperandIndex.toOpt(phi_index);
                    std.debug.print("φ(", .{});
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
}

pub fn init() !void {
    decls = try DeclIndex.List(Decl).init(std.heap.page_allocator);
    blocks = try BlockIndex.List(BasicBlock).init(std.heap.page_allocator);
    edges = try BlockEdgeIndex.List(InstructionToBlockEdge).init(std.heap.page_allocator);
    phi_operands = try PhiOperandIndex.List(PhiOperand).init(std.heap.page_allocator);
}

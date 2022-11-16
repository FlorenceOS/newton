const indexed_list = @import("indexed_list.zig");

const std = @import("std");

const sema = @import("sema.zig");

pub const DeclIndex = indexed_list.Indices(u32, .{});
pub const BlockIndex = indexed_list.Indices(u32, .{});
pub const BlockEdgeIndex = indexed_list.Indices(u32, .{});
pub const PhiArgumentIndex = indexed_list.Indices(u32, .{});

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
    add: Bop,
    incomplete_phi: DeclIndex.OptIndex, // Holds the next incomplete phi node in the same block
    copy: DeclIndex.Index, // Should be eliminated during optimization

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = options;
        _ = fmt;

        try switch(self) {
            .param_ref => |p| writer.print("@param({d})", .{p}),
            .add => |a| writer.print("${d} + ${d}", .{@enumToInt(a.lhs), @enumToInt(a.rhs)}),
            .incomplete_phi => writer.print("<incomplete phi node>", .{}),
            .copy => |c| writer.print("@copy(${d})", .{c}),
        };
    }
};

pub const Decl = struct {
    next: DeclIndex.OptIndex = .none,
    prev: DeclIndex.OptIndex = .none,
    //block: BlockIndex.Index,

    sema_decl: sema.DeclIndex.OptIndex,
    instr: DeclInstr,
};

const InstructionToBlockEdge = struct {
    source_instruction: DeclIndex.Index,
    target_block: Decl
};

pub const BasicBlock = struct {
    sealed: bool,
    filled: bool,
    first_incomplete_phi_node: DeclIndex.OptIndex = .none,
    first_predecessor: BlockEdgeIndex.OptIndex,
    first_decl: DeclIndex.OptIndex = .none,
    last_decl: DeclIndex.OptIndex = .none,

    pub fn seal(self: *@This()) !void {
        while(decls.getOpt(self.first_incomplete_phi_node)) |decl| {
            self.first_incomplete_phi_node = decl.incomplete_phi;
            try addPhiOperands(decl.sema_decl, blocks.getIndex(self), decls.getIndex(decl));
        }
        self.sealed = true;
    }
};

pub var decls: DeclIndex.List(Decl) = undefined;
pub var blocks: BlockIndex.List(BasicBlock) = undefined;

// Name from paper
fn readVariable(block_idx: BlockIndex.Index, decl: sema.DeclIndex.Index, pred_instr: DeclIndex.OptIndex) !DeclIndex.Index {
    const odecl = sema.DeclIndex.toOpt(decl);
    // Look backwards to find value in current basic block
    var pred_idx = pred_instr;
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
    if(!block.sealed) {
        const new_phi = try appendToBlock(block_idx, odecl, .{
            .incomplete_phi = block.first_incomplete_phi_node,
        });
        block.first_incomplete_phi_node = DeclIndex.toOpt(new_phi);
        return new_phi;
    } else if (false) { // Block has 1 predecessor
        @panic("readVariableRecursive 1 predecessor");
    } else if(false) { // Block has 0 predecessors
        @panic("readVariableRecursive 0 predecessors");
    } else {
        // Block gets new phi node
        @panic("readVariableRecursive many predecessors");
    }
}

// Name from paper
fn addPhiOperands(sema_decl: sema.DeclIndex.OptIndex, block_idx: BlockIndex.Index, decl_idx: DeclIndex.Index) !void {
    _ = sema_decl;
    _ = block_idx;
    _ = decl_idx;
    @panic("addPhiOperands");
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

var stack_gpa = std.heap.GeneralPurposeAllocator(.{}){.backing_allocator = std.heap.page_allocator};

fn ssaBlockStatementIntoBasicBlock(
    first_stmt: sema.StatementIndex.OptIndex,
    scope: sema.ScopeIndex.Index,
    basic_block: BlockIndex.Index,
) !void {
    _ = scope;
    var current_statement = first_stmt;

    while(sema.statements.getOpt(current_statement)) |stmt| {
        switch(stmt.value) {
            .block => |b| {
                // A freestanding block statement is part of the same basic block but with a different scope
                // and TODO: a new break target location
                try ssaBlockStatementIntoBasicBlock(b.first_stmt, b.scope, basic_block);
            },
            .declaration, .expression => {
                switch(stmt.value) {
                    .declaration => |decl_idx| {
                        const decl = sema.decls.get(decl_idx);
                        const init_value = sema.values.get(decl.init_value);

                        if(init_value.* == .runtime) {
                            const expr = init_value.runtime.expr;
                            _ = try ssaExpr(basic_block, sema.ExpressionIndex.unwrap(expr).?, sema.DeclIndex.toOpt(decl_idx));
                        }
                    },
                    .expression => |expr_idx| {
                        _ = try ssaExpr(basic_block, expr_idx, .none);
                    },
                    else => unreachable,
                }
            },
        }
        current_statement = stmt.next;
    }
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
                return readVariable(block_idx, decl_idx, blocks.get(block_idx).last_decl);
            }
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
    const first_basic_block = try blocks.insert(.{
        .first_predecessor = .none,
        .sealed = true,
        .filled = false,
    });

    // Loop over function params and add references to them
    var curr_param = sema.scopes.get(func.param_scope).first_decl;
    while(sema.decls.getOpt(curr_param)) |decl| {
        _ = try appendToBlock(first_basic_block, curr_param, .{
            .param_ref = decl.function_param_idx.?,
        });

        curr_param = decl.next;
    }

    _ = try ssaBlockStatementIntoBasicBlock(func.body.first_stmt, func.body.scope, first_basic_block);
    return first_basic_block;
}

pub fn memes(thing: *sema.Value) !void {
    const bbidx = try ssaFunction(&thing.function);
    std.debug.print("SSA dump:\n", .{});
    var current_decl = blocks.get(bbidx).first_decl;
    while(decls.getOpt(current_decl)) |decl| {
        std.debug.print(" ${d} (decl #{d}) = {}\n", .{@enumToInt(current_decl), @enumToInt(decl.sema_decl), decl.instr});
        current_decl = decl.next;
    }
}

pub fn init() !void {
    decls = try DeclIndex.List(Decl).init(std.heap.page_allocator);
    blocks = try BlockIndex.List(BasicBlock).init(std.heap.page_allocator);
}

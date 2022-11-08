const indexed_list = @import("indexed_list.zig");

const std = @import("std");

const sema = @import("sema.zig");

pub const DeclIndex = indexed_list.Indices(u32, .{});
pub const BlockIndex = indexed_list.Indices(u32, .{});

pub const Bop = struct {
    lhs: DeclIndex.Index,
    rhs: DeclIndex.Index,
};

const DeclInstr = union(enum) {
    param_ref: u8,
    add: Bop,

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
        };
    }
};

pub const Decl = struct {
    next: DeclIndex.OptIndex = .none,
    prev: DeclIndex.OptIndex = .none,
    //block: BlockIndex.Index,

    instr: DeclInstr,
};

pub const BasicBlock = struct {
    first_decl: DeclIndex.OptIndex = .none,
    last_decl: DeclIndex.OptIndex = .none,
};

pub var decls: DeclIndex.List(Decl) = undefined;
pub var blocks: BlockIndex.List(BasicBlock) = undefined;

fn appendToBlock(block_idx: BlockIndex.Index, instr: DeclInstr) !DeclIndex.Index {
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

pub const DeclContext = struct {
    const SSADecl = struct {
        ssa_id: DeclIndex.Index,
        ssa_block: BlockIndex.Index,
    };

    ssa_id_stack: std.ArrayListUnmanaged(SSADecl) = .{},
};

var stack_gpa = std.heap.GeneralPurposeAllocator(.{}){.backing_allocator = std.heap.page_allocator};

fn ssaBlockStatementIntoBasicBlock(
    first_stmt: sema.StatementIndex.OptIndex,
    scope: sema.ScopeIndex.Index,
    basic_block_out: *BlockIndex.OptIndex,
) !void {
    _ = scope;
    var current_statement = first_stmt;

    while(sema.statements.getOpt(current_statement)) |stmt| {
        switch(stmt.value) {
            .block => |b| {
                // A freestanding block statement is part of the same basic block but with a different scope
                try ssaBlockStatementIntoBasicBlock(b.first_stmt, b.scope, basic_block_out);
            },
            .declaration, .expression => {
                // Now we have to make a basic block because there is none yet
                if(basic_block_out.* == .none) {
                    basic_block_out.* = BlockIndex.toOpt(try blocks.insert(.{}));
                }
                const bb = BlockIndex.unwrap(basic_block_out.*).?;

                switch(stmt.value) {
                    .declaration => |decl_idx| {
                        const decl = sema.decls.get(decl_idx);
                        const init_value = sema.values.get(decl.init_value);
                        if(init_value.* == .runtime) {
                            const expr = init_value.runtime.expr;
                            try decl.ir_context.ssa_id_stack.append(stack_gpa.allocator(), .{
                                .ssa_id = DeclIndex.unwrap(try ssaExpr(bb, sema.ExpressionIndex.unwrap(expr).?)).?,
                                .ssa_block = bb,
                            });
                        }
                    },
                    .expression => |expr_idx| {
                        _ = try ssaExpr(bb, expr_idx);
                    },
                    else => unreachable,
                }
            },
        }
        current_statement = stmt.next;
    }
}

// Returns the first basic block in the block statement
fn ssaBlockStatement(first_stmt: sema.StatementIndex.OptIndex, scope: sema.ScopeIndex.Index) !BlockIndex.OptIndex {
    var first_basic_block: BlockIndex.OptIndex = .none;
    _ = try ssaBlockStatementIntoBasicBlock(first_stmt, scope, &first_basic_block);
    return first_basic_block;
}

fn ssaValue(
    block_idx: BlockIndex.Index,
    value_idx: sema.ValueIndex.Index,
    update_with_value: DeclIndex.OptIndex,
) !DeclIndex.OptIndex {
    switch(sema.values.get(value_idx).*) {
        .runtime => |rt| return ssaExpr(block_idx, sema.ExpressionIndex.unwrap(rt.expr).?),
        .decl_ref => |decl_idx| {
            const decl = sema.decls.get(decl_idx);
            if(DeclIndex.unwrap(update_with_value)) |new_value| {
                try decl.ir_context.ssa_id_stack.append(stack_gpa.allocator(), .{
                    .ssa_block = block_idx,
                    .ssa_id = new_value,
                });
                return .none;
            } else {
                return DeclIndex.toOpt(decl.ir_context.ssa_id_stack.items[decl.ir_context.ssa_id_stack.items.len - 1].ssa_id);
            }
        },
        else => |val| std.debug.panic("Unhandled ssaing of value {s}", .{@tagName(val)}),
    }
}

fn ssaExpr(block_idx: BlockIndex.Index, expr_idx: sema.ExpressionIndex.Index) anyerror!DeclIndex.OptIndex {
    switch(sema.expressions.get(expr_idx).*) {
        .value => |val_idx| return ssaValue(block_idx, val_idx, .none),
        .assign => |ass| {
            // Evaluate rhs first because it makes more lifetime sense for assignment ops
            const rhs = try ssaValue(block_idx, ass.rhs, .none);

            if(ass.lhs != .discard_underscore) {
                _ = try ssaValue(block_idx, ass.lhs, rhs);

                // TODO: Handle reference types on lhs
                return .none;
            }

            return .none;
        },
        .plus => |bop| {
            return DeclIndex.toOpt(try appendToBlock(block_idx, .{.add = .{
                .lhs = DeclIndex.unwrap(try ssaValue(block_idx, bop.lhs, .none)).?,
                .rhs = DeclIndex.unwrap(try ssaValue(block_idx, bop.rhs, .none)).?,
            }}));
        },
        else => |expr| std.debug.panic("Unhandled ssaing of expr {s}", .{@tagName(expr)}),
    }
}

fn ssaFunction(func: *sema.Function) !BlockIndex.OptIndex {
    var first_basic_block: BlockIndex.OptIndex = BlockIndex.toOpt(try blocks.insert(.{}));

    // Loop over function params and add references to them
    var curr_param = sema.scopes.get(func.param_scope).first_decl;
    while(sema.decls.getOpt(curr_param)) |decl| {
        try decl.ir_context.ssa_id_stack.append(
            stack_gpa.allocator(),
            .{
                .ssa_id = try appendToBlock(BlockIndex.unwrap(first_basic_block).?, .{
                    .param_ref = decl.function_param_idx.?,
                }),
                .ssa_block = BlockIndex.unwrap(first_basic_block).?,
            },
        );

        curr_param = decl.next;
    }

    _ = try ssaBlockStatementIntoBasicBlock(func.body.first_stmt, func.body.scope, &first_basic_block);
    return first_basic_block;
}

pub fn memes(thing: *sema.Value) !void {
    const bbidx = try ssaFunction(&thing.function);
    std.debug.print("SSA dump:\n", .{});
    var current_decl = blocks.getOpt(bbidx).?.first_decl;
    while(decls.getOpt(current_decl)) |decl| {
        std.debug.print(" ${d} = {}\n", .{@enumToInt(current_decl), decl.instr});
        current_decl = decl.next;
    }
}

pub fn init() !void {
    decls = try DeclIndex.List(Decl).init(std.heap.page_allocator);
    blocks = try BlockIndex.List(BasicBlock).init(std.heap.page_allocator);
}

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
    add: Bop,
};

pub const Decl = struct {
    next: DeclIndex.OptIndex = .none,
    prev: DeclIndex.OptIndex = .none,
    //block: BlockIndex.Index,

    instr: DeclInstr,
};

pub const BasicBlock = struct {
    first_decl: DeclIndex.OptIndex,
    last_decl: DeclIndex.OptIndex,
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

fn ssaExpr(block_idx: BlockIndex.Index, expr_idx: sema.ExpressionIndex.Index) !DeclIndex.Index {
    switch(sema.expressions.get(expr_idx).*) {
        .plus => return appendToBlock(block_idx, .{.add = undefined}),
        else => |expr| std.debug.panic("Unhandled ssaing of expr {s}", .{@tagName(expr)}),
    }
}

// pub fn memes(thing: *sema.Value) !void {
//     const assign_statement = sema.statements.getOpt(thing.function.body.first_stmt).?;
//     std.debug.print("--{}\n", .{assign_statement});
//     const assign_value_idx = sema.expressions.get(assign_statement.value.expression).value;
//     const assign_value = sema.values.get(assign_value_idx);
//     const assign_expr = sema.expressions.getOpt(assign_value.runtime.expr).?.assign;
//     const addition_expr = sema.ExpressionIndex.unwrap(sema.values.get(assign_expr.rhs).runtime.expr).?;
//     std.debug.print("--{}\n", .{addition_expr});
//     const bidx = try blocks.insert(.{
//         .first_decl = .none,
//         .last_decl = .none,
//     });
//     const decl_idx = try ssaExpr(bidx, addition_expr);
//     _ = decl_idx;

//     std.debug.print("--{}\n", .{blocks.get(bidx)});
// }

pub fn init() !void {
    decls = try DeclIndex.List(Decl).init(std.heap.page_allocator);
    blocks = try BlockIndex.List(BasicBlock).init(std.heap.page_allocator);
}

const std = @import("std");

const backend = @import("backend.zig");
const ir = @import("ir.zig");
const rega = @import("rega.zig");

pub const registers = struct {
    const rax = 0;
    const rcx = 1;
    const rdx = 2;
    const rbx = 3;
    const rsp = 4;
    const rbp = 5;
    const rsi = 6;
    const rdi = 7;
    const r8 = 8;
    const r9 = 9;
    const r10 = 10;
    const r11 = 11;
    const r12 = 12;
    const r13 = 13;
    const r14 = 14;
    const r15 = 15;

    pub const return_reg = rax;
    pub const gprs = [_]u8{rax, rcx, rdx, rbx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15};
    pub const param_regs = [_]u8{rdi, rsi, rdx, rcx, r8, r9};
};

const cond_flags = struct {
    const not = 1;

    const below = 2;       // Less than unsigned
    const zero = 4;        // Also equal
    const below_equal = 6; // Less than unsigned or equal
};

pub fn writeDecl(writer: *backend.Writer(@This()), decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .@"undefined",
        => {},
        .add => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            if(dest_reg == lhs_reg) {
                try writer.writeInt(u8, 0x48
                    | @as(u8, @boolToInt(dest_reg >= 8)) << 0
                    | @as(u8, @boolToInt(rhs_reg >= 8)) << 2
                );
                try writer.writeInt(u8, 0x01);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7) | ((rhs_reg & 0x7) << 3));
            } else if(dest_reg == rhs_reg) {
                try writer.writeInt(u8, 0x48
                    | @as(u8, @boolToInt(dest_reg >= 8)) << 0
                    | @as(u8, @boolToInt(lhs_reg >= 8)) << 2
                );
                try writer.writeInt(u8, 0x01);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7) | ((lhs_reg & 0x7) << 3));
            } else {
                try writer.writeInt(u8, 0x48
                    | @as(u8, @boolToInt(lhs_reg >= 8)) << 0
                    | @as(u8, @boolToInt(rhs_reg >= 8)) << 1
                    | @as(u8, @boolToInt(dest_reg >= 8)) << 2
                );
                try writer.writeInt(u8, 0x8D);
                try writer.writeInt(u8, ((dest_reg & 0x7) << 3) | 4);
                try writer.writeInt(u8, ((rhs_reg & 0x7) << 3) | (lhs_reg & 0x7));
            }
        },
        .add_constant => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            if(dest_reg == lhs_reg) {
                if(bop.rhs == 1) { // inc r64
                    try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                    try writer.writeInt(u8, 0xFF);
                    try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7));
                } else { // add r64, imm32
                    try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                    try writer.writeInt(u8, 0x81);
                    try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7));
                    try writer.writeInt(u32, @intCast(u32, bop.rhs));
                }
            } else { // lea r64, [r64 + imm32]
                try writer.writeInt(u8, 0x48
                    | @as(u8, @boolToInt(lhs_reg >= 8)) << 0
                    | @as(u8, @boolToInt(dest_reg >= 8)) << 2
                );
                try writer.writeInt(u8, 0x8D);
                try writer.writeInt(u8, 0x80 | (lhs_reg & 0x7) | ((dest_reg & 0x7) << 3));
                try writer.writeInt(u32, @intCast(u32, bop.rhs));
            }
        },
        .multiply => |bop| {
            // TODO: HIGH REGS
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;

            std.debug.assert(lhs_reg == registers.rax);
            std.debug.assert(dest_reg == registers.rax);
            try writer.writeInt(u8, 0x48);
            try writer.writeInt(u8, 0xF7);
            try writer.writeInt(u8, 0xE0 | rhs_reg);
        },
        .goto => |edge| {
            if(try writer.attemptInlineEdge(edge)) |bidx| {
                return bidx;
            } else {
                try writer.writeInt(u8, 0xE9);
                try writer.writeRelocatedValue(edge, .rel32_post_0);
            }
        },
        .copy => |cope| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const src_reg = uf.findDecl(cope).reg_alloc_value.?;
            if(dest_reg == src_reg) return null;
            try writer.writeInt(u8, 0x48
                | @as(u8, @boolToInt(dest_reg >= 8)) << 0
                | @as(u8, @boolToInt(src_reg >= 8)) << 2
            );
            try writer.writeInt(u8, 0x89);
            try writer.writeInt(u8, 0xC0 | ((src_reg & 0x7) << 3) | (dest_reg & 0x7));
        },
        .load_int_constant => |c| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            if(c == 0) {
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)) * 5);
                try writer.writeInt(u8, 0x31);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7) * 9);
            } else {
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                try writer.writeInt(u8, 0xC7);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7));
                try writer.writeInt(u32, @intCast(u32, c));
            }
        },
        .less_constant, .less_equal_constant,
        .greater_constant, .greater_equal_constant,
        .equals_constant, .not_equal_constant,
        => |bop| {
            const reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(reg >= 8)));
            try writer.writeInt(u8, 0x81);
            try writer.writeInt(u8, 0xF8 | (reg & 0x7));
            try writer.writeInt(u32, @truncate(u32, bop.rhs));
        },
        .less, .less_equal, .equals, .not_equal,
        => |bop| {
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try writer.writeInt(u8, 0x48
                | @as(u8, @boolToInt(lhs_reg >= 8)) << 0
                | @as(u8, @boolToInt(rhs_reg >= 8)) << 2
            );
            try writer.writeInt(u8, 0x39);
            try writer.writeInt(u8, 0xC0 | ((rhs_reg & 0x7) << 3) | (lhs_reg & 0x7));
        },
        .@"if" => |op| {
            const op_instr = ir.decls.get(op.condition).instr;
            const cond_flag: u8 = switch(op_instr) {
                .less, .less_constant, => cond_flags.below,
                .less_equal, .less_equal_constant => cond_flags.below_equal,
                .greater_constant => cond_flags.not | cond_flags.below_equal,
                .greater_equal_constant => cond_flags.not | cond_flags.below,
                .equals, .equals_constant => cond_flags.zero,
                .not_equal, .not_equal_constant => cond_flags.not | cond_flags.zero,
                else => unreachable,
            };
            if(try writer.attemptInlineEdge(op.not_taken)) |bidx| {
                try writer.writeInt(u8, 0x0F);
                try writer.writeInt(u8, 0x80 | cond_flag);
                try writer.writeRelocatedValue(op.taken, .rel32_post_0);
                return bidx;
            } else if(try writer.attemptInlineEdge(op.taken)) |bidx| {
                try writer.writeInt(u8, 0x0F);
                try writer.writeInt(u8, 0x80 | cond_flag ^ cond_flags.not);
                try writer.writeRelocatedValue(op.not_taken, .rel32_post_0);
                return bidx;
            } else {
                try writer.writeInt(u8, 0x0F);
                try writer.writeInt(u8, 0x80 | cond_flag);
                try writer.writeRelocatedValue(op.taken, .rel32_post_0);
                try writer.writeInt(u8, 0xE9);
                try writer.writeRelocatedValue(op.not_taken, .rel32_post_0);
            }
        },
        .@"return" => |op| {
            const op_reg = uf.findDecl(op).reg_alloc_value.?;
            std.debug.assert(op_reg == registers.rax);
            try writer.writeInt(u8, 0xC3);
        },
        .phi => {},
        inline else => |_, tag| @panic("TODO: x86_64 decl " ++ @tagName(tag)),
    }
    return null;
}

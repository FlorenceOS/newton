const std = @import("std");

const backend = @import("backend.zig");
const ir = @import("ir.zig");
const rega = @import("rega.zig");

pub const Writer = backend.Writer(@This());

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

fn movReg64(writer: *Writer, dest_reg: u8, src_reg: u8) !void {
    if(dest_reg == src_reg) return;
    try writer.writeInt(u8, 0x48
        | @as(u8, @boolToInt(dest_reg >= 8)) << 0
        | @as(u8, @boolToInt(src_reg >= 8)) << 2
    );
    try writer.writeInt(u8, 0x89);
    try writer.writeInt(u8, 0xC0 | ((src_reg & 0x7) << 3) | (dest_reg & 0x7));
}

pub fn writeDecl(writer: *Writer, decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .stack_ref, .undefined => {},
        .enter_function => |stack_size| {
            if(stack_size > 0) {
                try writer.writeInt(u8, 0x55);
                try writer.writeInt(u8, 0x48);
                try writer.writeInt(u8, 0x81);
                try writer.writeInt(u8, 0xEC);
                try writer.writeInt(u32, stack_size);
            }
        },
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
        .sub => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try movReg64(writer, dest_reg, lhs_reg);
            try writer.writeInt(u8, 0x48
                | @as(u8, @boolToInt(dest_reg >= 8)) << 0
                | @as(u8, @boolToInt(rhs_reg >= 8)) << 2
            );
            try writer.writeInt(u8, 0x29);
            try writer.writeInt(u8, 0xC8 | (dest_reg & 0x7) | ((rhs_reg & 0x7) << 3));
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
        .sub_constant => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try movReg64(writer, dest_reg, lhs_reg);
            if(bop.rhs == 1) { // dec r64
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                try writer.writeInt(u8, 0xFF);
                try writer.writeInt(u8, 0xC8 | (dest_reg & 0x7));
            } else { // sub r64, imm32
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                try writer.writeInt(u8, 0x81);
                try writer.writeInt(u8, 0xE8 | (dest_reg & 0x7));
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
                const reloc_type = writer.pickSmallestRelocationType(edge, &.{.{1, .rel8_post_0}}) orelse .rel32_post_0;
                try writer.writeInt(u8, @as(u8, switch(reloc_type) {
                    .rel8_post_0 => 0xEB,
                    .rel32_post_0 => 0xE9,
                    else => unreachable,
                }));
                try writer.writeRelocatedValue(edge, reloc_type);
            }
        },
        .copy => |target| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const src_reg = uf.findDecl(target).reg_alloc_value.?;
            try movReg64(writer, dest_reg, src_reg);
        },
        .load_int_constant => |c| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            if(c == 0) {
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)) * 5);
                try writer.writeInt(u8, 0x31);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7) * 9);
            } else if(c <= 0x7F or c > 0xFFFFFFFFFFFFFF80) {
                try writer.writeInt(u8, 0x6A);
                try writer.writeInt(i8, @intCast(i8, c));
                if(dest_reg >= 8) {
                    try writer.writeInt(u8, 0x41);
                }
                try writer.writeInt(u8, 0x58 | (dest_reg & 0x7));
            } else if(c <= 0x7FFFFFFF or c > 0xFFFFFFFF80000000) {
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                try writer.writeInt(u8, 0xC7);
                try writer.writeInt(u8, 0xC0 | (dest_reg & 0x7));
                try writer.writeInt(u32, @intCast(u32, c));
            } else {
                try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)));
                try writer.writeInt(u8, 0xB8 | (dest_reg & 0x7));
                try writer.writeInt(u64, c);
            }
        },
        .store_constant => |bop| {
            const lhs = ir.decls.get(bop.lhs);
            switch(lhs.instr) {
                .stack_ref => |offset| {
                    if(bop.rhs <= 0x7F or bop.rhs > 0xFFFFFFFFFFFFFF80) {
                        // push imm8
                        try writer.writeInt(u8, 0x6A);
                        try writer.writeInt(i8, @intCast(i8, bop.rhs));
                        // pop [rbp - offset]
                        try writer.writeInt(u8, 0x8F);
                        try writer.writeInt(u8, 0x85);
                        try writer.writeInt(u32, ~offset + 1);
                    } else if(bop.rhs <= 0x7FFFFFFF or bop.rhs > 0xFFFFFFFF80000000) {
                        // mov [rbp - offset], imm32
                        try writer.writeInt(u8, 0x48);
                        try writer.writeInt(u8, 0xC7);
                        try writer.writeInt(u8, 0x85);
                        try writer.writeInt(u32, ~offset + 1);
                        try writer.writeInt(i32, @intCast(i32, bop.rhs));
                    } else {
                        @panic(":(");
                    }
                },
                else => {
                    const lhs_reg = uf.findDeclByPtr(lhs).reg_alloc_value.?;
                    if(bop.rhs <= 0x7F or bop.rhs > 0xFFFFFFFFFFFFFF80) {
                        try writer.writeInt(u8, 0x6A);
                        try writer.writeInt(i8, @intCast(i8, bop.rhs));
                        if(lhs_reg >= 8) {
                            try writer.writeInt(u8, 0x41);
                        }
                        try writer.writeInt(u8, 0x58 | (lhs_reg & 0x7));
                    } else if(bop.rhs <= 0x7FFFFFFF or bop.rhs > 0xFFFFFFFF80000000) {
                        try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(lhs_reg >= 8)));
                        try writer.writeInt(u8, 0xC7);
                        try writer.writeInt(u8, 0x00 | (lhs_reg & 0x7));
                        try writer.writeInt(i32, @intCast(i32, bop.rhs));
                    } else {
                        @panic(":(");
                    }
                },
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
            const taken_reloc_type = writer.pickSmallestRelocationType(op.taken, &.{.{2, .rel8_post_0}}) orelse .rel32_post_0;
            var not_taken_reloc_type = writer.pickSmallestRelocationType(op.not_taken, &.{.{2, .rel8_post_0}}) orelse .rel32_post_0;
            if(try writer.attemptInlineEdge(op.not_taken)) |bidx| {
                switch(taken_reloc_type) {
                    .rel8_post_0 => try writer.writeInt(u8, 0x70 | cond_flag),
                    .rel32_post_0 => {
                        try writer.writeInt(u8, 0x0F);
                        try writer.writeInt(u8, 0x80 | cond_flag);
                    },
                    else => unreachable,
                }
                try writer.writeRelocatedValue(op.taken, taken_reloc_type);
                return bidx;
            } else if(try writer.attemptInlineEdge(op.taken)) |bidx| {
                switch(not_taken_reloc_type) {
                    .rel8_post_0 => try writer.writeInt(u8, 0x70 | cond_flag ^ cond_flags.not),
                    .rel32_post_0 => {
                        try writer.writeInt(u8, 0x0F);
                        try writer.writeInt(u8, 0x80 | cond_flag ^ cond_flags.not);
                    },
                    else => unreachable,
                }
                try writer.writeRelocatedValue(op.not_taken, not_taken_reloc_type);
                return bidx;
            } else {
                switch(taken_reloc_type) {
                    .rel8_post_0 => try writer.writeInt(u8, 0x70 | cond_flag),
                    .rel32_post_0 => {
                        try writer.writeInt(u8, 0x0F);
                        try writer.writeInt(u8, 0x80 | cond_flag);
                    },
                    else => unreachable,
                }
                try writer.writeRelocatedValue(op.taken, taken_reloc_type);
                not_taken_reloc_type = writer.pickSmallestRelocationType(op.not_taken, &.{.{2, .rel8_post_0}}) orelse .rel32_post_0;
                try writer.writeInt(u8, @as(u8, switch(not_taken_reloc_type) {
                    .rel8_post_0 => 0xEB,
                    .rel32_post_0 => 0xE9,
                    else => unreachable,
                }));
                try writer.writeRelocatedValue(op.not_taken, not_taken_reloc_type);
            }
        },
        .@"return" => |ret| {
            const op_reg = uf.findDecl(ret.value).reg_alloc_value.?;
            std.debug.assert(op_reg == registers.rax);
            if(ret.restore_stack) {
                try writer.writeInt(u8, 0x48);
                try writer.writeInt(u8, 0x89);
                try writer.writeInt(u8, 0xEC);
                try writer.writeInt(u8, 0x5D);
            }
            try writer.writeInt(u8, 0xC3);
        },
        .store => |bop| {
            const lhs = ir.decls.get(bop.lhs);
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            switch(lhs.instr) {
                .stack_ref => |offset| {
                    try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(rhs_reg >= 8)) << 2);
                    try writer.writeInt(u8, 0x89);
                    try writer.writeInt(u8, 0x85 | ((rhs_reg & 0x7) << 3));
                    try writer.writeInt(u32, ~offset + 1);
                },
                else => {
                    const lhs_reg = uf.findDeclByPtr(lhs).reg_alloc_value.?;
                    try writer.writeInt(u8, 0x48
                        | @as(u8, @boolToInt(lhs_reg >= 8)) << 0
                        | @as(u8, @boolToInt(rhs_reg >= 8)) << 2
                    );
                    try writer.writeInt(u8, 0x89);
                    try writer.writeInt(u8, 0x00 | (lhs_reg & 0x7) | ((rhs_reg & 0x7) << 3));
                },
            }
        },
        .load => |idx| {
            const source = ir.decls.get(idx);
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            switch(source.instr) {
                .stack_ref => |offset| {
                    try writer.writeInt(u8, 0x48 | @as(u8, @boolToInt(dest_reg >= 8)) << 2);
                    try writer.writeInt(u8, 0x8B);
                    try writer.writeInt(u8, 0x85 | ((dest_reg & 0x7) << 3));
                    try writer.writeInt(u32, ~offset + 1);
                },
                else => {
                    const source_reg = uf.findDeclByPtr(source).reg_alloc_value.?;
                    try writer.writeInt(u8, 0x48
                        | @as(u8, @boolToInt(source_reg >= 8)) << 0
                        | @as(u8, @boolToInt(dest_reg >= 8)) << 2
                    );
                    try writer.writeInt(u8, 0x8B);
                    try writer.writeInt(u8, 0x00 | ((dest_reg & 0x7) << 3) | (source_reg & 0x7));
                },
            }
        },
        inline else => |_, tag| @panic("TODO: x86_64 decl " ++ @tagName(tag)),
    }
    return null;
}

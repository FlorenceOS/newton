const std = @import("std");

const backend = @import("backend.zig");
const ir = @import("ir.zig");
const rega = @import("rega.zig");

const Writer = backend.Writer(@This());

pub const registers = struct {
    pub const fp = 29;
    pub const lr = 30;
    pub const sp = 31;
    pub const zero = 31;

    pub const return_reg = 0;
    pub const gprs = [_]u8{
        0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
        10, 11, 12, 13, 14, 15, 16, 17,     19,
        20, 21, 22, 23, 24, 25, 26, 27, 28,
    };
    pub const param_regs = [_]u8{0, 1, 2, 3, 4, 5, 6, 7};
    pub const caller_saved = [_]u8{
            1,  2,  3,  4,  5,  6,  7,  8,  9,
        10, 11, 12, 13, 14, 15,
    };
};

const cond_flags = struct {
    const not = 1;

    const zero = 0;
    const carry = 2;
    const negative = 4;
    const overflow = 6;
    const higher = 8;
};

const MovType = enum { movn, movz, movk };

fn emulateMov(movs: []const std.meta.Tuple(&.{u16, u2, MovType})) u64 {
    var result: u64 = 0;
    for(movs) |mov| {
        const shift = @as(u6, mov[1]) * 16;
        const shifted_value = @as(u64, mov[0]) << shift;
        const mask = @as(u64, 0xFFFF) << shift;
        switch(mov[2]) {
            .movz => result = shifted_value,
            .movn => result = (result & ~mask) | shifted_value | ~mask,
            .movk => result = (result & ~mask) | shifted_value,
        }
    }
    return result;
}

fn movReg(writer: *Writer, dest_reg: u8, src_reg: u8) !void {
    if(dest_reg == src_reg) return;
    return writer.writeInt(u32, 0xAA000000
        | @as(u32, dest_reg)
        | @as(u32, src_reg) << 5
        | @as(u32, registers.zero) << 16
    );
}

pub fn writeDecl(writer: *Writer, decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .undefined => {},
        .load_int_constant => |value| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const mov_ops: [4]std.meta.Tuple(&.{u16, u2, MovType}) = .{
                .{@truncate(u16, value >> 0),  0b00, .movz},
                .{@truncate(u16, value >> 16), 0b01, .movk},
                .{@truncate(u16, value >> 32), 0b10, .movk},
                .{@truncate(u16, value >> 48), 0b11, .movk},
            };
            comptime var len = 0;
            inline while(len < 4) : (len += 1) {
                if(emulateMov(mov_ops[0..len + 1]) == value) {
                    for(mov_ops[0..len + 1]) |mov| {
                        const base_opcode: u32 = switch(mov[2]) {
                            .movn => 0x92800000,
                            .movz => 0xD2800000,
                            .movk => 0xF2800000,
                        };
                        try writer.writeInt(u32, base_opcode
                            | @as(u32, dest_reg)
                            | @as(u32, mov[0]) << 5
                            | @as(u32, mov[1]) << 21
                        );
                    }
                    return null;
                }
            }
            unreachable;
        },
        .copy => |target| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const src_reg = uf.findDecl(target).reg_alloc_value.?;
            try movReg(writer, dest_reg, src_reg);
        },
        .goto => |edge| {
            if(try writer.attemptInlineEdge(edge)) |bidx| {
                return bidx;
            }
            try writer.writeIntWithRelocation(u32, 0x14000000, edge, .imm26_div4);
        },
        .add, .sub, .divide, .shift_left, .shift_right => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            const base_opcode: u32 = switch(decl.instr) {
                .add => 0x8B000000,
                .sub => 0xCB000000,
                .divide => 0x9AC00800,
                .shift_left => 0x9AC02000,
                .shift_right => 0x9AC02400,
                else => unreachable,
            };
            try writer.writeInt(u32, base_opcode
                | @as(u32, dest_reg)
                | @as(u32, lhs_reg) << 5
                | @as(u32, rhs_reg) << 16
            );
        },
        .add_constant => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try writer.writeInt(u32, 0x91000000
                | @as(u32, dest_reg)
                | @as(u32, lhs_reg) << 5
                | @as(u32, @intCast(u12, bop.rhs)) << 10
            );
        },
        .multiply => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try writer.writeInt(u32, 0x9B000000
                | @as(u32, dest_reg)
                | @as(u32, lhs_reg) << 5
                | @as(u32, registers.zero) << 10
                | @as(u32, rhs_reg) << 16
            );
        },
        .less, .less_equal, .equals, .not_equal => |bop| {
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try writer.writeInt(u32, 0xEB000000
                | @as(u32, registers.zero)
                | @as(u32, lhs_reg) << 5
                | @as(u32, rhs_reg) << 16
            );
        },
        .@"if" => |if_instr| {
            const op_instr = ir.decls.get(if_instr.condition).instr;
            const cond_flag: u32 = switch(op_instr) {
                .less, .less_constant, => cond_flags.not | cond_flags.carry,
                .less_equal, .less_equal_constant => cond_flags.not | cond_flags.higher,
                .greater_constant => cond_flags.higher,
                .greater_equal_constant => cond_flags.carry,
                .equals, .equals_constant => cond_flags.zero,
                .not_equal, .not_equal_constant => cond_flags.not | cond_flags.zero,
                else => unreachable,
            };

            if(try writer.attemptInlineEdge(if_instr.not_taken)) |bidx| {
                try writer.writeIntWithRelocation(u32, 0x54000000 | cond_flag, if_instr.taken, .imm19_div4_shift5);
                return bidx;
            } else if(try writer.attemptInlineEdge(if_instr.taken)) |bidx| {
                try writer.writeIntWithRelocation(u32, 0x54000000 | cond_flag ^ cond_flags.not, if_instr.not_taken, .imm19_div4_shift5);
                return bidx;
            } else {
                try writer.writeIntWithRelocation(u32, 0x54000000 | cond_flag, if_instr.taken, .imm19_div4_shift5);
                try writer.writeIntWithRelocation(u32, 0x14000000, if_instr.not_taken, .imm26_div4);
            }
        },
        .@"return" => |op| {
            const op_reg = uf.findDecl(op).reg_alloc_value.?;
            std.debug.assert(op_reg == registers.return_reg);
            try writer.writeInt(u32, 0xD65F0000 | @as(u32, registers.lr) << 5);
        },
        inline else => |_, tag| @panic("TODO: aarch64 decl " ++ @tagName(tag)),
    }
    return null;
}

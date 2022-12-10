const std = @import("std");

const backends = @import("backends.zig");
const ir = @import("../ir.zig");
const rega = @import("../rega.zig");

fn registerName(reg: u8) []const u8 {
    switch(reg) {
        inline else => |regnum| {
            return std.fmt.comptimePrint("X{d}", .{regnum});
        },
    }
}

fn determineMaxMemoryOperands(_: *const ir.Decl) usize {
    return 0;
}

pub const backend = backends.Backend{
    .elf_machine = .AARCH64,
    .pointer_type = .u64,
    .register_name = registerName,
    .reg_alloc = regAlloc,
    .write_decl = writeDecl,
    .optimizations = .{
        .has_nonzero_constant_store = false,
        .has_divide_constant = false,
        .has_modulus_constant = false,
        .max_memory_operands_fn = determineMaxMemoryOperands,
    },
    .gprs = &.{
        0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
        10, 11, 12, 13, 14, 15, 16, 17,     19,
        20, 21, 22, 23, 24, 25, 26, 27, 28,
    },
};

pub const abis = struct {
    pub const aarch64 = backends.Abi{
        .return_reg = 0,
        .param_regs = &.{0, 1, 2, 3, 4, 5, 6, 7},
        .caller_saved_regs = &.{
            0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
            10, 11, 12, 13, 14, 15,
        },
    };
};

pub const oses = struct {
    pub const linux = backends.Os{
        .default_abi = &abis.aarch64,
        .syscall_return_reg = 0,
        .syscall_param_regs = &.{8, 0, 1, 2, 3, 4, 5},
        .syscall_clobbers = &.{},
    };
};

pub const registers = struct {
    pub const fp = 29;
    pub const lr = 30;
    pub const sp = 31;
    pub const zero = 31;
};

pub const pointer_type: ir.InstrType = .u64;

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

fn movReg(writer: *backends.Writer, dest_reg: u8, src_reg: u8) !void {
    if(dest_reg == src_reg) return;
    return writer.writeInt(u32, 0xAA000000
        | @as(u32, dest_reg)
        | @as(u32, src_reg) << 5
        | @as(u32, registers.zero) << 16
    );
}

fn addImm(writer: *backends.Writer, dest_reg: u8, src_reg: u8, imm: u12) !void {
    try writer.writeInt(u32, 0x91000000
        | @as(u32, dest_reg)
        | @as(u32, src_reg) << 5
        | @as(u32, imm) << 10
    );
}

fn subImm(writer: *backends.Writer, dest_reg: u8, src_reg: u8, imm: u12) !void {
    try writer.writeInt(u32, 0xD1000000
        | @as(u32, dest_reg)
        | @as(u32, src_reg) << 5
        | @as(u32, imm) << 10
    );
}

fn ldpPost(writer: *backends.Writer, ptr_reg: u8, r1: u8, r2: u8, imm: i7) !void {
    try writer.writeInt(u32, 0xA8C00000
        | @as(u32, ptr_reg) << 5
        | @as(u32, r1) << 0
        | @as(u32, r2) << 10
        | @as(u32, @bitCast(u7, imm)) << 15
    );
}

fn stpPre(writer: *backends.Writer, ptr_reg: u8, r1: u8, r2: u8, imm: i7) !void {
    try writer.writeInt(u32, 0xA9800000
        | @as(u32, ptr_reg) << 5
        | @as(u32, r1) << 0
        | @as(u32, r2) << 10
        | @as(u32, @bitCast(u7, imm)) << 15
    );
}

fn pushTwo(writer: *backends.Writer, r1: u8, r2: u8) !void {
    return stpPre(writer, registers.sp, r1, r2, -2);
}

fn popTwo(writer: *backends.Writer, r1: u8, r2: u8) !void {
    return ldpPost(writer, registers.sp, r1, r2, 2);
}

fn opSizeBit(decl: *ir.Decl) u32 {
    return if(decl.instr.getOperationType() == .u64) (1 << 31) else 0;
}

fn regAlloc(decl_idx: ir.DeclIndex.Index, param_replacement: *rega.ParamReplacement) !void {
    try rega.allocateRegsForInstr(decl_idx, 0, null, &.{}, &.{}, &.{}, true, param_replacement);
}

fn writeDecl(writer: *backends.Writer, decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind, regs_to_save: []const u8) !?ir.BlockIndex.Index {
    std.debug.assert(regs_to_save.len == 0);
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .undefined, .clobber, .offset_ref, .stack_ref, .reference_wrap,
        => {},
        .load_int_constant => |value| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const mov_ops: [4]std.meta.Tuple(&.{u16, u2, MovType}) = .{
                .{@truncate(u16, value.value >> 0),  0b00, .movz},
                .{@truncate(u16, value.value >> 16), 0b01, .movk},
                .{@truncate(u16, value.value >> 32), 0b10, .movk},
                .{@truncate(u16, value.value >> 48), 0b11, .movk},
            };
            comptime var len = 0;
            inline while(len < 4) : (len += 1) {
                if(emulateMov(mov_ops[0..len + 1]) == value.value) {
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
        .load => |l| {
            const opcode: u32 = switch(decl.instr.getOperationType()) {
                .u8 =>  0x38400000,
                .u16 => 0x78400000,
                .u32 => 0xB8400000,
                .u64 => 0xF8400000,
            };

            try writer.writeInt(u32, opcode
                | @as(u32, uf.findRegByPtr(decl).?) << 0
                | @as(u32, uf.findReg(l.source).?) << 5
            );
        },
        .store => |s| {
            const opcode: u32 = switch(decl.instr.getOperationType()) {
                .u8 =>  0x38000000,
                .u16 => 0x78000000,
                .u32 => 0xB8000000,
                .u64 => 0xF8000000,
            };

            try writer.writeInt(u32, opcode
                | @as(u32, uf.findReg(s.value).?) << 0
                | @as(u32, uf.findReg(s.dest).?) << 5
            );
        },
        .store_constant => |s| {
            const opcode: u32 = switch(decl.instr.getOperationType()) {
                .u8 =>  0x38000000,
                .u16 => 0x78000000,
                .u32 => 0xB8000000,
                .u64 => 0xF8000000,
            };

            try writer.writeInt(u32, opcode
                | @as(u32, registers.zero) << 0
                | @as(u32, uf.findReg(s.dest).?) << 5
            );
        },
        .addr_of => |op| {
            const operand = ir.decls.get(op);
            switch(operand.instr) {
                .offset_ref => |offref| {
                    const disp = @bitCast(u21, @intCast(i21, @bitCast(i64, offref.offset -% writer.currentOffset())));
                    try writer.writeInt(u32, 0x10000000
                        | @as(u32, uf.findRegByPtr(decl).?) << 0
                        | @as(u32, disp >> 2) << 5
                        | @as(u32, @truncate(u2, disp)) << 29
                    );
                },
                .stack_ref => |stackoff| try subImm(writer, uf.findRegByPtr(decl).?, registers.fp, @intCast(u12, stackoff.offset)),
                else => |other| std.debug.panic("aarch64: TODO addr_of {s}", .{@tagName(other)}),
            }
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
            const base_opcode = opSizeBit(decl) | @as(u32, switch(decl.instr) {
                .add => 0x0B000000,
                .sub => 0x4B000000,
                .divide => 0x1AC00800,
                .shift_left => 0x1AC02000,
                .shift_right => 0x1AC02400,
                else => unreachable,
            });
            try writer.writeInt(u32, base_opcode
                | @as(u32, dest_reg)
                | @as(u32, lhs_reg) << 5
                | @as(u32, rhs_reg) << 16
            );
        },
        .add_constant => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try addImm(writer, dest_reg, lhs_reg, @intCast(u12, bop.rhs));
        },
        .sub_constant => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try subImm(writer, dest_reg, lhs_reg, @intCast(u12, bop.rhs));
        },
        .multiply => |bop| {
            const dest_reg = uf.findDeclByPtr(decl).reg_alloc_value.?;
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try writer.writeInt(u32, opSizeBit(decl) | 0x1B000000
                | @as(u32, dest_reg)
                | @as(u32, lhs_reg) << 5
                | @as(u32, registers.zero) << 10
                | @as(u32, rhs_reg) << 16
            );
        },
        .less, .less_equal, .equals, .not_equal => |bop| {
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            const rhs_reg = uf.findDecl(bop.rhs).reg_alloc_value.?;
            try writer.writeInt(u32, opSizeBit(decl) | 0x6B000000
                | @as(u32, registers.zero)
                | @as(u32, lhs_reg) << 5
                | @as(u32, rhs_reg) << 16
            );
        },
        .less_constant, .less_equal_constant, .equals_constant, .not_equal_constant => |bop| {
            const lhs_reg = uf.findDecl(bop.lhs).reg_alloc_value.?;
            try writer.writeInt(u32, opSizeBit(decl) | 0x71000000
                | @as(u32, registers.zero)
                | @as(u32, lhs_reg) << 5
                | @as(u32, @intCast(u12, bop.rhs)) << 10
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
        .enter_function => |stack_size| {
            try pushTwo(writer, registers.fp, registers.lr);
            if(stack_size > 0) {
                try subImm(writer, registers.sp, registers.sp, @intCast(u12, stack_size));
            }
        },
        .function_call => |fcall| {
            try writer.writeIntWithFunctionRelocation(u32, 0x94000000, fcall.callee, .imm26_div4);
        },
        .syscall => try writer.writeInt(u32, 0xD4000001),
        .leave_function => |leave| {
            const op_reg = uf.findDecl(leave.value).reg_alloc_value.?;
            std.debug.assert(op_reg == backends.current_default_abi.return_reg);
            if(leave.restore_stack) {
                try movReg(writer, registers.sp, registers.fp);
            }
            try popTwo(writer, registers.fp, registers.lr);
            try writer.writeInt(u32, 0xD65F0000 | @as(u32, registers.lr) << 5);
        },
        inline else => |_, tag| @panic("TODO: aarch64 decl " ++ @tagName(tag)),
    }
    return null;
}

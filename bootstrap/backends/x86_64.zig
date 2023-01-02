const std = @import("std");

const backends = @import("backends.zig");
const ir = @import("../ir.zig");
const rega = @import("../rega.zig");

const registers = struct {
    const rax = 0;
    const rcx = 1;
    const rdx = 2;
    const rbx = 3;
    const rsp = 4;
    const rbp = 5;
    const rsi = 6;
    const rdi = 7;
};

pub const backend = backends.Backend{
    .elf_machine = .X86_64,
    .pointer_type = .u64,
    .register_name = registerName,
    .reg_alloc = regAlloc,
    .write_decl = writeDecl,
    .optimizations = .{
        .has_nonzero_constant_store = true,
        .has_divide_constant = false,
        .has_modulus_constant = false,
        .has_inplace_ops = true,
    },
    .gprs = &.{
        registers.rax,
        registers.rcx,
        registers.rdx,
        registers.rsi,
        registers.rdi,
        8, 9, 10, 11,
        registers.rbx,
        13, 14, 15, 12,
    },
};

pub const abis = struct {
    pub const sysv = backends.Abi{
        .return_reg = registers.rax,
        .param_regs = &.{registers.rdi, registers.rsi, registers.rdx, registers.rcx, 8, 9},
        .caller_saved_regs = &.{registers.rax, registers.rdi, registers.rsi, registers.rdx, registers.rcx, 8, 9, 10, 11},
    };
};

pub const oses = struct {
    pub const linux = backends.Os{
        .default_abi = &abis.sysv,
        .syscall_return_reg = registers.rax,
        .syscall_param_regs = &.{registers.rax, registers.rdi, registers.rsi, registers.rdx, 10, 8, 9},
        .syscall_clobbers =   &.{registers.rcx, 11},
    };
};

fn registerName(reg: u8) []const u8 {
    return switch(reg) {
        registers.rax => "rax",
        registers.rcx => "rcx",
        registers.rdx => "rdx",
        registers.rbx => "rbx",
        registers.rsp => "rsp",
        registers.rbp => "rbp",
        registers.rsi => "rsi",
        registers.rdi => "rdi",
        inline else => |r| if(r >= 8 and r <= 15) std.fmt.comptimePrint("r{d}", .{r}) else unreachable,
    };
}

const cond_flags = struct {
    const not = 1;

    const below = 2;       // Less than unsigned
    const zero = 4;        // Also equal
    const below_equal = 6; // Less than unsigned or equal
};

fn rexPrefix(writer: *backends.Writer, w: bool, r: bool, x: bool, b: bool, force: bool) !void {
    var result: u8 = 0;
    if(w) result |= 1 << 3;
    if(r) result |= 1 << 2;
    if(x) result |= 1 << 1;
    if(b) result |= 1 << 0;
    if(force or result != 0) {
        try writer.writeInt(u8, 0x40 | result);
    }
}

const PrefixBits = struct {
    op_size: bool,
    force_rex: bool,
    rex_w: bool,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,

    fn fromOp(operation_type: ir.InstrType, rm: u8, reg: u8, rm_reg_is_reg: bool) @This() {
        return .{
            .op_size = operation_type == .u16,
            .force_rex = operation_type == .u8 and (rm >= 4 or (rm_reg_is_reg and reg >= 4)),
            .rex_w = operation_type == .u64,
            .rex_r = reg >= 8,
            .rex_x = false,
            .rex_b = rm >= 8,
        };
    }

    fn prefixBytes(self: @This()) usize {
        return @as(usize, @boolToInt(self.op_size)) + @boolToInt(self.rex_w or self.rex_r or self.rex_x or self.rex_b or self.force_rex);
    }

    fn write(self: @This(), writer: *backends.Writer) !void {
        if(self.op_size) {
            try writer.writeInt(u8, 0x66);
        }
        try rexPrefix(writer, self.rex_w, self.rex_r, self.rex_x, self.rex_b, self.force_rex);
    }
};

fn opTypeImm(op_t: ir.InstrType, value: []const u8) []const u8 {
    return value[0..switch(op_t) {
        .u8 => 1,
        .u16 => 2,
        .u32, .u64 => 4,
    }];
}

fn boolToU8(val: bool) u8 {
    return @boolToInt(val);
}

fn writeInstr(
    writer: *backends.Writer,
    prefix_bits: PrefixBits,
    opcodes: []const u8,
    rm_type: u2,
    rm_rm_field: u3,
    rm_reg_field: u3,
    rm_immediate: []const u8,
    immediate: []const u8,
) !void {
    try prefix_bits.write(writer);
    try writer.write(opcodes);
    try writer.writeInt(u8, (@as(u8, rm_type) << 6) | (@as(u8, rm_reg_field) << 3) | @as(u8, rm_rm_field));
    try writer.write(rm_immediate);
    try writer.write(immediate);
}

fn writeDirect(
    writer: *backends.Writer,
    op_t: ir.InstrType,
    opcodes: []const u8,
    rm_reg: u8,
    reg: u8,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    const prefixes = PrefixBits.fromOp(op_t, rm_reg, reg, rm_reg_is_reg);
    return writeInstr(writer, prefixes, opcodes, 0b11, @truncate(u3, rm_reg), @truncate(u3, reg), &.{}, immediate);
}

fn writeRegIndirect(
    writer: *backends.Writer,
    op_t: ir.InstrType,
    opcodes: []const u8,
    rm_reg: u8,
    reg: u8,
    offset: i32,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    const prefixes = PrefixBits.fromOp(op_t, rm_reg, reg, rm_reg_is_reg);
    std.debug.assert(rm_reg != registers.rsp and rm_reg != 12); // SP and R12 uses SIB+DISP8
    if(offset == 0 and rm_reg != registers.rbp and rm_reg != 13) {
        return writeInstr(writer, prefixes, opcodes, 0b00, @truncate(u3, rm_reg), @truncate(u3, reg), &.{}, immediate);
    } else if(std.math.cast(i8, offset)) |i8_offset| {
        return writeInstr(writer, prefixes, opcodes, 0b01, @truncate(u3, rm_reg), @truncate(u3, reg), std.mem.asBytes(&i8_offset), immediate);
    } else {
        return writeInstr(writer, prefixes, opcodes, 0b10, @truncate(u3, rm_reg), @truncate(u3, reg), std.mem.asBytes(&offset), immediate);
    }
}

fn writeRipRelative(
    writer: *backends.Writer,
    op_t: ir.InstrType,
    opcodes: []const u8,
    reg: u8,
    offset: usize,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    const prefixes = PrefixBits.fromOp(op_t, registers.rbp, reg, rm_reg_is_reg);
    const instr_len = prefixes.prefixBytes() + opcodes.len + 5 + immediate.len;
    const disp = @intCast(i32, @bitCast(i64, offset -% (writer.currentOffset() + instr_len)));
    return writeInstr(writer, prefixes, opcodes, 0b00, registers.rbp, @truncate(u3, reg), std.mem.asBytes(&disp), immediate);
}

fn writeStackOffset(
    writer: *backends.Writer,
    op_t: ir.InstrType,
    opcodes: []const u8,
    reg: u8,
    stack_offset: i32,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    try writeRegIndirect(writer, op_t, opcodes, registers.rbp, reg, -stack_offset, immediate, rm_reg_is_reg);
}

fn writeOperandReg(
    writer: *backends.Writer,
    uf: rega.UnionFind,
    op_t: ir.InstrType,
    rm_operand: ir.DeclIndex.Index,
    reg: u8,
    opcodes: []const u8,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    const rm_decl = ir.decls.get(rm_operand);
    if(rm_decl.instr.memoryReference()) |mr| {
        switch(rm_decl.instr) {
            .global_ref => |offset| return writeRipRelative(writer, op_t, opcodes, reg, offset.offset, immediate, rm_reg_is_reg),
            .stack_ref => |offset| return writeStackOffset(writer, op_t, opcodes, reg, @intCast(i32, offset.offset), immediate, rm_reg_is_reg),
            .reference_wrap => return writeRegIndirect(writer, op_t, opcodes, uf.findReg(mr.pointer_value).?, reg, mr.pointer_value_offset, immediate, rm_reg_is_reg),
            else => unreachable,
        }
    } else {
        return writeDirect(writer, op_t, opcodes, uf.findRegByPtr(rm_decl).?, reg, immediate, rm_reg_is_reg);
    }
}

fn writeWithOperands(
    writer: *backends.Writer,
    uf: rega.UnionFind,
    op_t: ir.InstrType,
    rm_operand: ir.DeclIndex.Index,
    reg_operand: ir.DeclIndex.Index,
    opcodes: []const u8,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    return writeOperandReg(writer, uf, op_t, rm_operand, uf.findReg(reg_operand).?, opcodes, immediate, rm_reg_is_reg);
}

fn writeEitherOperandRm(
    writer: *backends.Writer,
    uf: rega.UnionFind,
    op_t: ir.InstrType,
    lhs_operand: ir.DeclIndex.Index,
    rhs_operand: ir.DeclIndex.Index,
    opcodes_lhs_rm: []const u8,
    opcodes_rhs_rm: []const u8,
    immediate: []const u8,
    rm_reg_is_reg: bool,
) !void {
    const lhs = ir.decls.get(lhs_operand);
    if(lhs.instr.memoryReference() != null) {
        return writeWithOperands(writer, uf, op_t, lhs_operand, rhs_operand, opcodes_lhs_rm, immediate, rm_reg_is_reg);
    } else {
        return writeWithOperands(writer, uf, op_t, rhs_operand, lhs_operand, opcodes_rhs_rm, immediate, rm_reg_is_reg);
    }
}

fn mov(
    writer: *backends.Writer,
    uf: rega.UnionFind,
    op_t: ir.InstrType,
    lhs: ir.DeclIndex.Index,
    rhs: ir.DeclIndex.Index,
    noop_if_same_reg: bool,
) !void {
    if(noop_if_same_reg) blk: {
        if((uf.findReg(lhs) orelse break :blk) == (uf.findReg(rhs) orelse break :blk)) {
            return;
        }
    }
    return writeEitherOperandRm(writer, uf, op_t, lhs, rhs,
        &.{0x88 | boolToU8(op_t != .u8)},
        &.{0x8A | boolToU8(op_t != .u8)},
        &.{},
        true,
    );
}

fn pushReg(writer: *backends.Writer, reg: u8) !void {
    try rexPrefix(writer, false, false, false, reg >= 8, false);
    try writer.writeInt(u8, 0x50 | (reg & 0x7));
}

fn pushImm(writer: *backends.Writer, value: i32) !void {
    if(std.math.cast(i8, value)) |i8_value| {
        try writer.writeInt(u8, 0x6A);
        try writer.writeInt(i8, i8_value);
    } else {
        try writer.writeInt(u8, 0x68);
        try writer.writeInt(i32, value);
    }
}

fn popReg(writer: *backends.Writer, reg: u8) !void {
    try rexPrefix(writer, false, false, false, reg >= 8, false);
    try writer.writeInt(u8, 0x58 | (reg & 0x7));
}

fn movRegReg(writer: *backends.Writer, op_t: ir.InstrType, dest_reg: u8, src_reg: u8) !void {
    return writeDirect(writer, op_t, &.{0x88 | boolToU8(op_t != .u8)}, dest_reg, src_reg, &.{}, true);
}

fn movImmToReg(writer: *backends.Writer, op_t: ir.InstrType, dest_reg: u8, value: u64) !void {
    if(value == 0) {
        try writeDirect(writer, .u32, &.{0x31}, dest_reg, dest_reg, &.{}, true);
    } else if(std.math.cast(i8, value)) |i8_value| {
        try pushImm(writer, i8_value);
        try popReg(writer, dest_reg);
    } else if(std.math.cast(i32, value)) |i32_value| {
        try writeDirect(writer, op_t, &.{0xC6 | boolToU8(op_t != .u8)}, dest_reg, 0, std.mem.asBytes(&i32_value), false);
    } else {
        @panic("TODO");
    }
}

fn subImm(writer: *backends.Writer, op_t: ir.InstrType, dest_reg: u8, value: i32) !void {
    if(value == 1) { // dec r/mN
        return writeDirect(writer, op_t, &.{0xFE | boolToU8(op_t != .u8)}, dest_reg, 1, &.{}, false);
    } else {
        if(std.math.cast(i8, value)) |i8_value| { // sub r/mN, imm8
            return writeDirect(writer, op_t, &.{0x83}, dest_reg, 5, std.mem.asBytes(&i8_value), false);
        }
        if(op_t == .u16) {
            if(std.math.cast(i16, value)) |i16_value| { // sub r/mN, imm16
                return writeDirect(writer, op_t, &.{0x81}, dest_reg, 5, std.mem.asBytes(&i16_value), false);
            }
        }
        return writeDirect(writer, op_t, &.{0x81}, dest_reg, 5, std.mem.asBytes(&value), false);
    }
}

fn regAlloc(decl_idx: ir.DeclIndex.Index, param_replacement: *rega.ParamReplacement) !void {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .multiply,
        => try rega.allocateRegsForInstr(
            decl_idx, 1, registers.rax, &.{registers.rax}, &.{registers.rdx}, &.{}, true, param_replacement
        ),
        .divide,
        => try rega.allocateRegsForInstr(
            decl_idx, 1, registers.rax, &.{registers.rax}, &.{registers.rax}, &.{registers.rdx}, true, param_replacement
        ),
        .modulus,
        => try rega.allocateRegsForInstr(
            decl_idx, 1, registers.rdx, &.{registers.rax}, &.{registers.rax}, &.{registers.rdx}, true, param_replacement
        ),
        .add_constant, .sub_constant, .multiply_constant, .divide_constant, .modulus_constant,
        .shift_left_constant, .shift_right_constant,
        .bit_and_constant, .bit_or_constant, .bit_xor_constant,
        => try rega.allocateRegsForInstr(decl_idx, 0, null, &.{}, &.{}, &.{}, true, param_replacement),
        .reference_wrap => try rega.allocateRegsForInstr(decl_idx, 0, null, &.{}, &.{}, &.{}, true, param_replacement),
        else => try rega.allocateRegsForInstr(decl_idx, 1, null, &.{}, &.{}, &.{}, true, param_replacement),
    }
}

fn writeLeaveFunction(writer: *backends.Writer, used_registers: []const u8, leave: std.meta.TagPayload(ir.DeclInstr, .leave_function)) !void {
    if(leave.restore_stack) {
        try movRegReg(writer, .u64, registers.rsp, registers.rbp);
        try popReg(writer, registers.rbp);
    }
    var it = used_registers.len;
    while(it > 0) {
        it -= 1;
        if(std.mem.indexOfScalar(u8, backends.current_default_abi.caller_saved_regs, used_registers[it]) == null) {
            try popReg(writer, used_registers[it]);
        }
    }
}

fn writeDecl(writer: *backends.Writer, decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind, used_registers: []const u8) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .stack_ref, .undefined, .clobber, .global_ref, .reference_wrap,
        => {},
        .enter_function => |stack_size| {
            for(used_registers) |reg| {
                if(std.mem.indexOfScalar(u8, backends.current_default_abi.caller_saved_regs, reg) == null) {
                    try pushReg(writer, reg);
                }
            }
            if(stack_size > 0) {
                try pushReg(writer, registers.rbp);
                try movRegReg(writer, .u64, registers.rbp, registers.rsp);
                try subImm(writer, .u64, registers.rsp, @intCast(i32, stack_size));
            }
        },
        .leave_function => |leave| {
            const op_reg = uf.findReg(leave.value).?;
            std.debug.assert(op_reg == backends.current_default_abi.return_reg);
            try writeLeaveFunction(writer, used_registers, leave);
            try writer.writeInt(u8, 0xC3);
        },
        .copy => |source| try mov(writer, uf, decl.instr.getOperationType(), decl_idx, source, true),
        .truncate => |t| try mov(writer, uf, t.type, decl_idx, t.value, true),
        .zero_extend => |zext| {
            const dest_type = decl.instr.getOperationType();
            const src_type = ir.decls.get(zext.value).instr.getOperationType();

            if(dest_type == .u64 and src_type == .u32) {
                try mov(writer, uf, .u32, decl_idx, zext.value, true);
            } else {
                // movzx rM r/mN
                try writeWithOperands(writer, uf, dest_type, zext.value, decl_idx, &.{
                    0x0F, 0xB6 | boolToU8(src_type != .u8)
                }, &.{}, true);
            }
        },
        .load_int_constant => |constant| try movImmToReg(
            writer,
            constant.type,
            uf.findRegByPtr(decl).?,
            constant.value,
        ),
        .load_bool_constant => |constant| try movImmToReg(
            writer,
            .u8,
            uf.findRegByPtr(decl).?,
            @boolToInt(constant),
        ),
        .add => |op| {
            const op_t = decl.instr.getOperationType();
            const dest_reg = uf.findRegByPtr(decl).?;
            const lhs_reg = uf.findReg(op.lhs);
            const rhs_reg = uf.findReg(op.rhs);

            if(dest_reg == lhs_reg and ir.decls.get(op.lhs).instr.memoryReference() == null) {
                try writeOperandReg(writer, uf, op_t, op.rhs, dest_reg, &.{0x02 | boolToU8(op_t != .u8)}, &.{}, true);
            } else if(dest_reg == rhs_reg and ir.decls.get(op.rhs).instr.memoryReference() == null) {
                try writeOperandReg(writer, uf, op_t, op.lhs, dest_reg, &.{0x02 | boolToU8(op_t != .u8)}, &.{}, true);
            } else if(ir.decls.get(op.lhs).instr.memoryReference() != null) {
                try mov(writer, uf, op_t, decl_idx, op.lhs, false);
                try writeOperandReg(writer, uf, op_t, op.rhs, dest_reg, &.{0x02 | boolToU8(op_t != .u8)}, &.{}, true);
            } else if(ir.decls.get(op.rhs).instr.memoryReference() != null) {
                try mov(writer, uf, op_t, decl_idx, op.rhs, false);
                try writeOperandReg(writer, uf, op_t, op.lhs, dest_reg, &.{0x02 | boolToU8(op_t != .u8)}, &.{}, true);
            } else { // lea
                // TODO: Replace when we support SIB byte memes
                try writer.writeInt(u8, 0x48
                    | boolToU8(lhs_reg.? >= 8) << 0
                    | boolToU8(rhs_reg.? >= 8) << 1
                    | boolToU8(dest_reg >= 8) << 2
                );
                try writer.writeInt(u8, 0x8D);
                try writer.writeInt(u8, ((dest_reg & 0x7) << 3) | 4);
                try writer.writeInt(u8, ((rhs_reg.? & 0x7) << 3) | (lhs_reg.? & 0x7));
            }
        },
        .sub => |op| {
            const op_t = decl.instr.getOperationType();
            const dest_reg = uf.findRegByPtr(decl).?;
            const lhs_reg = uf.findReg(op.lhs);
            const rhs_reg = uf.findReg(op.rhs);

            if(dest_reg == lhs_reg) {
                try writeOperandReg(writer, uf, op_t, op.rhs, dest_reg, &.{0x2A | boolToU8(op_t != .u8)}, &.{}, true);
            } else if(dest_reg == rhs_reg) {
                @panic("TODO: Sub into rhs");
            } else {
                @panic("TODO: Sub no common regs");
            }
        },
        .divide, .modulus => |op| {
            std.debug.assert(uf.findReg(op.lhs).? == registers.rax);
            const op_t = decl.instr.getOperationType();
            if(op_t != .u8) {
                try movImmToReg(writer, op_t, registers.rdx, 0);
            }
            try writeOperandReg(writer, uf, op_t, op.rhs, 6, &.{0xF6 | boolToU8(op_t != .u8)}, &.{}, false);
        },
        .inplace_add => |op| {
            const op_t = decl.instr.getOperationType();
            const rhs_reg = uf.findReg(op.rhs).?;
            try writeOperandReg(writer, uf, op_t, op.lhs, rhs_reg, &.{0x00 | boolToU8(op_t != .u8)}, &.{}, true);
        },
        .add_constant => |op| {
            const dest_reg = uf.findRegByPtr(decl).?;
            const lhs_reg = uf.findReg(op.lhs);
            const op_t = decl.instr.getOperationType();
            const imm = std.mem.asBytes(&op.rhs);
            if(dest_reg == lhs_reg) {
                if(op.rhs == 1) { // inc r/m64
                    try writeDirect(writer, op_t, &.{0xFE | boolToU8(op_t != .u8)}, dest_reg, 0, &.{}, false);
                } else { // add r/m64, imm8/16/32
                    try writeOperandReg(writer, uf, op_t, decl_idx, 0, &.{
                        0x80 | boolToU8(op_t != .u8),
                    }, opTypeImm(op_t, imm), false);
                }
            } else if(op_t != .u8) { // lea r/m64, [r + disp32]
                if(lhs_reg) |reg| {
                    try writeRegIndirect(writer, op_t, &.{0x8D}, reg, dest_reg, @intCast(i32, @bitCast(i64, op.rhs)), &.{}, true);
                } else {
                    try mov(writer, uf, op_t, decl_idx, op.lhs, false);
                    try writeOperandReg(writer, uf, op_t, decl_idx, 0, &.{
                        0x80 | boolToU8(op_t != .u8),
                    }, opTypeImm(op_t, imm), false);
                }
            } else {
                @panic("TODO");
            }
        },
        .sub_constant => |op| {
            const dest_reg = uf.findRegByPtr(decl).?;
            const op_t = decl.instr.getOperationType();
            const imm = std.mem.asBytes(&op.rhs);
            try mov(writer, uf, op_t, decl_idx, op.lhs, true);
            if(op.rhs == 1) { // dec r/m64
                try writeDirect(writer, op_t, &.{0xFE | boolToU8(op_t != .u8)}, dest_reg, 1, &.{}, false);
            } else { // sub r/m64, imm8/16/32
                try writeOperandReg(writer, uf, op_t, decl_idx, 5, &.{0x80 | boolToU8(op_t != .u8)}, opTypeImm(op_t, imm), false);
            }
        },
        .shift_left_constant => |op| {
            const op_t = decl.instr.getOperationType();
            const imm = std.mem.asBytes(&op.rhs)[0..1];
            try mov(writer, uf, op_t, decl_idx, op.lhs, true);
            try writeOperandReg(writer, uf, op_t, decl_idx, 4, &.{
                0xC0 | boolToU8(op_t != .u8),
            }, imm, false);
        },
        .shift_right_constant => |op| {
            const op_t = decl.instr.getOperationType();
            const imm = std.mem.asBytes(&op.rhs)[0..1];
            try mov(writer, uf, op_t, decl_idx, op.lhs, true);
            try writeOperandReg(writer, uf, op_t, decl_idx, 5, &.{
                0xC0 | boolToU8(op_t != .u8),
            }, imm, false);
        },
        .bit_and_constant => |op| {
            const op_t = decl.instr.getOperationType();
            const imm = std.mem.asBytes(&op.rhs);
            try mov(writer, uf, op_t, decl_idx, op.lhs, true);
            try writeOperandReg(writer, uf, op_t, decl_idx, 4, &.{
                0x80 | boolToU8(op_t != .u8),
            }, opTypeImm(op_t, imm), false);
        },
        .inplace_add_constant => |op| {
            const op_t = decl.instr.getOperationType();
            if(op.rhs == 1) {
                try writeOperandReg(writer, uf, op_t, op.lhs, 0, &.{0xFE | boolToU8(op_t != .u8)}, &.{}, false);
            } else {
                const imm = std.mem.asBytes(&op.rhs);
                try writeOperandReg(writer, uf, op_t, op.lhs, 0, &.{0x80 | boolToU8(op_t != .u8)}, opTypeImm(op_t, imm), false);
            }
        },
        .load => |op| {
            const out_reg = uf.findRegByPtr(decl).?;
            if(uf.findReg(op.source)) |src_ptr_reg| {
                try writeRegIndirect(writer, op.type, &.{0x8A | boolToU8(op.type != .u8)}, src_ptr_reg, out_reg, 0, &.{}, true);
            } else {
                try mov(writer, uf, op.type, decl_idx, op.source, false);
            }
        },
        .store => |op| {
            const value = ir.decls.get(op.value);
            const op_t = value.instr.getOperationType();
            if(uf.findReg(op.dest)) |dest_ptr_reg| {
                const value_reg = uf.findRegByPtr(value).?;
                try writeRegIndirect(writer, op_t, &.{0x88 | boolToU8(op_t != .u8)}, dest_ptr_reg, value_reg, 0, &.{}, true);
            } else {
                try mov(writer, uf, op_t, op.dest, op.value, false);
            }
        },
        .addr_of => |op| try writeWithOperands(writer, uf, .u64, op, decl_idx, &.{0x8D}, &.{}, true),
        .store_constant => |op| {
            if((op.type == .u16 or op.type == .u64) and (op.value <= 0x7F or op.value > 0xFFFFFFFFFFFFFF80)) {
                // push imm8; pop r/mN
                try pushImm(writer, @intCast(i8, @bitCast(i64, op.value)));
                try writeOperandReg(writer, uf, if(op.type == .u64) .u32 else op.type, op.dest, 0, &.{0x8F}, &.{}, false);
            } else { // mov r/mN, immN
                const imm = std.mem.asBytes(&op.value);
                try writeOperandReg(writer, uf, op.type, op.dest, 0, &.{0xC6 | boolToU8(op.type != .u8)}, opTypeImm(op.type, imm), false);
            }
        },
        .less_constant, .less_equal_constant,
        .greater_constant, .greater_equal_constant,
        .equals_constant, .not_equal_constant,
        => |op| {
            const imm = std.mem.asBytes(&op.rhs);
            const op_t = decl.instr.getOperationType();
            if(std.math.cast(i8, op.rhs)) |_| {
                try writeOperandReg(writer, uf, op_t, op.lhs, 7, &.{if(op_t == .u8) @as(u8, 0x80) else 0x83}, imm[0..1], false);
            } else if(op_t == .u16) {
                try writeOperandReg(writer, uf, op_t, op.lhs, 7, &.{0x81}, imm[0..2], false);
            } else if(std.math.cast(i32, op.rhs)) |_| {
                try writeOperandReg(writer, uf, op_t, op.lhs, 7, &.{0x81}, imm[0..4], false);
            } else {
                @panic(":(");
            }
        },
        .less, .less_equal, .greater, .greater_equal, .equals, .not_equal => |op| {
            const op_t = decl.instr.getOperationType();
            try writeEitherOperandRm(writer, uf, op_t, op.lhs, op.rhs, &.{0x38 | boolToU8(op_t != .u8)}, &.{0x3A | boolToU8(op_t != .u8)}, &.{}, true);
        },
        .@"if" => |op| {
            const op_instr = ir.decls.get(op.condition).instr;
            const cond_flag: u8 = switch(op_instr) {
                .less, .less_constant, => cond_flags.below,
                .less_equal, .less_equal_constant => cond_flags.below_equal,
                .greater, .greater_constant => cond_flags.not | cond_flags.below_equal,
                .greater_equal, .greater_equal_constant => cond_flags.not | cond_flags.below,
                .equals, .equals_constant => cond_flags.zero,
                .not_equal, .not_equal_constant => cond_flags.not | cond_flags.zero,
                else => blk: { // It's a bool in a register
                    try writeOperandReg(writer, uf, .u8, op.condition, 7, &.{0x80}, &.{0}, false);
                    break :blk cond_flags.not | cond_flags.zero;
                },
            };
            const taken_reloc_type = writer.pickSmallestRelocationType(
                op.taken,
                &.{.{2, .rel8_post_0}},
            ) orelse .rel32_post_0;
            var not_taken_reloc_type = writer.pickSmallestRelocationType(
                op.not_taken,
                &.{.{2, .rel8_post_0}},
            ) orelse .rel32_post_0;
            if(try writer.attemptInlineEdge(op.taken)) |new_block| {
                switch(not_taken_reloc_type) {
                    .rel8_post_0 => try writer.writeInt(u8, 0x70 | cond_flag ^ cond_flags.not),
                    .rel32_post_0 => {
                        try writer.writeInt(u8, 0x0F);
                        try writer.writeInt(u8, 0x80 | cond_flag ^ cond_flags.not);
                    },
                    else => unreachable,
                }
                try writer.writeRelocatedValue(op.not_taken, not_taken_reloc_type);
                return new_block;
            } else if(try writer.attemptInlineEdge(op.not_taken)) |new_block| {
                switch(taken_reloc_type) {
                    .rel8_post_0 => try writer.writeInt(u8, 0x70 | cond_flag),
                    .rel32_post_0 => {
                        try writer.writeInt(u8, 0x0F);
                        try writer.writeInt(u8, 0x80 | cond_flag);
                    },
                    else => unreachable,
                }
                try writer.writeRelocatedValue(op.taken, taken_reloc_type);
                return new_block;
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
                not_taken_reloc_type = writer.pickSmallestRelocationType(
                    op.not_taken,
                    &.{.{2, .rel8_post_0}},
                ) orelse .rel32_post_0;
                try writer.writeInt(u8, @as(u8, switch(not_taken_reloc_type) {
                    .rel8_post_0 => 0xEB,
                    .rel32_post_0 => 0xE9,
                    else => unreachable,
                }));
                try writer.writeRelocatedValue(op.not_taken, not_taken_reloc_type);
            }
        },
        .goto => |edge| {
            if(try writer.attemptInlineEdge(edge)) |new_block| {
                return new_block;
            } else {
                const reloc_type = writer.pickSmallestRelocationType(
                    edge,
                    &.{.{1, .rel8_post_0}},
                ) orelse .rel32_post_0;
                try writer.writeInt(u8, @as(u8, switch(reloc_type) {
                    .rel8_post_0 => 0xEB,
                    .rel32_post_0 => 0xE9,
                    else => unreachable,
                }));
                try writer.writeRelocatedValue(edge, reloc_type);
            }
        },
        .function_call => |fcall| {
            try writer.writeInt(u8, 0xE8);
            try writer.writeRelocatedFunction(fcall.callee, .rel32_post_0);
        },
        .tail_call => |tcall| {
            try writeLeaveFunction(writer, used_registers, ir.decls.get(tcall.tail).instr.leave_function);
            try writer.writeInt(u8, 0xE9);
            try writer.writeRelocatedFunction(tcall.callee, .rel32_post_0);
        },
        .syscall => {
            try writer.writeInt(u8, 0x0F);
            try writer.writeInt(u8, 0x05);
        },
        .@"unreachable" => try writer.write(&.{0x0F, 0x0B}),
        inline else => |_, tag| @panic("TODO: x86_64 decl " ++ @tagName(tag)),
    }
    return null;
}

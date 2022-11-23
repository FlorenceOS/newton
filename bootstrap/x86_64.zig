const std = @import("std");

const backend = @import("backend.zig");
const ir = @import("ir.zig");
const rega = @import("rega.zig");

const Writer = backend.Writer(@This());

pub const registers = struct {
    const rax = 0;
    const rcx = 1;
    const rdx = 2;
    const rbx = 3;
    const rsp = 4;
    const rbp = 5;
    const rsi = 6;
    const rdi = 7;

    pub const return_reg = rax;
    pub const gprs = [_]u8{rax, rcx, rdx, rbx, rsi, rdi, 8, 9, 10, 11, 12, 13, 14, 15};
    pub const param_regs = [_]u8{rdi, rsi, rdx, rcx, 8, 9};
};

pub const pointer_type: ir.InstrType = .u64;

pub fn registerName(reg: u8) []const u8 {
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

fn rexPrefix(writer: *Writer, w: bool, r: bool, x: bool, b: bool) !void {
    var result: u8 = 0;
    if(w) result |= 1 << 3;
    if(r) result |= 1 << 2;
    if(x) result |= 1 << 1;
    if(b) result |= 1 << 0;
    if(result != 0) {
        try writer.writeInt(u8, 0x40 | result);
    }
}

fn prefix(writer: *Writer, operation_type: ir.InstrType, r: bool, x: bool, b: bool) !void {
    if(operation_type == .u16) {
        try writer.writeInt(u8, 0x66);
    }
    return rexPrefix(writer, operation_type == .u64, r, x, b);
}

const RmBuffer = std.BoundedArray(u8, 8);

const Rm = struct {
    rex_r: bool,
    rex_b: bool,
    encoded: RmBuffer,
};

fn rmRegDirect(rm: u8, reg: u8) Rm {
    var array: RmBuffer = .{};
    array.appendAssumeCapacity(0xC0 | (rm & 0x7) | ((reg & 0x7) << 3));
    return .{.rex_r = reg >= 8, .rex_b = rm >= 8, .encoded = array};
}

fn rmRegIndirect(rm: u8, reg: u8, offset: i32) Rm {
    var array: RmBuffer = .{};
    std.debug.assert(rm != registers.rsp and rm != 12); // SP and R12 uses SIB+DISP8
    if(offset == 0 and rm != registers.rbp and rm != 13) {
        array.appendAssumeCapacity(0x00 | (rm & 0x7) | ((reg & 0x7) << 3));
    } else if(std.math.cast(i8, offset)) |i8_offset| {
        array.appendAssumeCapacity(0x40 | (rm & 0x7) | ((reg & 0x7) << 3));
        array.appendSliceAssumeCapacity(&std.mem.toBytes(i8_offset));
    } else {
        array.appendAssumeCapacity(0x80 | (rm & 0x7) | ((reg & 0x7) << 3));
        array.appendSliceAssumeCapacity(&std.mem.toBytes(offset));
    }
    return .{.rex_r = reg >= 8, .rex_b = rm >= 8, .encoded = array};
}

fn rmStackOffset(stack_offset: i32, reg: u8) Rm {
    return rmRegIndirect(registers.rbp, reg, -stack_offset);
}

fn pushReg(writer: *Writer, reg: u8) !void {
    try rexPrefix(writer, reg >= 8, false, false, false);
    try writer.writeInt(u8, 0x50 | (reg & 0x7));
}

fn pushImm(writer: *Writer, value: i32) !void {
    if(std.math.cast(i8, value)) |i8_value| {
        try writer.writeInt(u8, 0x6A);
        try writer.writeInt(i8, i8_value);
    } else {
        try writer.writeInt(u8, 0x68);
        try writer.writeInt(i32, value);
    }
}

fn popReg(writer: *Writer, reg: u8) !void {
    try rexPrefix(writer, false, reg >= 8, false, false);
    try writer.writeInt(u8, 0x58 | (reg & 0x7));
}

fn popRm(writer: *Writer, rm: Rm) !void {
    try rexPrefix(writer, false, rm.rex_r, false, rm.rex_b);
    try writer.writeInt(u8, 0x8F);
    try writer.write(rm.encoded.slice());
}

fn movRegToReg(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, src_reg: u8) !void {
    if(dest_reg == src_reg) return;
    const rm = rmRegDirect(dest_reg, src_reg);
    try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
    try writer.writeInt(u8, 0x89);
    try writer.write(rm.encoded.slice());
}

fn movRmToReg(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, rm: Rm) !void {
    const opcode: u8 = if(operation_type == .u8) 0x8A else 0x8B;
    try prefix(writer, operation_type, rm.rex_r, false, dest_reg >= 8);
    try writer.writeInt(u8, opcode);
    try writer.write(rm.encoded.slice());
}

fn movRegToRm(writer: *Writer, operation_type: ir.InstrType, rm: Rm, src_reg: u8) !void {
    const opcode: u8 = if(operation_type == .u8) 0x88 else 0x89;
    try prefix(writer, operation_type, src_reg >= 8, false, rm.rex_r);
    try writer.writeInt(u8, opcode);
    try writer.write(rm.encoded.slice());
}

fn movImmToRm(writer: *Writer, operation_type: ir.InstrType, rm: Rm, value: i32) !void {
    if(operation_type == .u64 and value <= 0x7F or value > 0xFFFFFFFFFFFFFF80) {
        try pushImm(writer, value);
        try popRm(writer, rm);
    } else {
        const opcode: u8 = if(operation_type == .u8) 0xC6 else 0xC7;
        try prefix(writer, operation_type, false, false, rm.rex_r);
        try writer.writeInt(u8, opcode);
        try writer.write(rm.encoded.slice());
        switch(operation_type) {
            .u8 => try writer.writeInt(i8, @intCast(i8, value)),
            .u16 => try writer.writeInt(i16, @intCast(i16, value)),
            .u32 => try writer.writeInt(i32, @intCast(i32, value)),
            .u64 => try writer.writeInt(i32, value),
        }
    }
}

fn movImmToReg(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, value: u64) !void {
    _ = operation_type;
    if(std.math.cast(i32, value)) |i32_value| {
        try pushImm(writer, i32_value);
        try popReg(writer, dest_reg);
    } else {
        @panic("TODO");
    }
}

fn addRegReg(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, rhs_reg: u8) !void {
    const opcode: u8 = if(operation_type == .u8) 0x00 else 0x01;
    const rm = rmRegDirect(dest_reg, rhs_reg);
    try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
    try writer.writeInt(u8, opcode);
    try writer.write(rm.encoded.slice());
}

fn addReg3(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, lhs_reg: u8, rhs_reg: u8) !void {
    if(dest_reg == lhs_reg) {
        return addRegReg(writer, operation_type, dest_reg, rhs_reg);
    } else if (dest_reg == rhs_reg) {
        return addRegReg(writer, operation_type, dest_reg, lhs_reg);
    } else {
        // TODO: Replace when we support SIB byte memes
        try writer.writeInt(u8, 0x48
            | @as(u8, @boolToInt(lhs_reg >= 8)) << 0
            | @as(u8, @boolToInt(rhs_reg >= 8)) << 1
            | @as(u8, @boolToInt(dest_reg >= 8)) << 2
        );
        try writer.writeInt(u8, 0x8D);
        try writer.writeInt(u8, ((dest_reg & 0x7) << 3) | 4);
        try writer.writeInt(u8, ((rhs_reg & 0x7) << 3) | (lhs_reg & 0x7));
    }
}

fn subImm(writer: *Writer, operation_type: ir.InstrType, dest_reg: u8, value: i32) !void {
    if(value == 1) {
        try prefix(writer, operation_type, false, false, dest_reg >= 8);
        try writer.writeInt(u8, 0xFF);
        try writer.writeInt(u8, 0xC8 | (dest_reg & 0x7));
    } else {
        const opcode: u8 = 0xE9 | (dest_reg & 0x7);
        try prefix(writer, operation_type, false, false, dest_reg >= 8);
        if(std.math.cast(i8, value)) |i8_value| {
            try writer.writeInt(u8, 0x83);
            try writer.writeInt(u8, opcode);
            try writer.writeInt(i8, i8_value);
        } else {
            try writer.writeInt(u8, 0x81);
            try writer.writeInt(u8, opcode);
            try writer.writeInt(i32, value);
        }
    }
}

pub fn writeDecl(writer: *Writer, decl_idx: ir.DeclIndex.Index, uf: rega.UnionFind) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .stack_ref, .undefined => {},
        .enter_function => |stack_size| if(stack_size > 0) {
            try pushReg(writer, registers.rbp);
            try movRegToReg(writer, .u64, registers.rbp, registers.rsp);
            try subImm(writer, .u64, registers.rsp, @intCast(i32, stack_size));
        },
        .copy => |source| try movRegToReg(
            writer,
            decl.instr.getOperationType(),
            uf.findRegByPtr(decl).?,
            uf.findReg(source).?,
        ),
        .truncate => |t| try movRegToReg(
            writer,
            t.type,
            uf.findRegByPtr(decl).?,
            uf.findReg(t.value).?,
        ),
        .zero_extend => |zext| {
            const dest_reg = uf.findRegByPtr(decl).?;
            const src_reg = uf.findReg(zext.value).?;

            const dest_type = decl.instr.getOperationType();
            const src_type = ir.decls.get(zext.value).instr.getOperationType();

            if(dest_type == .u64 and src_type == .u32) {
                try movRegToReg(writer, .u32, dest_reg, src_reg);
            } else {
                // movzx rM r/mN
                const rm = rmRegDirect(src_reg, dest_reg);
                const opcode: u8 = if(src_type == .u8) 0xB6 else 0xB7;
                try prefix(writer, dest_type, rm.rex_r, false, rm.rex_b);
                try writer.writeInt(u8, opcode);
                try writer.write(rm.encoded.slice());
            }
        },
        .load_int_constant => |constant| try movImmToReg(
            writer,
            constant.type,
            uf.findRegByPtr(decl).?,
            constant.value,
        ),
        .add => |op| try addReg3(
            writer,
            decl.instr.getOperationType(),
            uf.findRegByPtr(decl).?,
            uf.findReg(op.lhs).?,
            uf.findReg(op.rhs).?,
        ),
        .add_constant => |op| {
            const dest_reg = uf.findRegByPtr(decl).?;
            const lhs_reg = uf.findReg(op.lhs).?;
            const operation_type = decl.instr.getOperationType();
            if(dest_reg == lhs_reg) {
                if(op.rhs == 1) { // inc r/m64
                    const rm = rmRegDirect(dest_reg, 0);
                    try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
                    try writer.writeInt(u8, 0xFF);
                    try writer.write(rm.encoded.slice());
                } else { // add r/m64, imm8/16/32
                    const rm = rmRegDirect(dest_reg, 0);
                    const opcode: u8 = if(operation_type == .u8) 0x80 else 0x81;
                    try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
                    try writer.writeInt(u8, opcode);
                    try writer.write(rm.encoded.slice());
                    switch(operation_type) {
                        .u8 => try writer.writeInt(i8, @intCast(i8, @bitCast(i64, op.rhs))),
                        .u16 => try writer.writeInt(i16, @intCast(i16, @bitCast(i64, op.rhs))),
                        .u32, .u64 => try writer.writeInt(i32, @intCast(i32, @bitCast(i64, op.rhs))),
                    }
                }
            } else { // lea r/m64, [r + disp32]
                const rm = rmRegIndirect(lhs_reg, dest_reg, @intCast(i32, @bitCast(i64, op.rhs)));
                try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
                try writer.writeInt(u8, 0x8D);
                try writer.write(rm.encoded.slice());
            }
        },
        .load => |op| {
            const source = ir.decls.get(op.source);
            const dest_reg = uf.findRegByPtr(decl).?;
            const rm = switch(source.instr) {
                .stack_ref => |stack_offset| rmStackOffset(@intCast(i32, stack_offset), dest_reg),
                else => rmRegIndirect(uf.findRegByPtr(source).?, dest_reg, 0),
            };
            try movRmToReg(writer, op.type, dest_reg, rm);
        },
        .store => |op| {
            const dest = ir.decls.get(op.dest);
            const value = ir.decls.get(op.value);
            const value_reg = uf.findRegByPtr(value).?;
            const operation_type = value.instr.getOperationType();
            const rm = switch(dest.instr) {
                .stack_ref => |stack_offset| rmStackOffset(@intCast(i32, stack_offset), value_reg),
                else => rmRegIndirect(uf.findRegByPtr(dest).?, value_reg, 0),
            };
            try movRegToRm(writer, operation_type, rm, value_reg);
        },
        .store_constant => |op| {
            const dest = ir.decls.get(op.dest);
            const rm = switch(dest.instr) {
                .stack_ref => |stack_offset| rmStackOffset(@intCast(i32, stack_offset), 0),
                else => rmRegIndirect(uf.findRegByPtr(dest).?, 0, 0),
            };
            try movImmToRm(writer, op.type, rm, @intCast(i32, @bitCast(i64, op.value)));
        },
        .less_constant, .less_equal_constant,
        .greater_constant, .greater_equal_constant,
        .equals_constant, .not_equal_constant,
        => |op| {
            const reg = uf.findReg(op.lhs).?;
            const rm = rmRegDirect(reg, 7);
            const operation_type = decl.instr.getOperationType();
            try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
            if(std.math.cast(i8, op.rhs)) |i8_value| {
                const opcode: u8 = if(operation_type == .u8) 0x80 else 0x83;
                try writer.writeInt(u8, opcode);
                try writer.write(rm.encoded.slice());
                try writer.writeInt(i8, i8_value);
            } else if(std.math.cast(i32, op.rhs)) |i32_value| {
                try writer.writeInt(u8, 0x81);
                try writer.write(rm.encoded.slice());
                try writer.writeInt(i32, i32_value);
            } else {
                @panic(":(");
            }
        },
        .less, .less_equal, .equals, .not_equal => |op| {
            const lhs_reg = uf.findReg(op.lhs).?;
            const rhs_reg = uf.findReg(op.rhs).?;
            const rm = rmRegDirect(lhs_reg, rhs_reg);
            const operation_type = decl.instr.getOperationType();
            try prefix(writer, operation_type, rm.rex_r, false, rm.rex_b);
            const opcode: u8 = if(operation_type == .u8) 0x38 else 0x39;
            try writer.writeInt(u8, opcode);
            try writer.write(rm.encoded.slice());
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
        .@"return" => |ret| {
            const op_reg = uf.findReg(ret.value).?;
            std.debug.assert(op_reg == registers.rax);
            if(ret.restore_stack) {
                try movRegToReg(writer, .u64, registers.rsp, registers.rbp);
                try popReg(writer, registers.rbp);
            }
            try writer.writeInt(u8, 0xC3);
        },
        inline else => |_, tag| @panic("TODO: x86_64 decl " ++ @tagName(tag)),
    }
    return null;
}

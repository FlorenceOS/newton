const backend = @import("backend.zig");
const ir = @import("ir.zig");

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
    const rflags = 255; // Special value the IR will emit to signal the use of flags

    pub const return_reg = rax;
    pub const flags_reg = rflags;
    pub const gprs = [_]u8{rax, rcx, rdx, rbx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15};
    pub const param_regs = [_]u8{rdi, rsi, rdx, rcx, r8, r9};
};

pub fn writeDecl(writer: *backend.Writer(@This()), decl_idx: ir.DeclIndex.Index) !?ir.BlockIndex.Index {
    const decl = ir.decls.get(decl_idx);
    switch(decl.instr) {
        .param_ref, .@"undefined",
        => {},
        .add => |bop| {
            const dest_reg = decl.reg_alloc_value.?;
            const lhs_reg = ir.decls.get(bop.lhs).reg_alloc_value.?;
            const rhs_reg = ir.decls.get(bop.rhs).reg_alloc_value.?;

            if(dest_reg == lhs_reg) {
                try writer.writeInt(u8, 0x48);
                try writer.writeInt(u8, 0x01);
                try writer.writeInt(u8, 0xC0 | dest_reg | (rhs_reg << 3));
            } else {
                try writer.writeInt(u8, 0x48);
                try writer.writeInt(u8, 0x8D);
                try writer.writeInt(u8, (dest_reg << 3) | 4);
                try writer.writeInt(u8, (rhs_reg << 3) | lhs_reg);
            }
        },
        inline else => |_, tag| @panic("TODO: x86_64 decl " ++ @tagName(tag)),
    }
    return null;
}

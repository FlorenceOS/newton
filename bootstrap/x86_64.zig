const ir = @import("ir.zig");

const backend = @import("backend.zig");

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

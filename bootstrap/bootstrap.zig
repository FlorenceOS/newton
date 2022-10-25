const std = @import("std");

const ast = @import("ast.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const sources = @import("sources.zig");
const values = @import("values.zig");

pub fn main() !void {
    try ast.init();
    try sema.init();
    try sources.init();
    try values.init();

    var output_path: [:0]const u8 = "a.out";
    var root_path: ?[:0]u8 = null;

    const argv = std.os.argv;
    var i: usize = 1;
    while(i < argv.len) : (i += 1) {
        const arg = std.mem.span(argv[i]);
        if(std.mem.eql(u8, arg, "-o")) {
            i += 1;
            output_path = std.mem.span(argv[i]);
        }
        else {
            root_path = std.mem.span(argv[i]);
        }
    }

    if(root_path) |rp| {
        const root_ast = try parser.parseRootFile(rp);
        const root_sema = try sema.analyzeExpr(root_ast);
        const root_value = sema.values.get(root_sema);
        const root_type = sema.types.get(root_value.type_idx);
        const root_struct = sema.structs.get(root_type.struct_idx);

        const main_decl = (try root_struct.lookupStaticDecl("main")).?;
        try main_decl.analyze();
        std.debug.print("{any}\n", .{main_decl});
        std.debug.print("{any}\n", .{sema.values.get(main_decl.init_value)});
    } else {
        std.debug.print("Missing root file path!\n", .{});
    }
}

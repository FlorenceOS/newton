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
        const root_struct = try parser.parseRootFile(rp);
        _ = try sema.analyzeExpr(root_struct);
    } else {
        std.debug.print("Missing root file path!\n", .{});
    }
}

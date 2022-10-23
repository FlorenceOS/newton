const std = @import("std");

const parser = @import("parser.zig");

pub fn main() !void {
    try @import("ast.zig").init();
    try @import("sources.zig").init();
    try @import("values.zig").init();

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
        _ = try parser.parseRootFile(rp);
    } else {
        std.debug.print("Missing root file path!\n", .{});
    }
}

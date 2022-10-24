const std = @import("std");

const indexed_list = @import("indexed_list.zig");
const ast = @import("ast.zig");

pub const SourceIndex = indexed_list.Indices(u32, .{});
const SourceFileList = indexed_list.IndexedList(SourceIndex, SourceFile);

pub const SourceFile = struct {
    file: std.fs.File,
    dir: std.fs.Dir,
    contents: [:0]const u8,
    top_level_struct: ast.ExprIndex.Index,
};

pub var source_files: SourceFileList = undefined;

pub fn init() !void {
    source_files = try SourceFileList.init(std.heap.page_allocator);
}

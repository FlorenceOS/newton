const std = @import("std");

const indexed_list = @import("indexed_list.zig");
const ast = @import("ast.zig");
const sema = @import("sema.zig");

pub const SourceIndex = indexed_list.Indices(u32, opaque{}, .{});
const SourceFileList = indexed_list.IndexedList(SourceIndex, SourceFile);

pub const SourceFile = struct {
    file: std.fs.File,
    dir: std.fs.Dir,
    realpath: []const u8,
    contents: [:0]const u8,
    top_level_struct: ast.ExprIndex.Index,
    sema_struct: sema.ValueIndex.OptIndex,
};

pub var source_files: SourceFileList = undefined;

// Map from paths or package names to source file indices
pub var path_map = std.StringHashMap(SourceIndex.Index).init(std.heap.page_allocator);

pub fn init() !void {
    source_files = try SourceFileList.init(std.heap.page_allocator);
}

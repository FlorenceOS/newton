const std = @import("std");

const ast = @import("ast.zig");
const backend = @import("backend.zig");
const elf = @import("elf.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const sources = @import("sources.zig");
const ir = @import("ir.zig");

pub fn main() !void {
    try ast.init();
    try sema.init();
    try sources.init();
    try ir.init();

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
        const root_value_idx = try sema.values.insert(.{
            .unresolved = .{
                .expression = root_ast,
                .requested_type = .type,
                .scope = .builtin_scope,
            },
        });
        const root_value = sema.values.get(root_value_idx);
        try root_value.analyze();
        const root_type = sema.types.get(root_value.type_idx);
        const root_struct = sema.structs.get(root_type.struct_idx);

        const root_scope = sema.scopes.get(root_struct.scope);
        const main_decl = (try root_scope.lookupDecl("main")).?;
        try main_decl.analyze();
        std.debug.print("{any}\n", .{sema.values.get(main_decl.init_value)});

        try backend.writer.output_bytes.appendNTimes(backend.writer.allocator, 0xCC, 6);
        while((backend.writer.output_bytes.items.len & 3) != 0) {
            try backend.writer.output_bytes.append(backend.writer.allocator, 0xCC);
        }

        try backend.writer.writeFunction(main_decl.init_value);
        var elf_writer = try elf.Writer.init(std.heap.page_allocator);
        for(sema.decls.elements.items[1..]) |decl| {
            if(backend.writer.placed_functions.get(decl.init_value)) |offset| {
                const token = try decl.name.retokenize();
                defer token.deinit();
                try elf_writer.addSymbol(token.identifier_value(), offset);
            }
        }
        const main_offset = backend.writer.placed_functions.get(main_decl.init_value).?;
        var file = try std.fs.cwd().createFile("a.out", .{.mode = 0o777});
        defer file.close();
        try elf_writer.finalize(&file, backend.writer.output_bytes.items, main_offset);
    } else {
        std.debug.print("Missing root file path!\n", .{});
    }
}

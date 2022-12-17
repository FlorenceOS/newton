const std = @import("std");

const ast = @import("ast.zig");
const backends = @import("backends/backends.zig");
const elf = @import("elf.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const sources = @import("sources.zig");
const ir = @import("ir.zig");

pub fn main() !void {
    try ast.init();
    try sources.init();

    var output_path: [:0]const u8 = "a.out";
    var target: [:0]const u8 = "x86_64-linux";
    var root_path: ?[:0]u8 = null;

    _ = try parser.parsePackageRootFile("std/lib.n", "std");

    {
        const argv = std.os.argv;
        var i: usize = 1;
        while(i < argv.len) : (i += 1) {
            const arg = std.mem.span(argv[i]);
            if(std.mem.eql(u8, arg, "-o")) {
                i += 1;
                output_path = std.mem.span(argv[i]);
            } else if(std.mem.eql(u8, arg, "-target")) {
                i += 1;
                target = std.mem.span(argv[i]);
            } else if(std.mem.eql(u8, arg, "-package")) {
                i += 1;
                var split_it = std.mem.split(u8, std.mem.span(argv[i]), ":");
                const package_name = split_it.next().?;
                const package_root = split_it.next().?;
                std.debug.assert(split_it.next() == null);
                _ = try parser.parsePackageRootFile(package_root, package_name);
            } else {
                root_path = std.mem.span(argv[i]);
            }
        }
    }

    var target_it = std.mem.split(u8, target, "-");
    const arch_str = target_it.next().?;
    const os_str = target_it.next().?;
    const abi_str = target_it.next();
    std.debug.assert(target_it.next() == null);

    var target_arch: ?*const backends.Backend = null;
    var target_os: ?*const backends.Os = null;
    var target_abi: ?*const backends.Abi = null;

    inline for(@typeInfo(backends.backends).Struct.decls) |arch_decl| {
        const platform = &@field(backends.backends, arch_decl.name);
        if(std.mem.eql(u8, arch_str, arch_decl.name)) {
            target_arch = &platform.backend;
            inline for(@typeInfo(platform.oses).Struct.decls) |os_decl| {
                const os = &@field(platform.oses, os_decl.name);

                if(std.mem.eql(u8, os_str, os_decl.name)) {
                    target_os = os;
                }
            }
            if(abi_str) |abi_name| {
                inline for(@typeInfo(platform.abis).Struct.decls) |abi_decl| {
                    const abi = &@field(platform.abis, abi_decl.name);

                    if(std.mem.eql(u8, abi_name, abi_decl.name)) {
                        target_abi = abi;
                    }
                }
            }
        }
    }

    if(target_arch) |arch| {
        backends.current_backend = arch;
    } else {
        std.debug.panic("Could not find architecture {s}", .{arch_str});
    }

    if(target_os) |os| {
        backends.current_os = os;
    } else {
        std.debug.panic("Could not find OS {s} for architecture {s}", .{os_str, arch_str});
    }

    if(target_abi) |abi| {
        backends.current_default_abi = abi;
    } else if(abi_str) |abi| {
        std.debug.panic("Could not find ABI {s} for architecture {s}", .{abi, arch_str});
    } else {
        backends.current_default_abi = backends.current_os.default_abi;
    }

    try sema.init();
    try ir.init();

    if(root_path) |rp| {
        const root_ast = try parser.parseRootFile(rp);
        for(sources.source_files.elements.items[sources.SourceIndex.alloc_base..]) |*file| {
            try ast.dumpFile(file);
        }

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
        const main_call = try sema.callFunctionWithArgs(main_decl.init_value, null, .none);
        std.debug.print("{any}\n", .{sema.values.get(main_decl.init_value)});

        try backends.writer.output_bytes.appendNTimes(backends.writer.allocator, 0xCC, 6);
        while((backends.writer.output_bytes.items.len & 3) != 0) {
            try backends.writer.output_bytes.append(backends.writer.allocator, 0xCC);
        }

        try backends.writer.writeFunction(main_call.callee);
        var elf_writer = try elf.Writer.init(std.heap.page_allocator);
        var name_buf = try std.ArrayList(u8).initCapacity(std.heap.page_allocator, 4096);
        for(sema.decls.elements.items[1..]) |decl| {
            const token = try decl.name.retokenize();
            defer token.deinit();
            if(!decl.static or decl.comptime_param) continue;
            switch(sema.values.get(decl.init_value).*) {
                .function => |*func| {
                    name_buf.shrinkRetainingCapacity(0);
                    try name_buf.appendSlice(token.identifier_value());
                    const base_name_len = name_buf.items.len;

                    for(func.instantiations.items) |instantiation, i| {
                        const inst = sema.InstantiatedFunction{
                            .function_value = decl.init_value,
                            .instantiation = @intCast(u32, i),
                        };
                        if(backends.writer.placed_functions.get(inst)) |offset| {
                            name_buf.shrinkRetainingCapacity(base_name_len);
                            try instantiation.name(func, name_buf.writer());
                            try elf_writer.addSymbol(
                                name_buf.items,
                                offset,
                                true,
                                backends.writer.function_sizes.get(inst).?,
                            );
                        }
                    }
                },
                else => {
                    if(decl.offset) |offset| {
                        const global_ty = try sema.values.get(decl.init_value).getType();
                        try elf_writer.addSymbol(
                            token.identifier_value(),
                            offset,
                            false,
                            try sema.types.get(global_ty).getSize(),
                        );
                    }
                },
            }
        }
        const main_offset = backends.writer.placed_functions.get(main_call.callee).?;
        var file = try std.fs.cwd().createFile("a.out", .{.mode = 0o777});
        defer file.close();
        try elf_writer.finalize(&file, backends.writer.output_bytes.items, main_offset);
    } else {
        std.debug.print("Missing root file path!\n", .{});
    }
}

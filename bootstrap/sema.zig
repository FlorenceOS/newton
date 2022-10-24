const std = @import("std");

const ast = @import("ast.zig");
const indexed_list = @import("indexed_list.zig");

pub const TypeIndex = indexed_list.Indices(u32, .{});
pub const ValueIndex = indexed_list.Indices(u32, .{});
pub const StaticDeclIndex = indexed_list.Indices(u32, .{});
pub const StructFieldIndex = indexed_list.Indices(u32, .{});
pub const StructIndex = indexed_list.Indices(u32, .{});

const TypeList = indexed_list.IndexedList(TypeIndex, Type);
const ValueList = indexed_list.IndexedList(ValueIndex, Value);
const StaticDeclList = indexed_list.IndexedList(StaticDeclIndex, StaticDecl);
const StructFieldList = indexed_list.IndexedList(StructFieldIndex, StructField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);

pub const Type = union(enum) {
    unresolved: ast.ExprIndex.OptIndex,
    void,
    anyopaque,
    bool,
    type,
    unsigned_int: u32,
    signed_int: u32,
    struct_idx: StructIndex.Index,
};

pub const Value = union(enum) {
    unresolved: ast.ExprIndex.Index,
    runtime: TypeIndex.Index,
    type_idx: TypeIndex.Index,
    void,
    undefined,
    bool: bool,
    comptime_int: i65,
};

pub const StaticDecl = struct {
    mutable: bool,
    name: ast.SourceRef,
    type_idx: TypeIndex.Index,
    init_value: ValueIndex.Index,
    next: StaticDeclIndex.OptIndex,
};

pub const StructField = struct {
    name: ast.SourceRef,
    type_idx: TypeIndex.Index,
    init_value: ValueIndex.OptIndex,
    next: StructFieldIndex.OptIndex,
};

pub const Struct = struct {
    first_static_decl: StaticDeclIndex.OptIndex,
    first_field: StructFieldIndex.OptIndex,
};

pub var types: TypeList = undefined;
pub var values: ValueList = undefined;
pub var static_decls: StaticDeclList = undefined;
pub var struct_fields: StructFieldList = undefined;
pub var structs: StructList = undefined;

pub fn init() !void {
    types = try TypeList.init(std.heap.page_allocator);
    values = try ValueList.init(std.heap.page_allocator);
    static_decls = try StaticDeclList.init(std.heap.page_allocator);
    struct_fields = try StructFieldList.init(std.heap.page_allocator);
    structs = try StructList.init(std.heap.page_allocator);
}

pub fn analyzeExpr(expr_idx: ast.ExprIndex.Index) !ValueIndex.Index {
    const expr = ast.expressions.get(expr_idx);
    switch(expr.*) {
        .struct_expression => |type_body| {
            var first_static_decl = StaticDeclIndex.OptIndex.none;
            var last_static_decl = StaticDeclIndex.OptIndex.none;
            var first_field = StructFieldIndex.OptIndex.none;
            var last_field = StructFieldIndex.OptIndex.none;

            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        const static_decl_idx = try static_decls.insert(.{
                            .mutable = inner_decl.mutable,
                            .name = inner_decl.identifier,
                            .type_idx = try types.insert(.{ .unresolved = inner_decl.type }),
                            .init_value = try values.insert(.{ .unresolved = inner_decl.init_value }),
                            .next = .none,
                        });
                        const oidx = StaticDeclIndex.toOpt(static_decl_idx);
                        if(static_decls.getOpt(last_static_decl)) |ld| {
                            ld.next = oidx;
                        }
                        if(first_static_decl == .none) {
                            first_static_decl = oidx;
                        }
                        last_static_decl = oidx;
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        const field_decl_idx = try struct_fields.insert(.{
                            .name = field_decl.identifier,
                            .type_idx = try types.insert(.{ .unresolved = field_decl.type }),
                            .init_value = if(ast.ExprIndex.unwrap(field_decl.init_value)) |init_expr_idx| blk: {
                                break :blk ValueIndex.toOpt(try values.insert(.{ .unresolved = init_expr_idx }));
                            } else .none,
                            .next = .none,
                        });
                        const oidx = StructFieldIndex.toOpt(field_decl_idx);
                        if(struct_fields.getOpt(last_field)) |lf| {
                            lf.next = oidx;
                        }
                        if(first_field == .none) {
                            first_field = oidx;
                        }
                        last_field = oidx;
                    },
                    else => unreachable,
                }

                curr_decl = decl.next;
            }

            const struct_idx = try structs.insert(.{
                .first_static_decl = first_static_decl,
                .first_field = first_field,
            });

            return values.insert(.{
                .type_idx = try types.insert(.{ .struct_idx = struct_idx }),
            });
        },
        else => std.debug.panic("Unhandled expression type {s}", .{@tagName(expr.*)}),
    }
}

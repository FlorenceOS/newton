const std = @import("std");

const ast = @import("ast.zig");
const indexed_list = @import("indexed_list.zig");

pub const TypeIndex = indexed_list.Indices(u32, .{
    .void = .{.void = {}},
    .bool = .{.bool = {}},
    .type = .{.type = {}},
    .comptime_int = .{.comptime_int = {}},
});
pub const ValueIndex = indexed_list.Indices(u32, .{
    .type = .{.type_idx = .type},
});
pub const StaticDeclIndex = indexed_list.Indices(u32, .{});
pub const StructFieldIndex = indexed_list.Indices(u32, .{});
pub const StructIndex = indexed_list.Indices(u32, .{});

const TypeList = indexed_list.IndexedList(TypeIndex, Type);
const ValueList = indexed_list.IndexedList(ValueIndex, Value);
const StaticDeclList = indexed_list.IndexedList(StaticDeclIndex, StaticDecl);
const StructFieldList = indexed_list.IndexedList(StructFieldIndex, StructField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);

fn evaluateWithoutTypeHint(
    expr_idx: ast.ExprIndex.Index,
) !Value {
    switch(ast.expressions.get(expr_idx).*) {
        .identifier => @panic("TODO: Sema idents"),
        .int_literal => |lit| {
            const tok = try lit.retokenize();
            defer tok.deinit();
            return .{.comptime_int = tok.int_literal.value};
        },
        else => |expr| std.debug.panic("TODO: Sema {s} expression", .{@tagName(expr)}),
    }
}

fn evaluateWithTypeHint(
    expr_idx: ast.ExprIndex.Index,
    requested_type: ValueIndex.Index,
) !Value {
    _ = expr_idx;
    _ = requested_type;
    return error.NotImplemented;
}

const Unresolved = struct {
    expression: ast.ExprIndex.Index,
    requested_type: ValueIndex.OptIndex,

    pub fn evaluate(self: @This()) !Value {
        if(ValueIndex.unwrap(self.requested_type)) |request| {
            return evaluateWithTypeHint(self.expression, request);
        } else {
            return evaluateWithoutTypeHint(self.expression);
        }
    }
};

pub const Type = union(enum) {
    void,
    anyopaque,
    bool,
    type,
    comptime_int,
    unsigned_int: u32,
    signed_int: u32,
    struct_idx: StructIndex.Index,
};

pub const Value = union(enum) {
    unresolved: Unresolved,

    // Values of type `type`
    type_idx: TypeIndex.Index,

    // Non-type comptile time known values
    void,
    undefined,
    bool: bool,
    comptime_int: i65,

    // Runtime known values
    runtime: ValueIndex.Index,

    pub fn analyze(self: *@This()) !void {
        switch(self.*) {
            .unresolved => |u| self.* = try u.evaluate(),
            .runtime => |r| try values.get(r).analyze(),
            else => {},
        }
    }

    fn getType(self: *@This()) !TypeIndex.OptIndex {
        try self.analyze();
        return switch(self.*) {
            .unresolved => unreachable,
            .type_idx => .type,
            .void => .void,
            .undefined => .none,
            .bool => .bool,
            .comptime_int => .comptime_int,
            .runtime => |idx| TypeIndex.toOpt(values.get(idx).type_idx),
        };
    }
};

pub const StaticDecl = struct {
    mutable: bool,
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: StaticDeclIndex.OptIndex,

    pub fn analyze(self: *@This()) !void {
        const value_ptr = values.get(self.init_value);
        try value_ptr.analyze();
    }
};

pub const StructField = struct {
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: StructFieldIndex.OptIndex,
};

fn genericChainLookup(
    comptime IndexType: type,
    comptime NodeType: type,
    container: *indexed_list.IndexedList(IndexType, NodeType),
    list_head: IndexType.OptIndex,
    name: []const u8,
) !?*NodeType {
    var current = list_head;
    while(container.getOpt(current)) |node| {
        const token = try node.name.retokenize();
        defer token.deinit();
        if (std.mem.eql(u8, name, token.identifier_value())) {
            return node;
        }
        current = node.next;
    }
    return null;
}

fn _lookupStaticDecl(first: StaticDeclIndex.OptIndex, name: []const u8) !?*StaticDecl {
    return genericChainLookup(StaticDeclIndex, StaticDecl, &static_decls, first, name);
}

pub const Struct = struct {
    first_static_decl: StaticDeclIndex.OptIndex,
    first_field: StructFieldIndex.OptIndex,

    pub fn lookupStaticDecl(self: *@This(), name: []const u8) !?*StaticDecl {
        return _lookupStaticDecl(self.first_static_decl, name);
    }

    pub fn lookupField(self: *@This(), name: []const u8) !?*StructField {
        return genericChainLookup(StructFieldIndex, StructField, &struct_fields, self.first_field, name);
    }
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

fn astDeclToValue(
    value_idx: ast.ExprIndex.OptIndex,
    value_type_idx: ast.ExprIndex.OptIndex,
) !ValueIndex.Index {
    const value_type = if(ast.ExprIndex.unwrap(value_type_idx)) |value_type| blk: {
        break :blk ValueIndex.toOpt(try values.insert(.{.unresolved = .{
            .expression = value_type,
            .requested_type = .type,
        }}));
    } else .none;

    if(ast.ExprIndex.unwrap(value_idx)) |value| {
        return values.insert(.{.unresolved = .{
            .expression = value,
            .requested_type = value_type,
        }});
    } else {
        return values.insert(.{.runtime = ValueIndex.unwrap(value_type).?});
    }
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
                            .init_value = try astDeclToValue(
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
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
                            .init_value = try astDeclToValue(field_decl.init_value, field_decl.type),
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

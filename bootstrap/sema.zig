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
pub const DeclIndex = indexed_list.Indices(u32, .{});
pub const StructFieldIndex = indexed_list.Indices(u32, .{});
pub const StructIndex = indexed_list.Indices(u32, .{});
pub const FunctionParamIndex = indexed_list.Indices(u32, .{});
pub const ScopeIndex = indexed_list.Indices(u32, .{});

const TypeList = indexed_list.IndexedList(TypeIndex, Type);
const ValueList = indexed_list.IndexedList(ValueIndex, Value);
const DeclList = indexed_list.IndexedList(DeclIndex, Decl);
const StructFieldList = indexed_list.IndexedList(StructFieldIndex, StructField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);
const FunctionParamList = indexed_list.IndexedList(FunctionParamIndex, FunctionParam);
const ScopeList = indexed_list.IndexedList(ScopeIndex, Scope);

fn canFitNumber(value: i65, requested_type: TypeIndex.Index) bool {
    switch(types.get(requested_type).*) {
        .comptime_int => return true,
        .unsigned_int => |bits| {
            if(value < 0) return false;
            if(value > std.math.pow(u65, 2, bits) - 1) return false;
            return true;
        },
        .signed_int => |bits| {
            if(value < -std.math.pow(i65, 2, bits - 1)) return false;
            if(value > std.math.pow(u65, 2, bits - 1) - 1) return false;
            return true;
        },
        else => return false,
    }
}

fn promoteInteger(value: i65, requested_type: TypeIndex.Index) ?Value {
    if(!canFitNumber(value, requested_type)) return null;

    switch(types.get(requested_type).*) {
        .comptime_int => return .{.comptime_int = value},
        .unsigned_int => |bits| return .{.unsigned_int = .{.bits = bits, .value = value}},
        .signed_int => |bits| return .{.signed_int = .{.bits = bits, .value = value}},
        else => return null,
    }
}

fn evaluateWithoutTypeHint(scope_idx: ScopeIndex.Index, expr_idx: ast.ExprIndex.Index) anyerror!Value {
    switch(ast.expressions.get(expr_idx).*) {
        .identifier => |ident| {
            const token = try ident.retokenize();
            defer token.deinit();
            const decl = (try scopes.get(scope_idx).lookupDecl(token.identifier_value())).?;
            try decl.analyze();
            std.debug.assert(decl.mutable == false);
            const decl_value = values.get(decl.init_value);
            std.debug.assert(decl_value.* != .runtime);
            return decl_value.*;
        },
        .int_literal => |lit| {
            const tok = try lit.retokenize();
            defer tok.deinit();
            return .{.comptime_int = tok.int_literal.value};
        },
        .unsigned_int => |bits| return .{.type_idx = try types.addDedupLinear(.{.unsigned_int = bits})},
        .signed_int => |bits| return .{.type_idx = try types.addDedupLinear(.{.signed_int = bits})},
        .function_expression => |func_idx| {
            const func = ast.functions.get(func_idx);
            var first_param = FunctionParamIndex.OptIndex.none;
            var last_param = FunctionParamIndex.OptIndex.none;
            var curr_ast_param = func.first_param;
            while(ast.function_params.getOpt(curr_ast_param)) |ast_param| {
                const param_idx = try function_params.insert(.{
                    .name = ast_param.identifier,
                    .type_idx = try values.addDedupLinear(try evaluateWithTypeHint(scope_idx, ast_param.type, .type)),
                    .next = .none,
                });
                const oparam_idx = FunctionParamIndex.toOpt(param_idx);
                if(first_param == .none) {
                    first_param = oparam_idx;
                }
                if(function_params.getOpt(last_param)) |lp| {
                    lp.next = oparam_idx;
                }
                last_param = oparam_idx;
                curr_ast_param = ast_param.next;
            }

            return .{.function = .{
                .return_type = try values.addDedupLinear(try evaluateWithTypeHint(scope_idx, func.return_type, .type)),
                .first_param = first_param,
            }};
        },
        .pointer_type => |ptr| {
            const item_type_idx = try values.insert(.{.unresolved = .{
                .expression = ptr.item,
                .requested_type = .type,
                .scope = scope_idx,
            }});
            return .{.type_idx = try types.insert(.{.pointer = .{
                .is_const = ptr.is_const,
                .is_volatile = ptr.is_volatile,
                .item = item_type_idx,
            }})};
        },
        else => |expr| std.debug.panic("TODO: Sema {s} expression", .{@tagName(expr)}),
    }
}

fn evaluateWithTypeHint(
    scope_idx: ScopeIndex.Index,
    expr_idx: ast.ExprIndex.Index,
    requested_type: TypeIndex.Index,
) !Value {
    const evaluated = try evaluateWithoutTypeHint(scope_idx, expr_idx);
    switch(evaluated) {
        .comptime_int => |value| if(promoteInteger(value, requested_type)) |promoted| return promoted,
        .unsigned_int, .signed_int => |int| if(promoteInteger(int.value, requested_type)) |promoted| return promoted,
        .type_idx => if(requested_type == .type) return evaluated,
        else => {},
    }

    std.debug.panic("Could not evaluate {any} with type {any}", .{evaluated, types.get(requested_type)});
}

const Unresolved = struct {
    expression: ast.ExprIndex.Index,
    requested_type: ValueIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn evaluate(self: @This()) !Value {
        if(values.getOpt(self.requested_type)) |request| {
            try request.analyze();
            return evaluateWithTypeHint(self.scope, self.expression, request.type_idx);
        } else {
            return evaluateWithoutTypeHint(self.scope, self.expression);
        }
    }
};

const SizedInt = struct {
    bits: u32,
    value: i65,
};

const PointerType = struct {
    is_const: bool,
    is_volatile: bool,
    item: ValueIndex.Index,
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
    pointer: PointerType,

    pub fn equals(self: *const @This(), other: *const @This()) bool {
        if(@enumToInt(self.*) != @enumToInt(other.*)) return false;
        return switch(self.*) {
            .unsigned_int => |bits| other.unsigned_int == bits,
            .signed_int => |bits| other.signed_int == bits,
            .struct_idx => |idx| other.struct_idx == idx,
            else => true,
        };
    }
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
    unsigned_int: SizedInt,
    signed_int: SizedInt,
    function: Function,

    // Runtime known values
    runtime: ValueIndex.Index,

    // TODO: Implement this so we can dedup values :)
    pub fn equals(self: *const @This(), other: *const @This()) bool {
        _ = self;
        _ = other;
        return false;
    }

    pub fn analyze(self: *@This()) anyerror!void {
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
            .unsigned_int => |int| try types.insert(.{.unsigned_int = int.bits}),
            .signed_int => |int| try types.insert(.{.signed_int = int.bits}),
            .runtime => |idx| TypeIndex.toOpt(values.get(idx).type_idx),
        };
    }
};

pub const Decl = struct {
    mutable: bool,
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: DeclIndex.OptIndex,

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

pub const Struct = struct {
    first_field: StructFieldIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn lookupField(self: *@This(), name: []const u8) !?*StructField {
        return genericChainLookup(StructFieldIndex, StructField, &struct_fields, self.first_field, name);
    }
};

pub const FunctionParam = struct {
    name: ast.SourceRef,
    type_idx: ValueIndex.Index,
    next: FunctionParamIndex.OptIndex,
};

pub const Function = struct {
    return_type: ValueIndex.Index,
    first_param: FunctionParamIndex.OptIndex,
    // first_stmt: StatmentIndex.OptIndex,
};

pub const Scope = struct {
    outer_scope: ScopeIndex.OptIndex,
    first_decl: DeclIndex.OptIndex,

    pub fn lookupDecl(self: *@This(), name: []const u8) !?*Decl {
        return genericChainLookup(DeclIndex, Decl, &decls, self.first_decl, name);
    }
};

pub var types: TypeList = undefined;
pub var values: ValueList = undefined;
pub var decls: DeclList = undefined;
pub var struct_fields: StructFieldList = undefined;
pub var structs: StructList = undefined;
pub var function_params: FunctionParamList = undefined;
pub var scopes: ScopeList = undefined;

pub fn init() !void {
    types = try TypeList.init(std.heap.page_allocator);
    values = try ValueList.init(std.heap.page_allocator);
    decls = try DeclList.init(std.heap.page_allocator);
    struct_fields = try StructFieldList.init(std.heap.page_allocator);
    structs = try StructList.init(std.heap.page_allocator);
    function_params = try FunctionParamList.init(std.heap.page_allocator);
    scopes = try ScopeList.init(std.heap.page_allocator);
}

fn astDeclToValue(
    scope_idx: ScopeIndex.Index,
    value_idx: ast.ExprIndex.OptIndex,
    value_type_idx: ast.ExprIndex.OptIndex,
) !ValueIndex.Index {
    const value_type = if(ast.ExprIndex.unwrap(value_type_idx)) |value_type| blk: {
        break :blk ValueIndex.toOpt(try values.insert(.{.unresolved = .{
            .expression = value_type,
            .requested_type = .type,
            .scope = scope_idx,
        }}));
    } else .none;

    if(ast.ExprIndex.unwrap(value_idx)) |value| {
        return values.insert(.{.unresolved = .{
            .expression = value,
            .requested_type = value_type,
            .scope = scope_idx,
        }});
    } else {
        return values.insert(.{.runtime = ValueIndex.unwrap(value_type).?});
    }
}

pub fn analyzeExpr(scope: ScopeIndex.OptIndex, expr_idx: ast.ExprIndex.Index) !ValueIndex.Index {
    const expr = ast.expressions.get(expr_idx);
    switch(expr.*) {
        .struct_expression => |type_body| {
            const scope_idx = try scopes.insert(.{.outer_scope = scope, .first_decl = .none});

            var first_decl = DeclIndex.OptIndex.none;
            var last_decl = DeclIndex.OptIndex.none;
            var first_field = StructFieldIndex.OptIndex.none;
            var last_field = StructFieldIndex.OptIndex.none;

            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        const decl_idx = try decls.insert(.{
                            .mutable = inner_decl.mutable,
                            .name = inner_decl.identifier,
                            .init_value = try astDeclToValue(
                                scope_idx,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                            .next = .none,
                        });
                        const oidx = DeclIndex.toOpt(decl_idx);
                        if(decls.getOpt(last_decl)) |ld| {
                            ld.next = oidx;
                        }
                        if(first_decl == .none) {
                            first_decl = oidx;
                        }
                        last_decl = oidx;
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        const field_decl_idx = try struct_fields.insert(.{
                            .name = field_decl.identifier,
                            .init_value = try astDeclToValue(scope_idx, field_decl.init_value, field_decl.type),
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
                .first_field = first_field,
                .scope = scope_idx,
            });

            scopes.get(scope_idx).first_decl = first_decl;

            return values.insert(.{
                .type_idx = try types.insert(.{ .struct_idx = struct_idx }),
            });
        },
        else => std.debug.panic("Unhandled expression type {s}", .{@tagName(expr.*)}),
    }
}

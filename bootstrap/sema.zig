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
    .void = .{.type_idx = .void},
    .bool = .{.type_idx = .bool},
    .type = .{.type_idx = .type},
    .discard_underscore = .{.discard_underscore = {}},
});
pub const DeclIndex = indexed_list.Indices(u32, .{});
pub const StructFieldIndex = indexed_list.Indices(u32, .{});
pub const StructIndex = indexed_list.Indices(u32, .{});
pub const ScopeIndex = indexed_list.Indices(u32, .{
    .builtin_scope = .{
        .outer_scope = .none,
        .first_decl = .none,
    },
});
pub const StatementIndex = indexed_list.Indices(u32, .{});
pub const ExpressionIndex = indexed_list.Indices(u32, .{});

const TypeList = indexed_list.IndexedList(TypeIndex, Type);
const ValueList = indexed_list.IndexedList(ValueIndex, Value);
const DeclList = indexed_list.IndexedList(DeclIndex, Decl);
const StructFieldList = indexed_list.IndexedList(StructFieldIndex, StructField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);
const ScopeList = indexed_list.IndexedList(ScopeIndex, Scope);
const StatementList = indexed_list.IndexedList(StatementIndex, Statement);
const ExpressionList = indexed_list.IndexedList(ExpressionIndex, Expression);

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

fn promoteInteger(value: i65, value_out: ValueIndex.OptIndex, requested_type: TypeIndex.Index) !ValueIndex.Index {
    if(!canFitNumber(value, requested_type)) return error.CannotPromote;

    switch(types.get(requested_type).*) {
        .comptime_int => return putValueIn(value_out, .{.comptime_int = value}),
        .unsigned_int => |bits| return putValueIn(value_out, .{.unsigned_int = .{.bits = bits, .value = value}}),
        .signed_int => |bits| return putValueIn(value_out, .{.signed_int = .{.bits = bits, .value = value}}),
        else => return error.CannotPromote,
    }
}

fn promoteToBiggest(lhs_idx: *ValueIndex.Index, rhs_idx: *ValueIndex.Index) !void {
    const lhs = values.get(lhs_idx.*);
    const rhs = values.get(rhs_idx.*);

    if(lhs.* == .comptime_int) {
        lhs_idx.* = try promoteInteger(lhs.comptime_int, .none, TypeIndex.unwrap(try rhs.getType()).?);
        return;
    }
    if(rhs.* == .comptime_int) {
        rhs_idx.* = try promoteInteger(rhs.comptime_int, .none, TypeIndex.unwrap(try lhs.getType()).?);
        return;
    }
}

fn analyzeStatementChain(scope_idx: ScopeIndex.Index, first_ast_stmt: ast.StmtIndex.OptIndex) !Block {
    const block_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx), .first_decl = .none});
    const block_scope = scopes.get(block_scope_idx);
    var decl_builder = decls.builder();
    var stmt_builder = statements.builder();
    var curr_ast_stmt = first_ast_stmt;
    while(ast.statements.getOpt(curr_ast_stmt)) |ast_stmt| {
        switch(ast_stmt.value) {
            .declaration => |decl| {
                const init_value = try astDeclToValue(block_scope_idx, ast.ExprIndex.toOpt(decl.init_value), decl.type);
                try values.get(init_value).analyze();
                const new_decl = try decl_builder.insert(.{
                    .mutable = decl.mutable,
                    .name = decl.identifier,
                    .init_value = init_value,
                    .next = .none,
                });
                _ = try stmt_builder.insert(.{.value = .{.declaration = new_decl}, .next = .none});
                if(block_scope.first_decl == .none) block_scope.first_decl = decl_builder.first;
            },
            .block_statement => |blk| {
                const new_scope = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(block_scope_idx), .first_decl = .none});
                const block = try analyzeStatementChain(new_scope, blk.first_child);
                _ = try stmt_builder.insert(.{.value = .{.block = block}, .next = .none});
            },
            .expression_statement => |ast_expr| {
                const value = try evaluateWithoutTypeHint(block_scope_idx, .none, ast_expr.expr);
                const expr = try expressions.insert(.{.value = value});
                _ = try stmt_builder.insert(.{.value = .{.expression = expr}, .next = .none});
            },
            else => |stmt| std.debug.panic("TODO: Sema {s} statement", .{@tagName(stmt)}),
        }
        curr_ast_stmt = ast_stmt.next;
    }
    return .{.scope = block_scope_idx, .first_stmt = stmt_builder.first};
}

fn putValueIn(
    value_out: ValueIndex.OptIndex,
    value: Value,
) !ValueIndex.Index {
    const retval = ValueIndex.unwrap(value_out) orelse try values.insert(undefined);
    values.get(retval).* = value;
    return retval;
}

fn evaluateWithoutTypeHint(
    scope_idx: ScopeIndex.Index,
    value_out: ValueIndex.OptIndex,
    expr_idx: ast.ExprIndex.Index,
) anyerror!ValueIndex.Index {
    switch(ast.expressions.get(expr_idx).*) {
        .void => return putValueIn(value_out, .{.type_idx = .void}),
        .anyopaque => return putValueIn(value_out, .{.type_idx = try types.addDedupLinear(.{.anyopaque = {}})}),
        .bool => return putValueIn(value_out, .{.type_idx = .bool}),
        .type => return putValueIn(value_out, .{.type_idx = .type}),
        .unsigned_int => |bits| return putValueIn(value_out, .{.type_idx = try types.addDedupLinear(.{.unsigned_int = bits})}),
        .signed_int => |bits| return putValueIn(value_out, .{.type_idx = try types.addDedupLinear(.{.signed_int = bits})}),
        .function_expression => |func_idx| {
            const func = ast.functions.get(func_idx);
            const param_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx), .first_decl = .none});
            const param_scope = scopes.get(param_scope_idx);
            var param_builder = decls.builder();
            var curr_ast_param = func.first_param;
            while(ast.function_params.getOpt(curr_ast_param)) |ast_param| {
                const param_type = try evaluateWithTypeHint(param_scope_idx, .none, ast_param.type, .type);
                _ = try param_builder.insert(.{
                    .mutable = true,
                    .name = ast_param.identifier,
                    .init_value = try values.addDedupLinear(.{.runtime = .{.expr = .none, .value_type = param_type}}),
                    .next = .none,
                });
                curr_ast_param = ast_param.next;
            }

            param_scope.first_decl = param_builder.first;

            const retval = try putValueIn(value_out, .{.function = .{
                .param_scope = param_scope_idx,
                .body = undefined,
                .return_type = try evaluateWithTypeHint(param_scope_idx, .none, func.return_type, .type),
            }});

            values.get(retval).function.body = try analyzeStatementChain(param_scope_idx, ast.StmtIndex.toOpt(func.body));
            return retval;
        },
        .pointer_type => |ptr| {
            const item_type_idx = try values.insert(.{.unresolved = .{
                .expression = ptr.item,
                .requested_type = .type,
                .scope = scope_idx,
            }});
            return putValueIn(value_out, .{.type_idx = try types.insert(.{.pointer = .{
                .is_const = ptr.is_const,
                .is_volatile = ptr.is_volatile,
                .item = item_type_idx,
            }})});
        },
        .struct_expression => |type_body| {
            const struct_scope = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx), .first_decl = .none});
            var decl_builder = decls.builder();
            var field_builder = struct_fields.builder();
            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        _ = try decl_builder.insert(.{
                            .mutable = inner_decl.mutable,
                            .name = inner_decl.identifier,
                            .init_value = try astDeclToValue(
                                struct_scope,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                            .next = .none,
                        });
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        _ = try field_builder.insert(.{
                            .name = field_decl.identifier,
                            .init_value = try astDeclToValue(struct_scope, field_decl.init_value, field_decl.type),
                            .next = .none,
                        });
                    },
                    else => unreachable,
                }

                curr_decl = decl.next;
            }

            const struct_idx = try structs.insert(.{
                .first_field = field_builder.first,
                .scope = struct_scope,
            });

            scopes.get(struct_scope).first_decl = decl_builder.first;

            return putValueIn(value_out, .{
                .type_idx = try types.insert(.{ .struct_idx = struct_idx }),
            });
        },
        .identifier => |ident| {
            const scope = scopes.get(scope_idx);
            const token = try ident.retokenize();
            defer token.deinit();
            if(try scope.lookupDecl(token.identifier_value())) |decl| {
                try values.get(decl.init_value).analyze();
                return decl.init_value;
            }
            return error.IdentifierNotFound;
        },
        .int_literal => |lit| {
            const tok = try lit.retokenize();
            return putValueIn(value_out, .{.comptime_int = tok.int_literal.value});
        },
        .char_literal => |lit| {
            const tok = try lit.retokenize();
            return putValueIn(value_out, .{.comptime_int = tok.char_literal.value});
        },
        .function_call => |call| {
            const callee_idx = try evaluateWithoutTypeHint(scope_idx, .none, call.callee);
            const callee = values.get(callee_idx);
            if(callee.* != .function) {
                return error.CallOnNonFunctionValue;
            }
            var arg_builder = expressions.builderWithPath("function_arg.next");
            var curr_ast_arg = call.first_arg;
            var curr_param_decl = scopes.get(callee.function.param_scope).first_decl;
            while(ast.expressions.getOpt(curr_ast_arg)) |ast_arg| {
                const func_arg = ast_arg.function_argument;
                const curr_param = decls.getOpt(curr_param_decl) orelse return error.TooManyArguments;
                _ = try arg_builder.insert(.{.function_arg = .{
                    .value = try evaluateWithTypeHint(
                        scope_idx,
                        .none,
                        func_arg.value,
                        values.get(values.get(curr_param.init_value).runtime.value_type).type_idx,
                    ),
                    .next = .none,
                }});
                curr_ast_arg = func_arg.next;
                curr_param_decl = curr_param.next;
            }
            if(curr_param_decl != .none) return error.NotEnoughArguments;
            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.function_call = .{
                    .callee = callee_idx,
                    .first_arg = arg_builder.first,
                }})),
                .value_type = callee.function.return_type,
            }});
        },
        .parenthesized => |uop| return evaluateWithoutTypeHint(scope_idx, .none, uop.operand),
        .discard_underscore => return .discard_underscore,
        inline
        .multiply, .multiply_eq, .multiply_mod, .multiply_mod_eq,
        .divide, .divide_eq, .modulus, .modulus_eq,
        .plus, .plus_eq, .plus_mod, .plus_mod_eq,
        .minus, .minus_eq, .minus_mod, .minus_mod_eq,
        .shift_left, .shift_left_eq, .shift_right, .shift_right_eq,
        .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq,
        .less, .less_equal, .greater, .greater_equal,
        .equals, .not_equal, .logical_and, .logical_or,
        .assign, .range,
        => |bop, tag| {
            var lhs = try evaluateWithoutTypeHint(scope_idx, .none, bop.lhs);
            var rhs = try evaluateWithoutTypeHint(scope_idx, .none, bop.rhs);
            const value_type = switch(tag) {
                .multiply_eq, .multiply_mod_eq, .divide_eq, .modulus_eq, .plus_eq, .plus_mod_eq, .minus_eq,
                .minus_mod_eq, .shift_left_eq, .shift_right_eq, .bitand_eq, .bitxor_eq, .bitor_eq, .assign,
                => .void,
                .less, .less_equal, .greater, .greater_equal,
                .equals, .not_equal, .logical_and, .logical_or,
                => .bool,
                .multiply, .multiply_mod, .divide, .modulus, .plus, .plus_mod,
                .minus, .minus_mod, .shift_left, .shift_right, .bitand, .bitor, .bitxor,
                => blk: {
                    try promoteToBiggest(&lhs, &rhs);
                    break :blk try values.addDedupLinear(.{.type_idx = TypeIndex.unwrap(try values.get(lhs).getType()).?});
                },
                else => std.debug.panic("TODO: {s}", .{@tagName(tag)}),
            };

            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(
                    @unionInit(Expression, @tagName(tag), .{.lhs = lhs, .rhs = rhs}),
                )),
                .value_type = value_type,
            }});
        },
        .addr_of => |uop| {
            const operand_idx = try evaluateWithoutTypeHint(scope_idx, .none, uop.operand);
            const operand = values.get(operand_idx);
            const result_type = try values.addDedupLinear(.{
                .type_idx = try types.addDedupLinear(.{.pointer = .{
                    .is_const = true,
                    .is_volatile = false,
                    .item = try values.addDedupLinear(.{.type_idx = TypeIndex.unwrap(try operand.getType()).?}),
                }}),
            });

            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.addr_of = operand_idx})),
                .value_type = result_type,
            }});
        },
        else => |expr| std.debug.panic("TODO: Sema {s} expression", .{@tagName(expr)}),
    }
}

fn evaluateWithTypeHint(
    scope_idx: ScopeIndex.Index,
    value_out: ValueIndex.OptIndex,
    expr_idx: ast.ExprIndex.Index,
    requested_type: TypeIndex.Index,
) !ValueIndex.Index {
    const evaluated = try evaluateWithoutTypeHint(scope_idx, value_out, expr_idx);
    switch(values.get(evaluated).*) {
        .comptime_int => |value| return promoteInteger(value, value_out, requested_type),
        .unsigned_int, .signed_int => |int| return promoteInteger(int.value, value_out, requested_type),
        .type_idx => if(requested_type == .type) return evaluated,
        else => {},
    }

    std.debug.panic("Could not evaluate {any} with type {any}", .{evaluated, types.get(requested_type)});
}

const Unresolved = struct {
    analysis_started: bool = false,
    expression: ast.ExprIndex.Index,
    requested_type: ValueIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn evaluate(self: *@This(), value_out: ValueIndex.Index) !ValueIndex.Index {
        if(self.analysis_started) {
            return error.CircularReference;
        }

        self.analysis_started = true;
        if(values.getOpt(self.requested_type)) |request| {
            try request.analyze();
            return evaluateWithTypeHint(self.scope, ValueIndex.toOpt(value_out), self.expression, request.type_idx);
        } else {
            return evaluateWithoutTypeHint(self.scope, ValueIndex.toOpt(value_out), self.expression);
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

pub const RuntimeValue = struct {
    expr: ExpressionIndex.OptIndex,
    value_type: ValueIndex.Index,
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
    discard_underscore,

    // Runtime known values
    runtime: RuntimeValue,

    // TODO: Implement this so we can dedup values :)
    pub fn equals(self: *const @This(), other: *const @This()) bool {
        _ = self;
        _ = other;
        return false;
    }

    pub fn analyze(self: *@This()) anyerror!void {
        switch(self.*) {
            .unresolved => |*u| self.* = values.get(try u.evaluate(values.getIndex(self))).*,
            .runtime => |r| try values.get(r.value_type).analyze(),
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
            .unsigned_int => |int| TypeIndex.toOpt(try types.addDedupLinear(.{.unsigned_int = int.bits})),
            .signed_int => |int| TypeIndex.toOpt(try types.addDedupLinear(.{.signed_int = int.bits})),
            .runtime => |rt| TypeIndex.toOpt(values.get(rt.value_type).type_idx),
            else => |other| std.debug.panic("TODO: Get type of {s}", .{@tagName(other)}),
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

pub const Function = struct {
    return_type: ValueIndex.Index,
    param_scope: ScopeIndex.Index,
    body: Block,
};

pub const Scope = struct {
    outer_scope: ScopeIndex.OptIndex,
    first_decl: DeclIndex.OptIndex,

    pub fn lookupDecl(self: *@This(), name: []const u8) !?*Decl {
        if(try genericChainLookup(DeclIndex, Decl, &decls, self.first_decl, name)) |result| {
            return result;
        }
        if(scopes.getOpt(self.outer_scope)) |outer_scope| {
            return @call(.{.modifier = .always_tail}, outer_scope.lookupDecl, .{name});
        }
        return null;
    }
};

pub const Block = struct {
    scope: ScopeIndex.Index,
    first_stmt: StatementIndex.OptIndex,
};

pub const Statement = struct {
    next: StatementIndex.OptIndex,
    value: union(enum) {
        expression: ExpressionIndex.Index,
        declaration: DeclIndex.Index,
        block: Block,
    },
};

pub const BinaryOp = struct {
    lhs: ValueIndex.Index,
    rhs: ValueIndex.Index,
};

pub const FunctionArgument = struct {
    value: ValueIndex.Index,
    next: ExpressionIndex.OptIndex,
};

pub const FunctionCall = struct {
    callee: ValueIndex.Index,
    first_arg: ExpressionIndex.OptIndex,
};

pub const Expression = union(enum) {
    value: ValueIndex.Index,

    addr_of: ValueIndex.Index,
    // deref: ValueIndex.Index,

    multiply: BinaryOp,
    multiply_eq: BinaryOp,
    multiply_mod: BinaryOp,
    multiply_mod_eq: BinaryOp,
    divide: BinaryOp,
    divide_eq: BinaryOp,
    modulus: BinaryOp,
    modulus_eq: BinaryOp,
    plus: BinaryOp,
    plus_eq: BinaryOp,
    plus_mod: BinaryOp,
    plus_mod_eq: BinaryOp,
    minus: BinaryOp,
    minus_eq: BinaryOp,
    minus_mod: BinaryOp,
    minus_mod_eq: BinaryOp,
    shift_left: BinaryOp,
    shift_left_eq: BinaryOp,
    shift_right: BinaryOp,
    shift_right_eq: BinaryOp,
    bitand: BinaryOp,
    bitand_eq: BinaryOp,
    bitor: BinaryOp,
    bitxor_eq: BinaryOp,
    bitxor: BinaryOp,
    bitor_eq: BinaryOp,
    less: BinaryOp,
    less_equal: BinaryOp,
    greater: BinaryOp,
    greater_equal: BinaryOp,
    equals: BinaryOp,
    not_equal: BinaryOp,
    logical_and: BinaryOp,
    logical_or: BinaryOp,
    assign: BinaryOp,
    range: BinaryOp,

    function_arg: FunctionArgument,
    function_call: FunctionCall,
};

pub var types: TypeList = undefined;
pub var values: ValueList = undefined;
pub var decls: DeclList = undefined;
pub var struct_fields: StructFieldList = undefined;
pub var structs: StructList = undefined;
pub var scopes: ScopeList = undefined;
pub var statements: StatementList = undefined;
pub var expressions: ExpressionList = undefined;

pub fn init() !void {
    types = try TypeList.init(std.heap.page_allocator);
    values = try ValueList.init(std.heap.page_allocator);
    decls = try DeclList.init(std.heap.page_allocator);
    struct_fields = try StructFieldList.init(std.heap.page_allocator);
    structs = try StructList.init(std.heap.page_allocator);
    scopes = try ScopeList.init(std.heap.page_allocator);
    statements = try StatementList.init(std.heap.page_allocator);
    expressions = try ExpressionList.init(std.heap.page_allocator);
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
        return values.insert(.{.runtime = .{.expr = .none, .value_type = ValueIndex.unwrap(value_type).?}});
    }
}

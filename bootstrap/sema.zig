const std = @import("std");

const ast = @import("ast.zig");
const backends = @import("backends/backends.zig");
const ir = @import("ir.zig");
const indexed_list = @import("indexed_list.zig");
const sources = @import("sources.zig");

pub const TypeIndex = indexed_list.Indices(u32, opaque{}, .{
    .void = .{.void = {}},
    .bool = .{.bool = {}},
    .type = .{.type = {}},
    .undefined = .{.undefined = {}},
    .comptime_int = .{.comptime_int = {}},
    .u8 = .{.unsigned_int = 8},
    .u16 = .{.unsigned_int = 16},
    .u32 = .{.unsigned_int = 32},
    .u64 = .{.unsigned_int = 64},
    .i8 = .{.signed_int = 8},
    .i16 = .{.signed_int = 16},
    .i32 = .{.signed_int = 32},
    .i64 = .{.signed_int = 64},
    .pointer_int = undefined,
});
pub const ValueIndex = indexed_list.Indices(u32, opaque{}, .{
    .void = .{.type_idx = .void},
    .bool = .{.type_idx = .bool},
    .type = .{.type_idx = .type},
    .undefined = .{.undefined = {}},
    .discard_underscore = .{.discard_underscore = {}},
    .u8_type = .{.type_idx = .u8},
    .u16_type = .{.type_idx = .u16},
    .u32_type = .{.type_idx = .u32},
    .u64_type = .{.type_idx = .u64},
    .pointer_int_type = .{.type_idx = .pointer_int},
    .syscall_func = .{.function = .{
        .return_type = .u64_type,
        .param_scope = undefined,
        .body = undefined,
    }},
});
pub const DeclIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const StructFieldIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const StructIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const ScopeIndex = indexed_list.Indices(u32, opaque{}, .{
    .builtin_scope = .{
        .outer_scope = .none,
        .first_decl = .none,
    },
});
pub const StatementIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const ExpressionIndex = indexed_list.Indices(u32, opaque{}, .{});

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
        .reference => |ref| return canFitNumber(value, ref.item),
        else => return false,
    }
}

fn promoteInteger(value: i65, value_out: ValueIndex.OptIndex, requested_type: TypeIndex.Index) !ValueIndex.Index {
    if(!canFitNumber(value, requested_type)) return error.IncompatibleTypes;

    switch(types.get(requested_type).*) {
        .comptime_int => return putValueIn(value_out, .{.comptime_int = value}),
        .unsigned_int => |bits| return putValueIn(value_out, .{.unsigned_int = .{.bits = bits, .value = value}}),
        .signed_int => |bits| return putValueIn(value_out, .{.signed_int = .{.bits = bits, .value = value}}),
        .reference => |ref| return promoteInteger(value, value_out, ref.item),
        else => return error.IncompatibleTypes,
    }
}

fn decayValueType(vidx: ValueIndex.Index) !TypeIndex.Index {
    const value = values.get(vidx);
    const ty_idx = try value.getType();
    switch(value.*) {
        .runtime => {
            const value_ty = types.get(ty_idx);
            if(value_ty.* == .reference) {
                return value_ty.reference.item;
            }
            return ty_idx;
        },
        else => return ty_idx,
    }
}

fn commonType(lhs_ty: TypeIndex.Index, rhs_ty: TypeIndex.Index) !TypeIndex.Index {
    const lhs = types.get(lhs_ty);
    const rhs = types.get(rhs_ty);
    if(lhs.* == .comptime_int and rhs.* == .comptime_int) return lhs_ty;
    if(lhs.* == .comptime_int) return rhs_ty;
    if(rhs.* == .comptime_int) return lhs_ty;

    if(lhs.* == .unsigned_int) {
        std.debug.assert(rhs.* == .unsigned_int);
        if(lhs.unsigned_int > rhs.unsigned_int) {
            return lhs_ty;
        } else {
            return rhs_ty;
        }
    }

    if(lhs.* == .signed_int) {
        std.debug.assert(rhs.* == .signed_int);
        if(lhs.signed_int > rhs.signed_int) {
            return lhs_ty;
        } else {
            return rhs_ty;
        }
    }

    return error.IncompatibleTypes;
}

fn promote(vidx: *ValueIndex.Index, target_tidx: TypeIndex.Index) !void {
    const value = values.get(vidx.*);
    const value_ty = types.get(try decayValueType(vidx.*));
    const ty = types.get(target_tidx);

    switch(value_ty.*) {
         .comptime_int => switch(ty.*) {
            .comptime_int => {},
            .unsigned_int => |bits| vidx.* = try values.addDedupLinear(.{.unsigned_int = .{
                .bits = bits,
                .value = value.comptime_int,
            }}),
            .signed_int => |bits| vidx.* = try values.addDedupLinear(.{.signed_int = .{
                .bits = bits,
                .value = value.comptime_int,
            }}),
            else => @panic("Comptime int to non-int type(?)"),
        },
        .unsigned_int => |value_bits| {
            const target_bits = ty.unsigned_int;
            if(value_bits > target_bits) return error.IncompatibleTypes;
            if(value_bits == target_bits) return;
            vidx.* = try Value.fromExpression(
                try expressions.insert(.{.zero_extend = .{.value = vidx.*, .type = target_tidx}}),
                try values.addDedupLinear(.{.type_idx = target_tidx}),
            );
        },
        .signed_int => |value_bits| {
            const target_bits = ty.signed_int;
            if(value_bits > target_bits) return error.IncompatibleTypes;
            if(value_bits == target_bits) return;
            vidx.* = try Value.fromExpression(
                try expressions.insert(.{.sign_extend = .{.value = vidx.*, .type = target_tidx}}),
                try values.addDedupLinear(.{.type_idx = target_tidx}),
            );
        },
        else => @panic("TODO"),
    }
}

fn inplaceOp(lhs_idx: ValueIndex.Index, rhs_idx: *ValueIndex.Index) !void {
    const op_ty = try decayValueType(lhs_idx);
    try promote(rhs_idx, op_ty);
}

fn plainBinaryOp(lhs_idx: *ValueIndex.Index, rhs_idx: *ValueIndex.Index) !void {
    const lhs_ty = try decayValueType(lhs_idx.*);
    const rhs_ty = try decayValueType(rhs_idx.*);
    const common_type = try commonType(lhs_ty, rhs_ty);
    try promote(lhs_idx, common_type);
    try promote(rhs_idx, common_type);
}

fn analyzeStatementChain(
    parent_scope_idx: ScopeIndex.Index,
    first_ast_stmt: ast.StmtIndex.OptIndex,
    current_function: ValueIndex.OptIndex,
    current_break_block: StatementIndex.OptIndex,
) !Block {
    const block_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(parent_scope_idx)});
    const block_scope = scopes.get(block_scope_idx);
    var decl_builder = decls.builder();
    var stmt_builder = statements.builder();
    var curr_ast_stmt = first_ast_stmt;
    var reaches_end = true;
    while(ast.statements.getOpt(curr_ast_stmt)) |ast_stmt| {
        if(!reaches_end) {
            return error.StatementUnreachable;
        }
        switch(ast_stmt.value) {
            .declaration => |decl| {
                const init_value_idx = try astDeclToValue(block_scope_idx, ast.ExprIndex.toOpt(decl.init_value), decl.type);
                const init_value = values.get(init_value_idx);
                try init_value.analyze();
                const decl_type = types.get(try init_value.getType());
                const new_decl = try decl_builder.insert(.{
                    .mutable = decl.mutable,
                    .static = false,
                    .stack_offset = null,
                    .function_param_idx = null,
                    .name = decl.identifier,
                    .init_value = init_value_idx,
                });
                switch(decl_type.*) {
                    .struct_idx, .array,
                    => decls.get(new_decl).stack_offset = @as(u32, undefined),
                    else => {},
                }
                _ = try stmt_builder.insert(.{.value = .{.declaration = new_decl}});
                if(block_scope.first_decl == .none) block_scope.first_decl = decl_builder.first;
            },
            .block_statement => |blk| {
                const new_scope = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(block_scope_idx)});
                const block = try analyzeStatementChain(new_scope, blk.first_child, current_function, current_break_block);
                _ = try stmt_builder.insert(.{.value = .{.block = block}});
            },
            .expression_statement => |ast_expr| {
                const value = try evaluateWithoutTypeHint(block_scope_idx, .none, ast_expr.expr);
                const expr = try expressions.insert(.{.value = value});
                _ = try stmt_builder.insert(.{.value = .{.expression = expr}});
            },
            .if_statement => |if_stmt| {
                const condition = try evaluateWithTypeHint(block_scope_idx, .none, if_stmt.condition, .bool);

                const taken_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const not_taken_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const taken_block = try analyzeStatementChain(taken_scope, if_stmt.first_taken, current_function, current_break_block);
                const not_taken_block = try analyzeStatementChain(not_taken_scope, if_stmt.first_not_taken, current_function, current_break_block);
                _ = try stmt_builder.insert(.{.value = .{.if_statement = .{
                    .condition = condition,
                    .taken = taken_block,
                    .not_taken = not_taken_block,
                }}});
                reaches_end = taken_block.reaches_end or not_taken_block.reaches_end;
            },
            .loop_statement => |loop| {
                std.debug.assert(loop.condition == .none);
                const body_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const loop_stmt_idx = try stmt_builder.insert(.{.value = .{.loop_statement = .{.body = undefined, .breaks = false}}});
                const body = try analyzeStatementChain(body_scope, loop.first_child, current_function, StatementIndex.toOpt(loop_stmt_idx));
                const loop_stmt = statements.get(loop_stmt_idx);
                loop_stmt.value.loop_statement.body = body;
                reaches_end = loop_stmt.value.loop_statement.breaks;
            },
            .break_statement => {
                if(StatementIndex.unwrap(current_break_block)) |break_block| {
                    reaches_end = false;
                    statements.get(break_block).value.loop_statement.breaks = true;
                    _ = try stmt_builder.insert(.{.value = .{.break_statement = break_block}});
                } else {
                    return error.BreakOutsideLoop;
                }
            },
            .return_statement => |ret_stmt| {
                const func_idx = ValueIndex.unwrap(current_function).?;
                const func = values.get(func_idx).function;
                const return_type = values.get(func.return_type);
                var expr = ValueIndex.OptIndex.none;
                if(ast.ExprIndex.unwrap(ret_stmt.expr)) |ret_expr| {
                    expr = ValueIndex.toOpt(try evaluateWithTypeHint(block_scope_idx, .none, ret_expr, return_type.type_idx));
                } else {
                    std.debug.assert(func.return_type == .void);
                }
                reaches_end = false;
                _ = try stmt_builder.insert(.{.value = .{.return_statement = .{.function = func_idx, .value = expr}}});
            },
            else => |stmt| std.debug.panic("TODO: Sema {s} statement", .{@tagName(stmt)}),
        }
        curr_ast_stmt = ast_stmt.next;
    }
    return .{.scope = block_scope_idx, .first_stmt = stmt_builder.first, .reaches_end = reaches_end};
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
        .string_literal => |sr| {
            const token = try sr.retokenize();
            defer token.deinit();
            const offset = backends.writer.currentOffset();
            try backends.writer.write(token.string_literal.value);
            try backends.writer.writeInt(u8, 0);
            // TODO: Slice types
            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.offset = .{
                    .offset = @intCast(u32, offset),
                    .type = .{
                        .is_volatile = false,
                        .is_const = true,
                        .item = .u8,
                    },
                }})),
                .value_type = try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{
                    .reference = .{.is_const = true, .is_volatile = false, .item = .u8},
                })}),
            }});
        },
        .function_expression => |func_idx| {
            const func = ast.functions.get(func_idx);
            const param_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            const param_scope = scopes.get(param_scope_idx);
            var param_builder = decls.builder();
            var curr_ast_param = func.first_param;
            var function_param_idx: u8 = 0;
            while(ast.function_params.getOpt(curr_ast_param)) |ast_param| {
                const param_type = try evaluateWithTypeHint(param_scope_idx, .none, ast_param.type, .type);
                _ = try param_builder.insert(.{
                    .mutable = true,
                    .static = false,
                    .stack_offset = null,
                    .function_param_idx = function_param_idx,
                    .name = ast_param.identifier,
                    .init_value = try values.insert(.{.runtime = .{.expr = .none, .value_type = param_type}}),
                });
                function_param_idx += 1;
                curr_ast_param = ast_param.next;
            }

            param_scope.first_decl = param_builder.first;

            const retval = try putValueIn(value_out, .{.function = .{
                .param_scope = param_scope_idx,
                .body = undefined,
                .return_type = try evaluateWithTypeHint(param_scope_idx, .none, func.return_type, .type),
            }});

            values.get(retval).function.body = try analyzeStatementChain(param_scope_idx, func.body, ValueIndex.toOpt(retval), .none);
            return retval;
        },
        .pointer_type => |ptr| {
            const item_type_idx = try values.insert(.{.unresolved = .{
                .expression = ptr.item,
                .requested_type = .type,
                .scope = scope_idx,
            }});
            try values.get(item_type_idx).analyze();
            return putValueIn(value_out, .{.type_idx = try types.addDedupLinear(.{.pointer = .{
                .is_const = ptr.is_const,
                .is_volatile = ptr.is_volatile,
                .item = values.get(item_type_idx).type_idx,
            }})});
        },
        .struct_expression => |type_body| {
            const struct_scope = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            var decl_builder = decls.builder();
            var field_builder = struct_fields.builder();
            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        _ = try decl_builder.insert(.{
                            .mutable = inner_decl.mutable,
                            .static = true,
                            .stack_offset = null,
                            .function_param_idx = null,
                            .name = inner_decl.identifier,
                            .init_value = try astDeclToValue(
                                struct_scope,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                        });
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        _ = try field_builder.insert(.{
                            .name = field_decl.identifier,
                            .init_value = try astDeclToValue(struct_scope, field_decl.init_value, field_decl.type),
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
                const init_value = values.get(decl.init_value);
                try init_value.analyze();
                if(init_value.* != .runtime and !decl.mutable) {
                    return decl.init_value;
                }
                return putValueIn(value_out, .{.decl_ref = decls.getIndex(decl)});
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
        .bool_literal => |lit| {
            return putValueIn(value_out, .{.bool = lit});
        },
        .undefined => return putValueIn(value_out, .{.undefined = {}}),
        .function_call => |call| {
            var arg_builder = expressions.builderWithPath("function_arg.next");
            var curr_ast_arg = call.first_arg;
            const ast_callee = ast.expressions.get(call.callee);
            const callee_idx = switch(ast_callee.*) {
                .syscall_func => blk: {
                    while(ast.expressions.getOpt(curr_ast_arg)) |ast_arg| {
                        const func_arg = ast_arg.function_argument;
                        var arg_value = evaluateWithoutTypeHint(
                            scope_idx,
                            .none,
                            func_arg.value
                        ) catch try evaluateWithTypeHint(scope_idx, .none, func_arg.value, .u64);
                        const arg_value_type = try values.get(arg_value).getType();
                        switch(types.get(arg_value_type).*) {
                            .pointer => {},
                            .comptime_int => {
                                if(values.get(arg_value).comptime_int < 0) {
                                    try promote(&arg_value, .i64);
                                } else {
                                    try promote(&arg_value, .u64);
                                }
                            },
                            .signed_int => try promote(&arg_value, .i64),
                            .unsigned_int => try promote(&arg_value, .u64),
                            else => |other| std.debug.panic("Can't pass {s} to syscall", .{@tagName(other)}),
                        }
                        _ = try arg_builder.insert(.{.function_arg = .{.value = arg_value}});
                        curr_ast_arg = func_arg.next;
                    }
                    break :blk .syscall_func;
                },
                else => blk: {
                    const callee_idx = try evaluateWithoutTypeHint(scope_idx, .none, call.callee);
                    const callee = values.get(callee_idx);
                    try callee.analyze();
                    if(callee.* != .function) {
                        std.debug.panic("Cannot call non-function: {any}", .{callee});
                    }
                    var curr_param_decl = scopes.get(callee.function.param_scope).first_decl;
                    while(ast.expressions.getOpt(curr_ast_arg)) |ast_arg| {
                        const func_arg = ast_arg.function_argument;
                        const curr_param = decls.getOpt(curr_param_decl) orelse return error.TooManyArguments;
                        _ = try arg_builder.insert(.{.function_arg = .{.value = try evaluateWithTypeHint(
                            scope_idx,
                            .none,
                            func_arg.value,
                            values.get(values.get(curr_param.init_value).runtime.value_type).type_idx,
                        )}});
                        curr_ast_arg = func_arg.next;
                        curr_param_decl = curr_param.next;
                    }
                    if(curr_param_decl != .none) return error.NotEnoughArguments;
                    break :blk callee_idx;
                },
            };
            const callee = values.get(callee_idx);
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
        .plus, .plus_eq, .plus_mod, .plus_mod_eq,
        .minus, .minus_eq, .minus_mod, .minus_mod_eq,
        .multiply, .multiply_eq, .multiply_mod, .multiply_mod_eq,
        .divide, .divide_eq, .modulus, .modulus_eq,
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
                .minus_mod_eq, .shift_left_eq, .shift_right_eq, .bitand_eq, .bitxor_eq, .bitor_eq, .assign
                => blk: {
                    try inplaceOp(lhs, &rhs);
                    break :blk .void;
                },
                .less, .less_equal, .greater, .greater_equal,
                .equals, .not_equal, .logical_and, .logical_or,
                => blk: {
                    try plainBinaryOp(&lhs, &rhs);
                    break :blk .bool;
                },
                .multiply, .multiply_mod, .divide, .modulus, .plus, .plus_mod,
                .minus, .minus_mod, .shift_left, .shift_right, .bitand, .bitor, .bitxor,
                => blk: {
                    try plainBinaryOp(&lhs, &rhs);
                    break :blk try values.addDedupLinear(.{.type_idx = try values.get(lhs).getType()});
                },
                else => std.debug.panic("TODO: {s}", .{@tagName(tag)}),
            };
            const sema_tag = switch(tag) {
                inline .plus, .plus_eq, .plus_mod, .plus_mod_eq => |a| "add" ++ @tagName(a)[4..],
                inline .minus, .minus_eq, .minus_mod, .minus_mod_eq => |a| "sub" ++ @tagName(a)[5..],
                inline .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq => |a| "bit_" ++ @tagName(a)[3..],
                else => |a| @tagName(a),
            };

            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(
                    @unionInit(Expression, sema_tag, .{.lhs = lhs, .rhs = rhs}),
                )),
                .value_type = value_type,
            }});
        },
        .addr_of => |uop| {
            const operand_idx = try evaluateWithoutTypeHint(scope_idx, .none, uop.operand);
            const operand = values.get(operand_idx);
            const result_type = switch(operand.*) {
                .decl_ref => |decl_idx| blk: {
                    const decl = decls.get(decl_idx);
                    decl.stack_offset = @as(u32, undefined);
                    break :blk try values.addDedupLinear(.{
                        .type_idx = try types.addDedupLinear(.{.pointer = .{
                            .is_const = !decl.mutable,
                            .is_volatile = false,
                            .item = try operand.getType(),
                        }}),
                    });
                },
                .runtime => |rt| blk: {
                    const value_type = types.get(values.get(rt.value_type).type_idx);
                    std.debug.assert(value_type.* == .reference);
                    break :blk try values.addDedupLinear(.{
                        .type_idx = try types.addDedupLinear(.{.pointer = value_type.reference}),
                    });
                },
                else => |other| std.debug.panic("Can't take the addr of {s}", .{@tagName(other)}),
            };

            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.addr_of = operand_idx})),
                .value_type = result_type,
            }});
        },
        .deref => |uop| {
            const operand_idx = try evaluateWithoutTypeHint(scope_idx, .none, uop.operand);
            const operand = values.get(operand_idx);
            const operand_type = types.get(try operand.getType());
            std.debug.assert(operand_type.* == .pointer);
            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = operand_idx})),
                .value_type = try values.addDedupLinear(.{
                    .type_idx = try types.addDedupLinear(.{.reference = operand_type.pointer})
                }),
            }});
        },
        .member_access => |bop| {
            var lhs = try evaluateWithoutTypeHint(scope_idx, .none, bop.lhs);
            const lhs_value = values.get(lhs);
            const rhs_expr = ast.expressions.get(bop.rhs);
            std.debug.assert(rhs_expr.* == .identifier);
            switch(lhs_value.*) {
                .decl_ref => |dr| {
                    const decl = decls.get(dr);
                    const lhs_type = types.get(try lhs_value.getType());
                    std.debug.assert(lhs_type.* == .struct_idx);
                    const lhs_struct = structs.get(lhs_type.struct_idx);
                    const token = try rhs_expr.identifier.retokenize();
                    defer token.deinit();
                    if(try lhs_struct.lookupField(token.identifier_value())) |field| {
                        const member_ptr = try values.addDedupLinear(.{
                            .type_idx = try types.addDedupLinear(.{.pointer = .{
                                .is_const = !decl.mutable,
                                .is_volatile = false,
                                .item = try values.get(field.init_value).getType(),
                            }}),
                        });
                        const offset_expr = try values.insert(.{.unsigned_int = .{
                            .bits = 64,
                            .value = try lhs_struct.offsetOf(StructFieldIndex.toOpt(struct_fields.getIndex(field))),
                        }});
                        const addr_of_expr = try Value.fromExpression(try expressions.insert(.{.addr_of = lhs}), member_ptr);
                        const member_ref = try values.addDedupLinear(.{
                            .type_idx = try types.addDedupLinear(.{.reference = .{
                                .is_const = !decl.mutable,
                                .is_volatile = false,
                                .item = try values.get(field.init_value).getType(),
                            }}),
                        });
                        const add_expr = try Value.fromExpression(try expressions.insert(.{.add = .{.lhs = addr_of_expr, .rhs = offset_expr}}), member_ptr);
                        return putValueIn(value_out, .{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = add_expr})),
                            .value_type = member_ref,
                        }});
                    } else {
                        return error.MemberNotFound;
                    }
                },
                .type_idx => |idx| {
                    const lhs_type = types.get(idx);
                    std.debug.assert(lhs_type.* == .struct_idx);
                    const lhs_struct = structs.get(lhs_type.struct_idx);
                    const token = try rhs_expr.identifier.retokenize();
                    defer token.deinit();
                    if(try scopes.get(lhs_struct.scope).lookupDecl(token.identifier_value())) |member_decl| {
                        std.debug.assert(!member_decl.mutable);
                        return member_decl.init_value;
                    } else {
                        return error.MemberNotFound;
                    }
                },
                else => |other| std.debug.panic("TODO member_access of {s}", .{@tagName(other)}),
            }
        },
        .array_subscript => |bop| {
            const lhs_idx = try evaluateWithoutTypeHint(scope_idx, .none, bop.lhs);
            const lhs = values.get(lhs_idx);
            const lhs_type = types.get(try lhs.getType());

            const child_type = switch(lhs_type.*) {
                .pointer => |ptr| ptr.item,
                .array => |arr| arr.child,
                else => std.debug.panic("TODO: array subscript of {s}", .{@tagName(lhs_type.*)}), // ref(ptr|arr)
            };

            const child_ptr = switch(lhs_type.*) {
                .pointer => |ptr| ptr,
                .array => blk: {
                    const decl = decls.get(lhs.decl_ref);
                    break :blk PointerType{
                        .is_const = !decl.mutable,
                        .is_volatile = false,
                        .item = child_type,
                    };
                },
                else => unreachable,
            };

            const size_expr = try values.addDedupLinear(.{.unsigned_int = .{
                .bits = 64,
                .value = @as(i65, @intCast(i64, try types.get(child_type).getSize())),
            }});
            var rhs_idx = try evaluateWithoutTypeHint(scope_idx, .none, bop.rhs);
            try inplaceOp(size_expr, &rhs_idx);
            const rhs = values.get(rhs_idx);
            const rhs_type = types.get(try rhs.getType());
            std.debug.assert(rhs_type.* == .signed_int or rhs_type.* == .unsigned_int or rhs_type.* == .comptime_int);
            const pointer_expr = if(lhs_type.* != .pointer) blk: {
                break :blk try Value.fromExpression(
                    try expressions.insert(.{.addr_of = lhs_idx}),
                     try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{.pointer = child_ptr})}),
                );
            } else lhs_idx;
            const offset_expr = try Value.fromExpression(
                try expressions.insert(.{.multiply = .{.lhs = rhs_idx, .rhs = size_expr}}),
                 .pointer_int_type,
            );
            const ptr_expr = try Value.fromExpression(
                try expressions.insert(.{.add = .{.lhs = pointer_expr, .rhs = offset_expr}}),
                 try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{.pointer = child_ptr})}),
            );
            return putValueIn(value_out, .{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = ptr_expr})),
                .value_type = try values.addDedupLinear(.{
                    .type_idx = try types.addDedupLinear(.{.reference = child_ptr})
                }),
            }});
        },
        .array_type => |bop| {
            const size = try evaluateWithTypeHint(scope_idx, .none, bop.lhs, .pointer_int);
            const child = try evaluateWithTypeHint(scope_idx, .none, bop.rhs, .type);
            return putValueIn(value_out, .{
                .type_idx = try types.addDedupLinear(.{.array = .{
                    .child = values.get(child).type_idx,
                    .size = @intCast(u32, values.get(size).unsigned_int.value),
                }}),
            });
        },
        .import_call => |import| return evaluateWithTypeHint(scope_idx, .none, sources.source_files.get(import).top_level_struct, .type),
        else => |expr| std.debug.panic("TODO: Sema {s} expression", .{@tagName(expr)}),
    }
}

fn evaluateWithTypeHint(
    scope_idx: ScopeIndex.Index,
    value_out: ValueIndex.OptIndex,
    expr_idx: ast.ExprIndex.Index,
    requested_type: TypeIndex.Index,
) !ValueIndex.Index {
    const evaluated_idx = try evaluateWithoutTypeHint(scope_idx, value_out, expr_idx);
    const evaluated = values.get(evaluated_idx);
    switch(evaluated.*) {
        .comptime_int => |value| return promoteInteger(value, value_out, requested_type),
        .unsigned_int, .signed_int => |int| return promoteInteger(int.value, value_out, requested_type),
        .bool => if(requested_type == .bool) return evaluated_idx,
        .type_idx => if(requested_type == .type) return evaluated_idx,
        .undefined => return Value.fromExpression(try expressions.insert(.{.value = .undefined}), try values.addDedupLinear(.{.type_idx = requested_type})),
        .runtime => |rt| {
            if(values.get(rt.value_type).type_idx == requested_type) return evaluated_idx;
            const evaluated_type = types.get(try evaluated.getType());
            if(evaluated_type.* == .reference and evaluated_type.reference.item == requested_type) {
                return Value.fromExpression(try expressions.insert(.{.value = evaluated_idx}), try values.addDedupLinear(.{.type_idx = requested_type}));
            }
        },
        .decl_ref => |dr| {
            const decl_type = try values.get(decls.get(dr).init_value).getType();
            if(decl_type == requested_type) return evaluated_idx;
        },
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

pub const PointerType = struct {
    is_const: bool,
    is_volatile: bool,
    item: TypeIndex.Index,
};

pub const Type = union(enum) {
    void,
    anyopaque,
    undefined,
    bool,
    type,
    comptime_int,
    unsigned_int: u32,
    signed_int: u32,
    struct_idx: StructIndex.Index,
    pointer: PointerType,
    reference: PointerType,
    array: struct {
        child: TypeIndex.Index,
        size: u32,
    },

    pub fn getSize(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type => 0,
            .bool => 1,
            .unsigned_int, .signed_int => |bits| @as(u32, 1) << @intCast(u5, std.math.log2_int_ceil(u32, @divTrunc(bits + 7, 8))),
            .pointer, .reference => switch(backends.current_backend.pointer_type) {
                .u64 => 8,
                .u32 => 4,
                .u16 => 2,
                .u8 => 1,
            },
            .array => |arr| try types.get(arr.child).getSize() * arr.size,
            .struct_idx => |struct_idx| try structs.get(struct_idx).offsetOf(.none),
            else => |other| std.debug.panic("TODO: getSize of type {s}", .{@tagName(other)}),
        };
    }

    pub fn getAlignment(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type => 1,
            .bool, .unsigned_int, .signed_int, .pointer, .reference => self.getSize(),
            .struct_idx => |struct_idx| structs.get(struct_idx).getAlignment(),
            .array => |arr| types.get(arr.child).getAlignment(),
            else => |other| std.debug.panic("TODO: getAlignment of type {s}", .{@tagName(other)}),
        };
    }
};

pub const RuntimeValue = struct {
    expr: ExpressionIndex.OptIndex,
    value_type: ValueIndex.Index,
};

pub const Value = union(enum) {
    unresolved: Unresolved,
    decl_ref: DeclIndex.Index,

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

    pub fn analyze(self: *@This()) anyerror!void {
        switch(self.*) {
            .unresolved => |*u| self.* = values.get(try u.evaluate(values.getIndex(self))).*,
            .runtime => |r| try values.get(r.value_type).analyze(),
            else => {},
        }
    }

    pub fn getType(self: *@This()) !TypeIndex.Index {
        try self.analyze();
        return switch(self.*) {
            .unresolved => unreachable,
            .type_idx => .type,
            .void => .void,
            .undefined => .undefined,
            .bool => .bool,
            .comptime_int => .comptime_int,
            .unsigned_int => |int| try types.addDedupLinear(.{.unsigned_int = int.bits}),
            .signed_int => |int| try types.addDedupLinear(.{.signed_int = int.bits}),
            .runtime => |rt| values.get(rt.value_type).type_idx,
            .decl_ref => |dr| return values.get(decls.get(dr).init_value).getType(),
            else => |other| std.debug.panic("TODO: Get type of {s}", .{@tagName(other)}),
        };
    }

    fn fromExpression(expression: ExpressionIndex.Index, value_type: ValueIndex.Index) !ValueIndex.Index {
        return values.insert(.{.runtime = .{.expr = ExpressionIndex.toOpt(expression), .value_type = value_type}});
    }
};

pub const Decl = struct {
    mutable: bool,
    static: bool,
    stack_offset: ?u32,
    function_param_idx: ?u8,
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: DeclIndex.OptIndex = .none,

    pub fn analyze(self: *@This()) !void {
        const value_ptr = values.get(self.init_value);
        try value_ptr.analyze();
    }
};

pub const StructField = struct {
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: StructFieldIndex.OptIndex = .none,
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

    pub fn getAlignment(self: *@This()) anyerror!u32 {
        var alignment: u32 = 0;
        var curr_field = self.first_field;
        while(struct_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            alignment = std.math.max(alignment, try field_type.getAlignment());
        }
        return alignment;
    }

    pub fn offsetOf(self: *@This(), field_idx: StructFieldIndex.OptIndex) anyerror!u32 {
        var offset: u32 = 0;
        var curr_field = self.first_field;
        while(struct_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            const alignment = try field_type.getAlignment();
            offset += alignment - 1;
            offset &= ~(alignment - 1);
            if(field_idx == curr_field) return offset;
            offset += try field_type.getSize();
        }
        std.debug.assert(field_idx == .none);
        const alignment = try self.getAlignment();
        offset += alignment - 1;
        offset &= ~(alignment - 1);
        return offset;
    }
};

pub const Function = struct {
    return_type: ValueIndex.Index,
    param_scope: ScopeIndex.Index,
    body: Block,
};

pub const Scope = struct {
    outer_scope: ScopeIndex.OptIndex,
    first_decl: DeclIndex.OptIndex = .none,

    pub fn lookupDecl(self: *@This(), name: []const u8) !?*Decl {
        var scope_idx = ScopeIndex.toOpt(scopes.getIndex(self));
        while(scopes.getOpt(scope_idx)) |scope| {
            if(try genericChainLookup(DeclIndex, Decl, &decls, scope.first_decl, name)) |result| {
                return result;
            }
            scope_idx = scope.outer_scope;
        }
        return null;
    }
};

pub const Block = struct {
    scope: ScopeIndex.Index,
    first_stmt: StatementIndex.OptIndex,
    reaches_end: bool,
};

pub const Statement = struct {
    next: StatementIndex.OptIndex = .none,
    ir_block: ir.BlockIndex.OptIndex = .none,
    value: union(enum) {
        expression: ExpressionIndex.Index,
        declaration: DeclIndex.Index,
        if_statement: struct {
            condition: ValueIndex.Index,
            taken: Block,
            not_taken: Block,
        },
        loop_statement: struct {
            body: Block,
            breaks: bool,
        },
        break_statement: StatementIndex.Index,
        return_statement: struct {
            function: ValueIndex.Index,
            value: ValueIndex.OptIndex,
        },
        block: Block,
    },
};

pub const BinaryOp = struct {
    lhs: ValueIndex.Index,
    rhs: ValueIndex.Index,
};

pub const FunctionArgument = struct {
    value: ValueIndex.Index,
    next: ExpressionIndex.OptIndex = .none,
};

pub const FunctionCall = struct {
    callee: ValueIndex.Index,
    first_arg: ExpressionIndex.OptIndex,
};

pub const Cast = struct {
    value: ValueIndex.Index,
    type: TypeIndex.Index,
};

pub const Expression = union(enum) {
    value: ValueIndex.Index,
    sign_extend: Cast,
    zero_extend: Cast,
    truncate: Cast,

    offset: struct { offset: u32, type: PointerType },
    addr_of: ValueIndex.Index,
    deref: ValueIndex.Index,

    add: BinaryOp,
    add_eq: BinaryOp,
    add_mod: BinaryOp,
    add_mod_eq: BinaryOp,
    sub: BinaryOp,
    sub_eq: BinaryOp,
    sub_mod: BinaryOp,
    sub_mod_eq: BinaryOp,
    multiply: BinaryOp,
    multiply_eq: BinaryOp,
    multiply_mod: BinaryOp,
    multiply_mod_eq: BinaryOp,
    divide: BinaryOp,
    divide_eq: BinaryOp,
    modulus: BinaryOp,
    modulus_eq: BinaryOp,
    shift_left: BinaryOp,
    shift_left_eq: BinaryOp,
    shift_right: BinaryOp,
    shift_right_eq: BinaryOp,
    bit_and: BinaryOp,
    bit_and_eq: BinaryOp,
    bit_or: BinaryOp,
    bit_or_eq: BinaryOp,
    bit_xor: BinaryOp,
    bit_xor_eq: BinaryOp,
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

    types.get(.pointer_int).* = switch(backends.current_backend.pointer_type) {
        .u64 => .{.unsigned_int = 64},
        .u32 => .{.unsigned_int = 32},
        .u16 => .{.unsigned_int = 16},
        .u8 => .{.unsigned_int = 8},
    };
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

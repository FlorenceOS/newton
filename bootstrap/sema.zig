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
    .discard_underscore = .{.discard_underscore = {}},
    .u8_type = .{.type_idx = .u8},
    .u16_type = .{.type_idx = .u16},
    .u32_type = .{.type_idx = .u32},
    .u64_type = .{.type_idx = .u64},
    .pointer_int_type = .{.type_idx = .pointer_int},
    .syscall_func = .{.function = undefined},
    .undefined = .{.undefined = null},
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
pub const TypeInitValueIndex = indexed_list.Indices(u32, opaque{}, .{});

const TypeList = indexed_list.IndexedList(TypeIndex, Type);
const ValueList = indexed_list.IndexedList(ValueIndex, Value);
const DeclList = indexed_list.IndexedList(DeclIndex, Decl);
const StructFieldList = indexed_list.IndexedList(StructFieldIndex, StructField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);
const ScopeList = indexed_list.IndexedList(ScopeIndex, Scope);
const StatementList = indexed_list.IndexedList(StatementIndex, Statement);
const ExpressionList = indexed_list.IndexedList(ExpressionIndex, Expression);
const TypeInitValueList = indexed_list.IndexedList(TypeInitValueIndex, TypeInitValue);

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
        .reference => |ref| return canFitNumber(value, ref.child),
        else => return false,
    }
}

fn promoteComptimeInt(value: i65, requested_type: TypeIndex.Index) !ValueIndex.Index {
    if(!canFitNumber(value, requested_type)) return error.IncompatibleTypes;

    switch(types.get(requested_type).*) {
        .comptime_int => return values.addDedupLinear(.{.comptime_int = value}),
        .unsigned_int => |bits| return values.addDedupLinear(.{.unsigned_int = .{.bits = bits, .value = value}}),
        .signed_int => |bits| return values.addDedupLinear(.{.signed_int = .{.bits = bits, .value = value}}),
        .reference => |ref| return promoteComptimeInt(value, ref.child),
        else => return error.IncompatibleTypes,
    }
}

fn decayValueType(vidx: ValueIndex.Index) !TypeIndex.Index {
    const ty_idx = try values.get(vidx).getType();
    switch(types.get(ty_idx).*) {
        .reference => |ptr| return ptr.child,
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

    if(lhs.* == .pointer) {
        switch(rhs.*) {
            .comptime_int,
            .unsigned_int,
            .signed_int,
            => return lhs_ty,
            .pointer => {
                if(rhs.pointer.is_volatile != lhs.pointer.is_volatile) return error.IncompatibleTypes;
                if(rhs.pointer.child != lhs.pointer.child) return error.IncompatibleTypes;
                return types.addDedupLinear(.{.pointer = .{
                    .child = lhs.pointer.child,
                    .is_volatile = lhs.pointer.is_volatile,
                    .is_const = lhs.pointer.is_const or rhs.pointer.is_const,
                }});
            },
            else => {},
        }
    }

    return error.IncompatibleTypes;
}

const TilAssignment = struct {
    // StructFieldIndex
    identifier: u32,
    assignment: union (enum) {
        default: ValueIndex.Index,
        normal: ast.ExprIndex.Index,
    },
};

fn typeTil(first_value: ast.TypeInitValueIndex.OptIndex, target_type: TypeIndex.Index) !std.BoundedArray(TilAssignment, 256) {
    var result = std.BoundedArray(TilAssignment, 256){};

    switch(types.get(target_type).*) {
        .struct_idx => |sidx| {
            const target_struct = structs.get(sidx);

            var current_iv = first_value;
            while(ast.type_init_values.getOpt(current_iv)) |tiv| : (current_iv = tiv.next) {
                const tiv_field_name = try tiv.identifier.?.retokenize();
                defer tiv_field_name.deinit();

                var found_field = false;

                var current_field = target_struct.first_field;
                while(struct_fields.getOpt(current_field)) |field| : (current_field = field.next) {
                    const struct_field_name = try field.name.retokenize();
                    defer struct_field_name.deinit();

                    if(std.mem.eql(u8, tiv_field_name.identifier_value(), struct_field_name.identifier_value())) {
                        found_field = true;
                        for(result.slice()) |ass| {
                            if(ass.identifier == @enumToInt(current_field)) {
                                std.debug.panic("Duplicate field '{s}'", .{tiv_field_name.identifier_value()});
                            }
                        }
                        try result.append(.{
                            .identifier = @enumToInt(current_field),
                            .assignment = .{.normal = tiv.value},
                        });
                    }
                }

                if(!found_field) {
                    std.debug.panic("Field '{s}' is specified but does not exist in struct type", .{tiv_field_name.identifier_value()});
                }
            }

            var current_field = target_struct.first_field;
            while(struct_fields.getOpt(current_field)) |field| : (current_field = field.next) {
                if(for(result.slice()) |ass| {
                    if(ass.identifier == @enumToInt(current_field)) {
                        break false;
                    }
                } else true) {
                    try result.append(.{
                        .identifier = @enumToInt(current_field),
                        .assignment = .{.default = field.init_value},
                    });
                }
            }
        },
        else => |t| std.debug.panic("typeTil for type {s}", .{@tagName(t)}),
    }

    return result;
}

fn promote(vidx: *ValueIndex.Index, target_tidx: TypeIndex.Index, is_assign: bool) !void {
    var value = values.get(vidx.*);

    // First decay the value
    if(value.* == .decl_ref) {
        const decl = decls.get(value.decl_ref);
        if(!decl.mutable and decl.static) {
            // This has to be a compile time known value
            value = values.get(decl.init_value);
            std.debug.assert(value.* != .runtime);
        }
    }

    const value_ty = types.get(try decayValueType(vidx.*));
    const ty = types.get(target_tidx);

    if(ty.* == .pointer) {
        const child_type = types.get(ty.pointer.child);
        switch(value_ty.*) {
            .comptime_int, .unsigned_int, .signed_int => {
                if(is_assign) return error.IncompatibleTypes;
                vidx.* = try Value.fromExpression(
                    try expressions.insert(.{.multiply = .{
                        .lhs = vidx.*,
                        .rhs = try values.addDedupLinear(.{.comptime_int = try child_type.getSize()}),
                    }}),
                    try values.addDedupLinear(.{.type_idx = target_tidx}),
                );
            },
            else => {
                if(value_ty.pointer.is_volatile == ty.pointer.is_volatile) {
                    if(value_ty.pointer.child == ty.pointer.child) {
                        if(!value_ty.pointer.is_const or ty.pointer.is_const) {
                            return;
                        }
                    }
                }
                std.debug.panic("Invalid assignment from {any} to pointer type {any}!", .{value_ty.*, ty.*});
            }
        }
        return;
    }

    switch(value_ty.*) {
        .comptime_int => {
            std.debug.assert(value.* != .decl_ref); // This must have been decayed earlier
            switch(value.*) {
                .runtime => {
                    std.debug.print("{any}\n", .{value.*});
                    std.debug.print("{any}\n", .{expressions.getOpt(value.runtime.expr).?});
                },
                else => {},
            }
            switch(ty.*) {
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
            }
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
        .bool, .type, .void => if(value_ty != ty) return error.IncompatibleTypes,
        .undefined => vidx.* = try values.addDedupLinear(.{.undefined = target_tidx}),
        else => |other| {
            if(std.meta.eql(ty.*, value_ty.*)) return;
            std.debug.panic("TODO {any} -> {any}", .{other, ty.*});
        },
    }
}

fn inplaceOp(lhs_idx: ValueIndex.Index, rhs_idx: *ValueIndex.Index, is_assign: bool) !void {
    if(lhs_idx != .discard_underscore) {
        const op_ty = try decayValueType(lhs_idx);
        try promote(rhs_idx, op_ty, is_assign);
    } else {
        std.debug.assert(is_assign);
    }
}

fn plainBinaryOp(lhs_idx: *ValueIndex.Index, rhs_idx: *ValueIndex.Index) !void {
    const lhs_ty = try decayValueType(lhs_idx.*);
    const rhs_ty = try decayValueType(rhs_idx.*);
    const common_type = try commonType(lhs_ty, rhs_ty);
    try promote(lhs_idx, common_type, false);
    try promote(rhs_idx, common_type, false);
}

fn analyzeStatementChain(
    parent_scope_idx: ScopeIndex.Index,
    first_ast_stmt: ast.StmtIndex.OptIndex,
    return_type: TypeIndex.Index,
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
                var decl_type: ?TypeIndex.Index = null;
                if(ast.ExprIndex.unwrap(decl.type)) |dt| {
                    decl_type = values.get(try semaASTExpr(block_scope_idx, dt, true, .type, null)).type_idx;
                }
                const new_decl = try decl_builder.insert(.{
                    .mutable = decl.mutable,
                    .static = false,
                    .comptime_param = false,
                    .offset = null,
                    .function_param_idx = null,
                    .name = decl.identifier,
                    .init_value = undefined,
                });
                const decl_ref = try values.insert(.{.decl_ref = new_decl});
                const return_location_ptr = try values.insert(.{.runtime = .{
                    .expr = ExpressionIndex.toOpt(try expressions.insert(.{.addr_of = decl_ref})),
                    .value_type = try values.addDedupLinear(.{
                        .type_idx = try types.addDedupLinear(.{.pointer = .{
                            .is_const = false,
                            .is_volatile = false,
                            .child = .void,
                        }}),
                    }),
                }});
                const init_value = try semaASTExpr(block_scope_idx, decl.init_value, false, decl_type, return_location_ptr);
                decls.get(new_decl).init_value = init_value;
                if(decl_type == null) {
                    decl_type = try values.get(init_value).getType();
                }
                if(types.get(decl_type.?).isContainer()) {
                    decls.get(new_decl).offset = @as(u32, undefined);
                }
                _ = try stmt_builder.insert(.{.value = .{.declaration = new_decl}});
                if(block_scope.first_decl == .none) block_scope.first_decl = decl_builder.first;
            },
            .block_statement => |blk| {
                const new_scope = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(block_scope_idx)});
                const block = try analyzeStatementChain(new_scope, blk.first_child, return_type, current_break_block);
                _ = try stmt_builder.insert(.{.value = .{.block = block}});
            },
            .expression_statement => |ast_expr| {
                const value = try semaASTExpr(block_scope_idx, ast_expr.expr, false, null, null);
                const expr = try expressions.insert(.{.value = value});
                _ = try stmt_builder.insert(.{.value = .{.expression = expr}});
            },
            .if_statement => |if_stmt| {
                const condition = try semaASTExpr(block_scope_idx, if_stmt.condition, false, .bool, null);
                const condition_value = values.get(condition);
                const taken_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const not_taken_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                if(condition_value.* == .bool) {
                    if(condition_value.bool) {
                        const taken_block = try analyzeStatementChain(taken_scope, if_stmt.first_taken, return_type, current_break_block);
                        _ = try stmt_builder.insert(.{.value = .{.block = taken_block}});
                        reaches_end = taken_block.reaches_end;
                    } else {
                        const not_taken_block = try analyzeStatementChain(not_taken_scope, if_stmt.first_not_taken, return_type, current_break_block);
                        _ = try stmt_builder.insert(.{.value = .{.block = not_taken_block}});
                        reaches_end = not_taken_block.reaches_end;
                    }
                } else {
                    const taken_block = try analyzeStatementChain(taken_scope, if_stmt.first_taken, return_type, current_break_block);
                    const not_taken_block = try analyzeStatementChain(not_taken_scope, if_stmt.first_not_taken, return_type, current_break_block);
                    _ = try stmt_builder.insert(.{.value = .{.if_statement = .{
                        .condition = condition,
                        .taken = taken_block,
                        .not_taken = not_taken_block,
                    }}});
                    reaches_end = taken_block.reaches_end or not_taken_block.reaches_end;
                }
            },
            .loop_statement => |loop| {
                std.debug.assert(loop.condition == .none);
                const body_scope = try scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const loop_stmt_idx = try stmt_builder.insert(.{.value = .{.loop_statement = .{.body = undefined, .breaks = false}}});
                const body = try analyzeStatementChain(body_scope, loop.first_child, return_type, StatementIndex.toOpt(loop_stmt_idx));
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
                var expr = ValueIndex.OptIndex.none;
                if(ast.ExprIndex.unwrap(ret_stmt.expr)) |ret_expr| {
                    expr = ValueIndex.toOpt(try semaASTExpr(block_scope_idx, ret_expr, false, return_type, null));
                } else {
                    std.debug.assert(return_type == .void);
                }
                reaches_end = false;
                _ = try stmt_builder.insert(.{.value = .{.return_statement =  expr}});
            },
            .unreachable_statement => {
                reaches_end = false;
                _ = try stmt_builder.insert(.{.value = .unreachable_statement});
            },
            else => |stmt| std.debug.panic("TODO: Sema {s} statement", .{@tagName(stmt)}),
        }
        curr_ast_stmt = ast_stmt.next;
    }
    return .{.scope = block_scope_idx, .first_stmt = stmt_builder.first, .reaches_end = reaches_end};
}

fn evaluateComptimeCall(fn_call: FunctionCall) ValueIndex.Index {
    if(fn_call.first_arg != .none) {
        @panic("TODO: Non-comptime marked parameters in comptime eval of function");
    }

    const callee = fn_call.callee;

    const instantiation = &values.get(callee.function_value).function.instantiations.items[callee.instantiation];

    var curr_stmt = instantiation.body.first_stmt;
    while(statements.getOpt(curr_stmt)) |stmt| : (curr_stmt = stmt.next) {
        switch(stmt.value) {
            .return_statement => |ret| return ValueIndex.unwrap(ret).?,
            else => |other| std.debug.panic("TODO: evaluateComptimeCall(): {any}", .{other}),
        }
    }
    unreachable;
}

fn fixupTypeHint(value_idx: ValueIndex.Index, type_hint: ?TypeIndex.Index) !ValueIndex.Index {
    var vidx = value_idx;
    if(type_hint) |ty| {
        try promote(&vidx, ty, true);
    }
    return vidx;
}

fn semaASTExpr(
    scope_idx: ScopeIndex.Index,
    expr_idx: ast.ExprIndex.Index,
    force_comptime_eval: bool,
    type_hint: ?TypeIndex.Index,
    // MUST match the type hint if provided
    // You can ONLY use this value if the resulting value is a container
    return_location_ptr: ?ValueIndex.Index,
) anyerror!ValueIndex.Index {
    return fixupTypeHint(switch(ast.expressions.get(expr_idx).*) {
        .identifier => |ident| blk: {
            const scope = scopes.get(scope_idx);
            const token = try ident.retokenize();
            defer token.deinit();
            if(try scope.lookupDecl(token.identifier_value())) |decl| {
                const init_value = values.get(decl.init_value);
                try init_value.analyze();
                if(init_value.* != .runtime and !decl.mutable) {
                    break :blk decl.init_value;
                }
                if(decl.static and decl.offset == null) {
                    decl.offset = @intCast(u32, try init_value.toBytes());
                }
                break :blk try values.addDedupLinear(.{.decl_ref = decls.getIndex(decl)});
            }
            std.debug.print("Cannot find identifier {s}\n", .{token.identifier_value()});
            return error.IdentifierNotFound;
        },
        .discard_underscore => .discard_underscore,
        .parenthesized => |uop| return semaASTExpr(scope_idx, uop.operand, force_comptime_eval, type_hint, return_location_ptr),
        .force_comptime_eval => |uop| {
            if(force_comptime_eval) @panic("Redundant comptime expression, already in comptime context");
            return semaASTExpr(scope_idx, uop.operand, true, type_hint, null);
        },

        .int_literal => |lit| try values.addDedupLinear(.{.comptime_int = (try lit.retokenize()).int_literal.value}),
        .char_literal => |lit| try values.addDedupLinear(.{.comptime_int = (try lit.retokenize()).char_literal.value}),
        .undefined => .undefined,
        .string_literal => |sr| blk: {
            const token = try sr.retokenize();
            defer token.deinit();
            const offset = backends.writer.currentOffset();
            // TODO: String interning
            try backends.writer.write(token.string_literal.value);
            try backends.writer.writeInt(u8, 0);
            // TODO: Slice types
            if(force_comptime_eval) @panic("TODO: Comptime string literals");
            const init_value = try values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.global = .{
                    .offset = @intCast(u32, offset),
                    .type = .{
                        .is_volatile = false,
                        .is_const = true,
                        .child = .u8,
                    },
                }})),
                .value_type = try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{
                    .reference = .{.is_const = true, .is_volatile = false, .child = .u8},
                })}),
            }});
            _ = try decls.insert(.{
                .mutable = false,
                .static = true,
                .comptime_param = false,
                .offset = @intCast(u32, offset),
                .function_param_idx = null,
                .name = sr,
                .init_value = init_value,
            });
            break :blk init_value;
        },

        .bool_literal => |lit| try values.addDedupLinear(.{.bool = lit}),
        .void => try values.addDedupLinear(.{.type_idx = .void}),
        .bool => try values.addDedupLinear(.{.type_idx = .bool}),
        .type => try values.addDedupLinear(.{.type_idx = .type}),
        .unsigned_int => |bits| try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{.unsigned_int = bits})}),
        .signed_int => |bits| try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{.signed_int = bits})}),

        .array_type => |arr| blk: {
            const size = try semaASTExpr(scope_idx, arr.lhs, true, .pointer_int, null);
            const child = try semaASTExpr(scope_idx, arr.rhs, true, .type, null);
            break :blk try values.addDedupLinear(.{.type_idx = try types.addDedupLinear(.{.array = .{
                .child = values.get(child).type_idx,
                .size = @intCast(u32, values.get(size).unsigned_int.value),
            }})});
        },
        .pointer_type => |ptr| blk: {
            const child_type = try semaASTExpr(scope_idx, ptr.child, true, .type, null);
            break :blk try values.insert(.{.type_idx = try types.addDedupLinear(.{.pointer = .{
                .is_const = ptr.is_const,
                .is_volatile = ptr.is_volatile,
                .child = values.get(child_type).type_idx,
            }})});
        },
        .struct_expression => |type_body| blk: {
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
                            .offset = null,
                            .comptime_param = false,
                            .function_param_idx = null,
                            .name = inner_decl.identifier,
                            .init_value = try lazyDeclInit(
                                struct_scope,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                        });
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        const field_type = try semaASTExpr(
                            struct_scope,
                            ast.ExprIndex.unwrap(field_decl.type).?,
                            true,
                            .type,
                            null,
                        );
                        _ = try field_builder.insert(.{
                            .name = field_decl.identifier,
                            .init_value = if(ast.ExprIndex.unwrap(field_decl.init_value)) |iv|
                                    try semaASTExpr(struct_scope, iv, true, values.get(field_type).type_idx, null)
                                else
                                    try values.insert(.{.runtime = .{
                                        .expr = .none,
                                        .value_type = field_type,
                                    }}),
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

            const type_idx = try types.insert(.{ .struct_idx = struct_idx });

            scopes.get(struct_scope).first_decl = decl_builder.first;
            scopes.get(struct_scope).this_type = TypeIndex.toOpt(type_idx);

            break :blk try values.insert(.{.type_idx = type_idx});
        },
        .function_expression => |func_idx| blk: {
            const func = ast.functions.get(func_idx);
            const param_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            const param_scope = scopes.get(param_scope_idx);
            var param_builder = decls.builder();
            var curr_ast_param = func.first_param;
            var function_param_idx: u8 = 0;
            while(ast.function_params.getOpt(curr_ast_param)) |ast_param| {
                const param_type = try values.insert(.{.unresolved = .{
                    .expression = ast_param.type,
                    .requested_type = .type,
                    .scope = undefined,
                }});
                _ = try param_builder.insert(.{
                    .mutable = true,
                    .static = false,
                    .offset = null,
                    .comptime_param = ast_param.is_comptime,
                    .function_param_idx = if(ast_param.is_comptime) null else function_param_idx,
                    .name = ast_param.identifier,
                    .init_value = try values.insert(.{.runtime = .{.expr = .none, .value_type = param_type}}),
                });
                if(!ast_param.is_comptime) function_param_idx += 1;
                curr_ast_param = ast_param.next;
            }

            param_scope.first_decl = param_builder.first;

            break :blk try values.insert(.{.function = .{
                .ast_function = func_idx,
                .generic_param_scope = param_scope_idx,
                .generic_body = func.body,
                .generic_return_type = func.return_type,
            }});
        },
        .function_call => |call| outer: {
            var curr_ast_arg = call.first_arg;
            const ast_callee = ast.expressions.get(call.callee);
            var return_type: ValueIndex.Index = undefined;
            const sema_call = switch(ast_callee.*) {
                .builtin_function => |bi| switch(bi) {
                    .import => unreachable,
                    .This => break :outer try values.insert(.{.type_idx = scopes.get(scope_idx).getThisType().?}),
                    .size_of => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(type_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        const type_value = types.get(values.get(ty).type_idx);

                        break :outer try values.insert(.{.comptime_int = try type_value.getSize()});
                    },
                    .is_pointer => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(type_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        break :outer try values.insert(.{.bool = types.get(values.get(ty).type_idx).* == .pointer});
                    },
                    .int_to_ptr => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        const expr_arg = ast.expressions.getOpt(type_arg.next).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        std.debug.assert(types.get(values.get(ty).type_idx).* == .pointer);
                        const value = try semaASTExpr(scope_idx, expr_arg.value, false, null, null);

                        if(force_comptime_eval) @panic("TODO: Comptime int_to_ptr");
                        break :outer try values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{
                                .value = value,
                            })),
                            .value_type = ty,
                        }});
                    },
                    .ptr_to_int => {
                        const expr_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        const value = try semaASTExpr(scope_idx, expr_arg.value, false, null, null);
                        std.debug.assert(types.get(try decayValueType(value)).* == .pointer);

                        if(force_comptime_eval) @panic("TODO: Comptime ptr_to_int");
                        break :outer try values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{
                                .value = value,
                            })),
                            .value_type = .pointer_int_type,
                        }});
                    },
                    .truncate => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        const expr_arg = ast.expressions.getOpt(type_arg.next).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        const value = try semaASTExpr(scope_idx, expr_arg.value, false, null, null);

                        if(force_comptime_eval) @panic("TODO: Comptime truncate");

                        break :outer try values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{.truncate = .{
                                .value = value,
                                .type = values.get(ty).type_idx,
                            }})),
                            .value_type = ty,
                        }});
                    },
                    .syscall => inner: {
                        var arg_builder = expressions.builderWithPath("function_arg.next");
                        while(ast.expressions.getOpt(curr_ast_arg)) |ast_arg| {
                            const func_arg = ast_arg.function_argument;
                            var arg_value = try semaASTExpr(scope_idx, func_arg.value, false, null, null);
                            const arg_value_type = try values.get(arg_value).getType();
                            switch(types.get(arg_value_type).*) {
                                .pointer, .signed_int, .unsigned_int => {},
                                .comptime_int => {
                                    if(values.get(arg_value).comptime_int < 0) {
                                        try promote(&arg_value, .i64, false);
                                    } else {
                                        try promote(&arg_value, .u64, false);
                                    }
                                },
                                else => |other| std.debug.panic("Can't pass {s} to syscall", .{@tagName(other)}),
                            }
                            _ = try arg_builder.insert(.{.function_arg = .{
                                .value = arg_value,
                                .param_decl = undefined,
                            }});
                            curr_ast_arg = func_arg.next;
                        }
                        return_type = .u64_type;
                        break :inner FunctionCall{
                            .callee = .{
                                .function_value = .syscall_func,
                                .instantiation = 0,
                            },
                            .first_arg = arg_builder.first,
                        };
                    },
                },
                else => inner: {
                    const callee_idx = try semaASTExpr(scope_idx, call.callee, true, null, null);
                    const callee = values.get(callee_idx);
                    // TODO: Runtime functions (function pointers)
                    switch(callee.*) {
                        .function => {
                            const gen = try callFunctionWithArgs(callee_idx, scope_idx, call.first_arg);
                            return_type = callee.function.instantiations.items[gen.callee.instantiation].return_type;
                            break :inner gen;
                        },
                        .bound_fn => |b| {
                            ast.expressions.get(b.first_arg).function_argument.next = call.first_arg;
                            const gen = try callFunctionWithArgs(b.callee, scope_idx, ast.ExprIndex.toOpt(b.first_arg));
                            return_type = values.get(b.callee).function.instantiations.items[gen.callee.instantiation].return_type;
                            break :inner gen;
                        },
                        else => std.debug.panic("Cannot call non-function: {any}", .{callee}),
                    }
                },
            };
            if(force_comptime_eval) {
                break :outer evaluateComptimeCall(sema_call);
            }
            break :outer try values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.function_call = sema_call})),
                .value_type = return_type,
            }});
        },

        .unary_bitnot => |uop| blk: {
            const value_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const value = values.get(value_idx);
            if(value.isComptime()) {
                switch(value.*) {
                    .comptime_int => |int| break :blk try values.insert(.{.comptime_int = ~int & 0xFFFFFFFFFFFFFFFF}),
                    else => unreachable,
                }
            }
            break :blk try Value.fromExpression(try expressions.insert(.{.bit_not = value_idx}), try values.insert(.{.type_idx = try value.getType()}));
        },

        .unary_lognot => |uop| blk: {
            const value_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, .bool, null);
            const value = values.get(value_idx);
            if(value.isComptime()) {
                switch(value.*) {
                    .bool => |b| break :blk try values.addDedupLinear(.{.bool = !b}),
                    else => unreachable,
                }
            }
            break :blk try Value.fromExpression(try expressions.insert(.{.logical_not = value_idx}), .bool);
        },

        inline
        .plus, .plus_eq, .minus, .minus_eq, .multiply, .multiply_eq,
        .divide, .divide_eq, .modulus, .modulus_eq,
        .shift_left, .shift_left_eq, .shift_right, .shift_right_eq,
        .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq,
        .less, .less_equal, .greater, .greater_equal,
        .equals, .not_equal, .logical_and, .logical_or,
        .assign, .range,
        => |bop, tag| {
            var lhs = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, null);
            // TODO: Assign RLS
            var rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);

            const value_type = switch(tag) {
                .plus_eq, .minus_eq, .multiply_eq, .divide_eq, .modulus_eq,
                .shift_left_eq, .shift_right_eq, .bitand_eq, .bitxor_eq, .bitor_eq, .assign
                => blk: {
                    try inplaceOp(lhs, &rhs, tag == .assign);
                    break :blk .void;
                },
                .less, .less_equal, .greater, .greater_equal,
                .equals, .not_equal, .logical_and, .logical_or,
                => blk: {
                    try plainBinaryOp(&lhs, &rhs);
                    break :blk .bool;
                },
                .plus, .minus, .multiply, .divide, .modulus,
                .shift_left, .shift_right, .bitand, .bitor, .bitxor,
                => blk: {
                    try plainBinaryOp(&lhs, &rhs);
                    break :blk try values.addDedupLinear(.{.type_idx = try values.get(lhs).getType()});
                },
                else => std.debug.panic("TODO: {s}", .{@tagName(tag)}),
            };
            const sema_tag = switch(tag) {
                inline .plus, .plus_eq => |a| "add" ++ @tagName(a)[4..],
                inline .minus, .minus_eq => |a| "sub" ++ @tagName(a)[5..],
                inline .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq => |a| "bit_" ++ @tagName(a)[3..],
                else => |a| @tagName(a),
            };

            const lhs_value = values.get(lhs);
            const rhs_value = values.get(rhs);
            if(lhs_value.isComptime() and rhs_value.isComptime()) {
                std.debug.assert(std.meta.activeTag(lhs_value.*) == std.meta.activeTag(rhs_value.*));
                const lhs_int = switch(lhs_value.*) {
                    .comptime_int => |i| i,
                    .unsigned_int => |i| i.value,
                    .signed_int => |i| i.value,
                    else => unreachable,
                };
                const rhs_int = switch(rhs_value.*) {
                    .comptime_int => |i| i,
                    .unsigned_int => |i| i.value,
                    .signed_int => |i| i.value,
                    else => unreachable,
                };
                return values.insert(switch(tag) {
                    .plus => .{.comptime_int = lhs_int +% rhs_int},
                    .minus => .{.comptime_int = lhs_int -% rhs_int},
                    .multiply => .{.comptime_int = lhs_int *% rhs_int},
                    .divide => .{.comptime_int = @divTrunc(lhs_int, rhs_int)},
                    .modulus => .{.comptime_int = @rem(lhs_int, rhs_int)},
                    .shift_left => .{.comptime_int = lhs_int << @intCast(u7, rhs_int)},
                    .shift_right => .{.comptime_int = lhs_int >> @intCast(u7, rhs_int)},
                    .bitand => .{.comptime_int = lhs_int & rhs_int},
                    .bitor => .{.comptime_int = lhs_int | rhs_int},
                    .bitxor => .{.comptime_int = lhs_int ^ rhs_int},
                    .less => .{.bool = lhs_int < rhs_int},
                    .less_equal => .{.bool = lhs_int <= rhs_int},
                    .greater => .{.bool = lhs_int > rhs_int},
                    .greater_equal => .{.bool = lhs_int >= rhs_int},
                    .equals => .{.bool = lhs_int == rhs_int},
                    .not_equal => .{.bool = lhs_int != rhs_int},
                    else => @panic("TODO: " ++ @tagName(tag)),
                });
            }

            return values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(
                    @unionInit(Expression, sema_tag, .{.lhs = lhs, .rhs = rhs}),
                )),
                .value_type = value_type,
            }});
        },
        .member_access => |bop| {
            var lhs = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, null);
            const lhs_value = values.get(lhs);
            const rhs_expr = ast.expressions.get(bop.rhs);
            std.debug.assert(rhs_expr.* == .identifier);
            const token = try rhs_expr.identifier.retokenize();
            defer token.deinit();
            switch(lhs_value.*) {
                .decl_ref => |dr| {
                    const lhs_type = types.get(try lhs_value.getType());
                    const lhs_struct = structs.get(switch(lhs_type.*) {
                        .struct_idx => |sidx| sidx,
                        .pointer => |ptr| types.get(ptr.child).struct_idx,
                        else => |other| std.debug.panic("Can't do member access on {any}", .{other}),
                    });
                    const decl = decls.get(dr);
                    if(try lhs_struct.lookupField(token.identifier_value())) |field| {
                        if(force_comptime_eval) @panic("TODO: Comptime eval field access");
                        const member_ptr = try values.addDedupLinear(.{
                            .type_idx = try types.addDedupLinear(.{.pointer = .{
                                .is_const = !decl.mutable,
                                .is_volatile = false,
                                .child = try values.get(field.init_value).getType(),
                            }}),
                        });
                        const offset_expr = try values.insert(.{.unsigned_int = .{
                            .bits = 64,
                            .value = try lhs_struct.offsetOf(struct_fields.getIndex(field)),
                        }});
                        const addr_of_expr = if(types.get(try decayValueType(lhs)).* == .pointer) lhs else
                            try Value.fromExpression(try expressions.insert(.{.addr_of = lhs}), member_ptr);
                        const member_ref = try values.addDedupLinear(.{
                            .type_idx = try types.addDedupLinear(.{.reference = .{
                                .is_const = !decl.mutable,
                                .is_volatile = false,
                                .child = try values.get(field.init_value).getType(),
                            }}),
                        });
                        const add_expr = try Value.fromExpression(try expressions.insert(.{.add = .{.lhs = addr_of_expr, .rhs = offset_expr}}), member_ptr);
                        return values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = add_expr})),
                            .value_type = member_ref,
                        }});
                    } else {
                        if(try scopes.get(lhs_struct.scope).lookupDecl(token.identifier_value())) |static_decl| {
                            try values.get(static_decl.init_value).analyze();
                            const fn_value = &values.get(static_decl.init_value).function;
                            const first_param = decls.getOpt(scopes.get(fn_value.generic_param_scope).first_decl).?;
                            std.debug.assert(!first_param.comptime_param);

                            const param_type_value = values.get(first_param.init_value).runtime.value_type;
                            const param_type = switch(values.get(param_type_value).*) {
                                .unresolved => |ur| try semaASTExpr(scope_idx, ur.expression, true, .type, null),
                                else => param_type_value,
                            };

                            const first_param_is_ptr = types.get(values.get(param_type).type_idx).* == .pointer;
                            if(lhs_type.* != .pointer and first_param_is_ptr) {
                                return values.insert(.{.bound_fn = .{
                                    .callee = static_decl.init_value,
                                    .first_arg = try ast.expressions.insert(.{.function_argument = .{
                                        .value = try ast.expressions.insert(.{.addr_of = .{.operand = bop.lhs}}),
                                    }}),
                                }});
                            } else if(lhs_type.* == .pointer and !first_param_is_ptr) {
                                return values.insert(.{.bound_fn = .{
                                    .callee = static_decl.init_value,
                                    .first_arg = try ast.expressions.insert(.{.function_argument = .{
                                        .value = try ast.expressions.insert(.{.deref = .{.operand = bop.lhs}}),
                                    }}),
                                }});
                            } else {
                                return values.insert(.{.bound_fn = .{
                                    .callee = static_decl.init_value,
                                    .first_arg = try ast.expressions.insert(.{.function_argument = .{
                                        .value = bop.lhs,
                                    }}),
                                }});
                            }
                        }
                        return error.MemberNotFound;
                    }
                },
                .type_idx => |idx| {
                    const lhs_type = types.get(idx);
                    const lhs_struct = structs.get(lhs_type.struct_idx);
                    if(try scopes.get(lhs_struct.scope).lookupDecl(token.identifier_value())) |static_decl| {
                        std.debug.assert(static_decl.static);
                        try values.get(static_decl.init_value).analyze();
                        if(!static_decl.mutable) {
                            return static_decl.init_value;
                        }
                        if(static_decl.offset == null) {
                            static_decl.offset = @intCast(u32, try values.get(static_decl.init_value).toBytes());
                        }
                        return values.addDedupLinear(.{.decl_ref = decls.getIndex(static_decl)});
                    } else {
                        std.debug.print("Member not found: {s}\n", .{token.identifier_value()});
                        return error.MemberNotFound;
                    }
                },
                else => |other| std.debug.panic("TODO: member_access of {s}", .{@tagName(other)}),
            }
        },
        .addr_of => |uop| {
            if(force_comptime_eval) @panic("TODO: comptime eval addr_of");
            const operand_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const operand = values.get(operand_idx);
            const result_type = switch(operand.*) {
                .decl_ref => |decl_idx| blk: {
                    const decl = decls.get(decl_idx);
                    if(!decl.static) {
                        decl.offset = @as(u32, undefined);
                    } else {
                        std.debug.assert(decl.offset != null);
                    }
                    break :blk try values.addDedupLinear(.{
                        .type_idx = try types.addDedupLinear(.{.pointer = .{
                            .is_const = !decl.mutable,
                            .is_volatile = false,
                            .child = try operand.getType(),
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

            return values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.addr_of = operand_idx})),
                .value_type = result_type,
            }});
        },
        .deref => |uop| {
            if(force_comptime_eval) @panic("TODO: comptime eval addr_of");
            const operand_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const operand = values.get(operand_idx);
            const operand_type = types.get(try operand.getType());
            std.debug.assert(operand_type.* == .pointer);
            return values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = operand_idx})),
                .value_type = try values.addDedupLinear(.{
                    .type_idx = try types.addDedupLinear(.{.reference = operand_type.pointer})
                }),
            }});
        },
        .array_subscript => |bop| {
            if(force_comptime_eval) @panic("TODO: comptime eval addr_of");
            var lhs_idx = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, null);
            const lhs_type = types.get(try decayValueType(lhs_idx));
            try promote(&lhs_idx, types.getIndex(lhs_type), true);
            const lhs = values.get(lhs_idx);

            const child_type = switch(lhs_type.*) {
                .pointer => |ptr| ptr.child,
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
                        .child = child_type,
                    };
                },
                else => unreachable,
            };

            const size_expr = try values.addDedupLinear(.{.unsigned_int = .{
                .bits = 64,
                .value = @as(i65, @intCast(i64, try types.get(child_type).getSize())),
            }});
            var rhs_idx = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);
            try inplaceOp(size_expr, &rhs_idx, false);
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
            return values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = ptr_expr})),
                .value_type = try values.addDedupLinear(.{
                    .type_idx = try types.addDedupLinear(.{.reference = child_ptr})
                }),
            }});
        },
        .imported_file => |import| {
            const sf = sources.source_files.get(import);
            if(sf.sema_struct == .none) {
                sf.sema_struct = ValueIndex.toOpt(try semaASTExpr(
                    scope_idx,
                    sf.top_level_struct,
                    true,
                    .type,
                    null,
                ));
            }
            return ValueIndex.unwrap(sf.sema_struct).?;
        },
        .type_init_list => |til| blk: {
            var target_type: ?TypeIndex.Index = if(ast.ExprIndex.unwrap(til.specified_type)) |st| inner: {
                const st_value = try semaASTExpr(scope_idx, st, true, .type, null);
                if(type_hint) |th| {
                    if(values.get(st_value).type_idx != th) {
                        @panic("Mismatched type hint and tiv type");
                    }
                }
                break :inner values.get(st_value).type_idx;
            } else type_hint;

            if(target_type) |ttyp| {
                if(return_location_ptr) |rloc| {
                    const new_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
                    const typed = try typeTil(til.first_value, ttyp);
                    var builder = statements.builder();

                    for(typed.slice()) |ass| {
                        var field_type: TypeIndex.Index = undefined;
                        var field_offset: u32 = undefined;

                        switch(types.get(ttyp).*) {
                            .struct_idx => |sidx| {
                                const fidx = @intToEnum(StructFieldIndex.Index, ass.identifier);
                                field_type = try values.get(struct_fields.get(fidx).init_value).getType();
                                field_offset = try structs.get(sidx).offsetOf(fidx);
                            },
                            else => unreachable,
                        }

                        // TODO: Propagate pointer qualifiers
                        const field_pointer_type = try values.addDedupLinear(.{.type_idx = try types.insert(.{.pointer = .{
                            .child = field_type,
                            .is_const = false,
                            .is_volatile = false,
                        }})});

                        const field_reference_type = try values.addDedupLinear(.{.type_idx = try types.insert(.{.reference = .{
                            .child = field_type,
                            .is_const = false,
                            .is_volatile = false,
                        }})});

                        const field_result_location = try values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(try expressions.insert(.{.add = .{
                                .lhs = rloc,
                                .rhs = try values.insert(.{.comptime_int = field_offset}),
                            }})),
                            .value_type = field_pointer_type,
                        }});

                        const value = switch(ass.assignment) {
                            .default => |def| def,
                            .normal => |norm| try semaASTExpr(
                                scope_idx,
                                norm,
                                force_comptime_eval,
                                field_type,
                                field_result_location,
                            ),
                        };

                        _ = try builder.insert(.{.value = .{
                            .expression = try expressions.insert(.{.assign = .{
                                .lhs = try values.insert(.{.runtime = .{
                                    .expr = ExpressionIndex.toOpt(try expressions.insert(.{.deref = field_result_location})),
                                    .value_type = field_reference_type,
                                }}),
                                .rhs = value,
                            }}),
                        }});
                    }

                    break :blk try values.insert(.{.runtime = .{
                        .expr = ExpressionIndex.toOpt(try expressions.insert(.{.block = .{
                            .scope = new_scope_idx,
                            .first_stmt = builder.first,
                            .reaches_end = true,
                        }})),
                        .value_type = try values.addDedupLinear(.{.type_idx = ttyp}),
                    }});
                }
            }
            break :blk try values.insert(.{.type_init = til.first_value});
        },
        .block_expression => |ast_blk| blk: {
            const new_scope_idx = try scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});

            break :blk try values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(try expressions.insert(.{.block = try analyzeStatementChain(
                    new_scope_idx,
                    ast_blk.block,
                    .void,
                    .none,
                )})),
                .value_type = .void,
            }});
        },
        else => |expr| std.debug.panic("Could not evaluate: {any}", .{expr}),
    }, type_hint);
}

const Unresolved = struct {
    analysis_started: bool = false,
    expression: ast.ExprIndex.Index,
    requested_type: ValueIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn evaluate(self: *@This()) !ValueIndex.Index {
        if(self.analysis_started) {
            return error.CircularReference;
        }

        self.analysis_started = true;
        if(values.getOpt(self.requested_type)) |request| {
            const eval_type = switch(request.*) {
                .unresolved => |u| values.get(try semaASTExpr(self.scope, u.expression, true, .type, null)).type_idx,
                .type_idx => |t| t,
                else => unreachable,
            };
            return semaASTExpr(self.scope, self.expression, true, eval_type, null);
        } else {
            return semaASTExpr(self.scope, self.expression, true, null, null);
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
    child: TypeIndex.Index,
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
    type_of_value: ValueIndex.Index,
    array: struct {
        child: TypeIndex.Index,
        size: u32,
    },

    pub fn getSize(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type => 0,
            .anyopaque => error.AnyopaqueHasNoSize,
            .type_of_value => @panic("type_of_value size"),
            .bool => 1,
            .unsigned_int, .signed_int => |bits| @as(u32, 1) << @intCast(u5, std.math.log2_int_ceil(u32, @divTrunc(bits + 7, 8))),
            .pointer, .reference => switch(backends.current_backend.pointer_type) {
                .u64 => 8,
                .u32 => 4,
                .u16 => 2,
                .u8 => 1,
            },
            .array => |arr| try types.get(arr.child).getSize() * arr.size,
            .struct_idx => |struct_idx| try structs.get(struct_idx).offsetOf(null),
        };
    }

    pub fn getAlignment(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type, .anyopaque => 1,
            .type_of_value => @panic("type_of_value align"),
            .bool, .unsigned_int, .signed_int, .pointer, .reference => self.getSize(),
            .struct_idx => |struct_idx| structs.get(struct_idx).getAlignment(),
            .array => |arr| types.get(arr.child).getAlignment(),
        };
    }

    pub fn isContainer(self: @This()) bool {
        return switch(self) {
            .reference => |r| types.get(r.child).isContainer(),
            .void, .undefined, .comptime_int, .type, .anyopaque,
            .bool, .unsigned_int, .signed_int, .pointer,
            => false,
            .struct_idx, .array, .type_of_value,
            => true,
        };
    }

    pub fn writeTo(self: @This(), writer: anytype) !void {
        switch(self) {
            inline
            .void, .anyopaque, .undefined, .bool, .type, .comptime_int,
            => |_, tag| try writer.writeAll(@tagName(tag)),
            .unsigned_int => |bits| try writer.print("u{d}", .{bits}),
            .signed_int => |bits| try writer.print("i{d}", .{bits}),
            .struct_idx => |idx| try writer.print("struct_{d}", .{@enumToInt(idx)}),
            .pointer => |ptr| {
                try writer.writeByte('*');
                if(ptr.is_const) try writer.writeAll("const ");
                if(ptr.is_volatile) try writer.writeAll("volatile ");
                try types.get(ptr.child).writeTo(writer);
            },
            .array => |arr| {
                try writer.print("[{d}]", .{arr.size});
                try types.get(arr.child).writeTo(writer);
            },
            .type_of_value => @panic("TODO: Write out type_of_value"),
            .reference => unreachable,
        }
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
    undefined: ?TypeIndex.Index,
    bool: bool,
    comptime_int: i65,
    unsigned_int: SizedInt,
    signed_int: SizedInt,
    function: Function,
    discard_underscore,
    empty_tuple,
    type_init: ast.TypeInitValueIndex.OptIndex,

    bound_fn: struct {
        callee: ValueIndex.Index,
        first_arg: ast.ExprIndex.Index,
    },

    // Runtime known values
    runtime: RuntimeValue,

    pub fn isComptime(self: *@This()) bool {
        switch(self.*) {
            .type_idx,
            .void,
            .bool,
            .comptime_int,
            .unsigned_int,
            .signed_int,
            .function,
            => return true,
            else => return false,
        }
    }

    pub fn analyze(self: *@This()) anyerror!void {
        switch(self.*) {
            .unresolved => |*u| self.* = values.get(try u.evaluate()).*,
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
            .undefined => |t| t orelse .undefined,
            .bool => .bool,
            .comptime_int => .comptime_int,
            .unsigned_int => |int| try types.addDedupLinear(.{.unsigned_int = int.bits}),
            .signed_int => |int| try types.addDedupLinear(.{.signed_int = int.bits}),
            .runtime => |rt| values.get(rt.value_type).type_idx,
            .decl_ref => |dr| return values.get(decls.get(dr).init_value).getType(),
            .type_init => return types.addDedupLinear(.{.type_of_value = values.getIndex(self)}),
            else => |other| std.debug.panic("TODO: Get type of {s}", .{@tagName(other)}),
        };
    }

    pub fn toBytes(self: *@This()) !usize {
        try self.analyze();
        const retval = backends.writer.currentOffset();
        switch(self.*) {
            .unsigned_int, .signed_int => |*i| {
                const num_bytes = @divTrunc(i.bits + 7, 8);
                // TODO: This assumes little endian
                try backends.writer.write(std.mem.asBytes(&i.value)[0..num_bytes]);
            },
            .undefined => { // TODO: .bss
                const num_bytes = try types.get(try self.getType()).getSize();
                var i: usize = 0;
                while(i < num_bytes) : (i += 1) {
                    try backends.writer.writeInt(u8, 0xAA);
                }
            },
            else => |other| std.debug.panic("TODO: Get bytes from {s} (type {any})", .{@tagName(other), types.get(try self.getType())}),
        }
        return retval;
    }

    pub fn writeTo(self: @This(), writer: anytype) !void {
        return switch(self) {
            .type_idx => |idx| types.get(idx).writeTo(writer),
            inline .unsigned_int, .signed_int => |i| writer.print("{d}", .{i.value}),
            .comptime_int => |i| writer.print("{d}", .{i}),
            else => |other| std.debug.panic("TODO: Write {s}", .{@tagName(other)}),
        };
    }

    fn fromExpression(expression: ExpressionIndex.Index, value_type: ValueIndex.Index) !ValueIndex.Index {
        return values.insert(.{.runtime = .{.expr = ExpressionIndex.toOpt(expression), .value_type = value_type}});
    }
};

pub const Decl = struct {
    mutable: bool,
    static: bool,
    comptime_param: bool,
    offset: ?u32,
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

    pub fn offsetOf(self: *@This(), field_idx: ?StructFieldIndex.Index) anyerror!u32 {
        var offset: u32 = 0;
        var curr_field = self.first_field;
        while(struct_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            const alignment = try field_type.getAlignment();
            offset += alignment - 1;
            offset &= ~(alignment - 1);
            if(field_idx == struct_fields.getIndex(field)) return offset;
            offset += try field_type.getSize();
        }
        std.debug.assert(field_idx == null);
        const alignment = try self.getAlignment();
        offset += alignment - 1;
        offset &= ~(alignment - 1);
        return offset;
    }
};

var func_instantiation_alloc = std.heap.GeneralPurposeAllocator(.{}){
    .backing_allocator = std.heap.page_allocator,
};

pub fn callFunctionWithArgs(fn_idx: ValueIndex.Index, arg_scope: ?ScopeIndex.Index, first_arg: ast.ExprIndex.OptIndex) !FunctionCall {
    const func = &values.get(fn_idx).function;

    var runtime_params_builder = expressions.builderWithPath("function_arg.next");
    if(func.hasComptimeParams()) {
        const new_scope_idx = try scopes.insert(.{.outer_scope = scopes.get(func.generic_param_scope).outer_scope});
        const new_scope = scopes.get(new_scope_idx);
        var scope_builder = decls.builder();

        {
            var curr_param = scopes.get(func.generic_param_scope).first_decl;
            var curr_arg = first_arg;
            while(decls.getOpt(curr_param)) |param| : ({
                curr_param = param.next;
                curr_arg = ast.expressions.getOpt(curr_arg).?.function_argument.next;
            }) {
                const arg = (ast.expressions.getOpt(curr_arg) orelse @panic("Not enough arguments!")).function_argument;

                const param_type = try semaASTExpr(
                    new_scope_idx,
                    values.get(values.get(param.init_value).runtime.value_type).unresolved.expression,
                    true,
                    .type,
                    null,
                );

                var new_param: Decl = .{
                    .mutable = !param.comptime_param,
                    .static = param.comptime_param,
                    .comptime_param = param.comptime_param,
                    .offset = null,
                    .function_param_idx = param.function_param_idx,
                    .name = param.name,
                    .init_value = if(param.comptime_param)
                            try semaASTExpr(arg_scope.?, arg.value, true, values.get(param_type).type_idx, null)
                        else
                            try values.insert(.{.runtime = .{
                                .expr = .none,
                                .value_type = param_type,
                            }}),
                };
                const new_param_idx = try scope_builder.insert(new_param);

                if(!param.comptime_param) {
                    _ = try runtime_params_builder.insert(.{.function_arg = .{
                        .value = try semaASTExpr(arg_scope.?, arg.value, false, values.get(param_type).type_idx, null),
                        .param_decl = new_param_idx,
                    }});
                }

                new_scope.first_decl = scope_builder.first;
            }
            if(curr_arg != .none) @panic("Too many arguments!");
        }

        for(func.instantiations.items) |inst, i| {
            var curr_param = scopes.get(inst.param_scope).first_decl;
            var curr_scope_arg = scopes.get(new_scope_idx).first_decl;

            while(decls.getOpt(curr_param)) |param| : ({
                curr_param = param.next;
                curr_scope_arg = decls.getOpt(curr_scope_arg).?.next;
            }) {
                if(!param.comptime_param) continue;
                const arg = decls.getOpt(curr_scope_arg).?;
                if(param.init_value != arg.init_value) break;
            } else {
                // Patch up the sema decls of the runtime param list to be the ones in the instantiation
                curr_param = scopes.get(inst.param_scope).first_decl;
                var curr_arg = runtime_params_builder.first;
                while(decls.getOpt(curr_param)) |param| : ({
                    curr_param = param.next;
                }) {
                    if(param.comptime_param) continue;
                    const arg = &expressions.getOpt(curr_arg).?.function_arg;
                    arg.param_decl = decls.getIndex(param);
                    curr_arg = arg.next;
                }
                std.debug.assert(curr_arg == .none);

                return .{
                    .callee = .{
                        .function_value = fn_idx,
                        .instantiation = @intCast(u32, i),
                    },
                    .first_arg = runtime_params_builder.first,
                };
            }
        }

        const return_type = try semaASTExpr(new_scope_idx, func.generic_return_type, true, .type, null);
        const instantiation = func.instantiations.items.len;
        try func.instantiations.append(func_instantiation_alloc.allocator(), .{
            .param_scope = new_scope_idx,
            .return_type = return_type,
            .body = undefined,
        });
        func.instantiations.items[instantiation].body = try analyzeStatementChain(
            new_scope_idx,
            func.generic_body,
            values.get(return_type).type_idx,
            .none,
        );

        return .{
            .callee = .{
                .function_value = fn_idx,
                .instantiation = @intCast(u32, instantiation),
            },
            .first_arg = runtime_params_builder.first,
        };
    } else {
        if(func.instantiations.items.len == 0) {
            func.instantiations = try std.ArrayListUnmanaged(Function.Instantation).initCapacity(
                func_instantiation_alloc.allocator(), 1
            );

            var curr_param = scopes.get(func.generic_param_scope).first_decl;
            while(decls.getOpt(curr_param)) |param| : (curr_param = param.next) {
                std.debug.assert(!param.comptime_param);
                const param_rt = &values.get(param.init_value).runtime;
                if(values.get(param_rt.value_type).* == .unresolved) {
                    const param_type = &values.get(param_rt.value_type).unresolved;
                    param_rt.value_type = try semaASTExpr(func.generic_param_scope, param_type.expression, true, .type, null);
                }
            }

            const return_type = try semaASTExpr(func.generic_param_scope, func.generic_return_type, true, .type, null);
            func.instantiations.appendAssumeCapacity(.{
                .param_scope = func.generic_param_scope,
                .return_type = return_type,
                .body = undefined,
            });
            func.instantiations.items[0].body = try analyzeStatementChain(
                func.generic_param_scope,
                func.generic_body,
                values.get(return_type).type_idx,
                .none,
            );
        }
        var curr_param_decl = scopes.get(func.generic_param_scope).first_decl;
        var curr_arg = first_arg;
        while(ast.expressions.getOpt(curr_arg)) |ast_arg| {
            const func_arg = ast_arg.function_argument;
            const curr_param = decls.getOpt(curr_param_decl) orelse return error.TooManyArguments;
            _ = try runtime_params_builder.insert(.{.function_arg = .{
                .value = try semaASTExpr(
                    arg_scope.?,
                    func_arg.value,
                    false,
                    values.get(values.get(curr_param.init_value).runtime.value_type).type_idx,
                    null,
                ),
                .param_decl = decls.getIndex(curr_param),
            }});
            curr_arg = func_arg.next;
            curr_param_decl = curr_param.next;
        }
        if(curr_param_decl != .none) return error.NotEnoughArguments;
        std.debug.assert(func.instantiations.items.len == 1);
        return .{
            .callee = .{
                .function_value = fn_idx,
                .instantiation = 0,
            },
            .first_arg = runtime_params_builder.first,
        };
    }
}

pub const Function = struct {
    ast_function: ast.FunctionIndex.Index,
    generic_return_type: ast.ExprIndex.Index,
    generic_body: ast.StmtIndex.OptIndex,
    generic_param_scope: ScopeIndex.Index,
    instantiations: std.ArrayListUnmanaged(Instantation) = .{},

    fn hasComptimeParams(self: @This()) bool {
        var curr_param = scopes.get(self.generic_param_scope).first_decl;
        while(decls.getOpt(curr_param)) |param| : ({
            curr_param = param.next;
        }) {
            if(param.comptime_param) return true;
        }
        return false;
    }

    const Instantation = struct {
        param_scope: ScopeIndex.Index,
        return_type: ValueIndex.Index,
        body: Block,

        pub fn name(self: @This(), func: *Function, writer: anytype) !void {
            if(func.hasComptimeParams()) {
                var first = true;

                var curr_param_decl = scopes.get(self.param_scope).first_decl;
                while(decls.getOpt(curr_param_decl)) |param| : (curr_param_decl = param.next) {
                    if(!param.comptime_param) continue;

                    if(first) {
                        try writer.writeByte('(');
                    } else {
                        try writer.writeAll(", ");
                    }

                    try values.get(param.init_value).writeTo(writer);

                    first = false;
                }

                if(!first) {
                    try writer.writeByte(')');
                } else {
                    unreachable;
                }
            }
        }
    };
};

pub const Scope = struct {
    outer_scope: ScopeIndex.OptIndex,
    this_type: TypeIndex.OptIndex = .none,
    first_decl: DeclIndex.OptIndex = .none,

    pub fn lookupDecl(self: *@This(), name: []const u8) !?*Decl {
        var scope_idx = ScopeIndex.toOpt(scopes.getIndex(self));
        while(scopes.getOpt(scope_idx)) |scope| : (scope_idx = scope.outer_scope) {
            if(try genericChainLookup(DeclIndex, Decl, &decls, scope.first_decl, name)) |result| {
                return result;
            }
        }
        return null;
    }

    fn getThisType(self: *@This()) ?TypeIndex.Index {
        var scope_idx = ScopeIndex.toOpt(scopes.getIndex(self));
        while(scopes.getOpt(scope_idx)) |scope| : (scope_idx = scope.outer_scope) {
            if(TypeIndex.unwrap(scope.this_type)) |idx| {
                return idx;
            }
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
        unreachable_statement,
        break_statement: StatementIndex.Index,
        return_statement: ValueIndex.OptIndex,
        block: Block,
    },
};

pub const BinaryOp = struct {
    lhs: ValueIndex.Index,
    rhs: ValueIndex.Index,
};

pub const FunctionArgument = struct {
    value: ValueIndex.Index,
    param_decl: DeclIndex.Index,
    next: ExpressionIndex.OptIndex = .none,
};

pub const InstantiatedFunction = struct {
    function_value: ValueIndex.Index,
    instantiation: u32,
};

pub const FunctionCall = struct {
    callee: InstantiatedFunction,
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

    global: struct { offset: u32, type: PointerType },
    addr_of: ValueIndex.Index,
    deref: ValueIndex.Index,

    add: BinaryOp,
    add_eq: BinaryOp,
    sub: BinaryOp,
    sub_eq: BinaryOp,
    multiply: BinaryOp,
    multiply_eq: BinaryOp,
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

    bit_not: ValueIndex.Index,
    logical_not: ValueIndex.Index,

    function_arg: FunctionArgument,
    function_call: FunctionCall,

    block: Block,
};

pub const TypeInitValue = struct {
    field_name: ?ast.SourceRef,
    value: ValueIndex.Index,
    next: TypeInitValueIndex.OptIndex = .none,
};

pub var types: TypeList = undefined;
pub var values: ValueList = undefined;
pub var decls: DeclList = undefined;
pub var struct_fields: StructFieldList = undefined;
pub var structs: StructList = undefined;
pub var scopes: ScopeList = undefined;
pub var statements: StatementList = undefined;
pub var expressions: ExpressionList = undefined;
pub var type_init_values: TypeInitValueList = undefined;

pub fn init() !void {
    types = try TypeList.init(std.heap.page_allocator);
    values = try ValueList.init(std.heap.page_allocator);
    decls = try DeclList.init(std.heap.page_allocator);
    struct_fields = try StructFieldList.init(std.heap.page_allocator);
    structs = try StructList.init(std.heap.page_allocator);
    scopes = try ScopeList.init(std.heap.page_allocator);
    statements = try StatementList.init(std.heap.page_allocator);
    expressions = try ExpressionList.init(std.heap.page_allocator);
    type_init_values = try TypeInitValueList.init(std.heap.page_allocator);

    types.get(.pointer_int).* = switch(backends.current_backend.pointer_type) {
        .u64 => .{.unsigned_int = 64},
        .u32 => .{.unsigned_int = 32},
        .u16 => .{.unsigned_int = 16},
        .u8 => .{.unsigned_int = 8},
    };
}

fn lazyDeclInit(
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

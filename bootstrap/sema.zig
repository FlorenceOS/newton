const std = @import("std");

const ast = @import("ast.zig");
const backends = @import("backends/backends.zig");
const ir = @import("ir.zig");
const indexed_list = @import("indexed_list.zig");
const sources = @import("sources.zig");

pub const TypeIndex = indexed_list.Indices(u32, opaque{}, .{
    .void = .{.void = {}},
    .noreturn = .{.noreturn = {}},
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
    .noreturn = .{.type_idx = .noreturn},
    .bool = .{.type_idx = .bool},
    .type = .{.type_idx = .type},
    .discard_underscore = .{.discard_underscore = {}},
    .u8_type = .{.type_idx = .u8},
    .u16_type = .{.type_idx = .u16},
    .u32_type = .{.type_idx = .u32},
    .u64_type = .{.type_idx = .u64},
    .true = .{.bool = true},
    .false = .{.bool = false},
    .pointer_int_type = .{.type_idx = .pointer_int},
    .syscall_func = .{.function = undefined},
    .undefined = .{.undefined = null},
});
pub const DeclIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const ContainerFieldIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const StructIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const UnionIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const EnumIndex = indexed_list.Indices(u32, opaque{}, .{});
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
const ContainerFieldList = indexed_list.IndexedList(ContainerFieldIndex, ContainerField);
const StructList = indexed_list.IndexedList(StructIndex, Struct);
const UnionList = indexed_list.IndexedList(UnionIndex, Union);
const EnumList = indexed_list.IndexedList(EnumIndex, Enum);
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

fn decay(vidx: *ValueIndex.Index) !void {
    const value = values.get(vidx.*);
    const value_ty = types.get(try value.getType());
    if(value_ty.* == .reference) {
        vidx.* = values.insert(.{.runtime = .{
            .expr = value.runtime.expr,
            .value_type = values.addDedupLinear(.{.type_idx = value_ty.reference.child}),
        }});
    }
}

fn commonType(lhs_ty: TypeIndex.Index, rhs_ty: TypeIndex.Index) !TypeIndex.Index {
    const lhs = types.get(lhs_ty);
    const rhs = types.get(rhs_ty);
    if(std.meta.eql(lhs.*, rhs.*)) return lhs_ty;
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
        sema: ValueIndex.Index,
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
                while(container_fields.getOpt(current_field)) |field| : (current_field = field.next) {
                    const struct_field_name = try field.name.retokenize();
                    defer struct_field_name.deinit();

                    if(std.mem.eql(u8, tiv_field_name.identifier_value(), struct_field_name.identifier_value())) {
                        found_field = true;
                        for(result.slice()) |ass| {
                            if(ass.identifier == @intFromEnum(current_field)) {
                                std.debug.panic("Duplicate field '{s}'", .{tiv_field_name.identifier_value()});
                            }
                        }
                        try result.append(.{
                            .identifier = @intFromEnum(current_field),
                            .assignment = .{.normal = tiv.value},
                        });
                    }
                }

                if(!found_field) {
                    std.debug.panic("Field '{s}' is specified but does not exist in struct type", .{tiv_field_name.identifier_value()});
                }
            }

            var current_field = target_struct.first_field;
            while(container_fields.getOpt(current_field)) |field| : (current_field = field.next) {
                if(for(result.slice()) |ass| {
                    if(ass.identifier == @intFromEnum(current_field)) {
                        break false;
                    }
                } else true) {
                    try result.append(.{
                        .identifier = @intFromEnum(current_field),
                        .assignment = .{.default = field.init_value},
                    });
                }
            }
        },
        .union_idx => |uidx| {
            const target_union = unions.get(uidx);
            if(ast.type_init_values.getOpt(first_value)) |tiv| {
                const tiv_field_name = try tiv.identifier.?.retokenize();
                defer tiv_field_name.deinit();

                var found_field = false;
                var current_field = target_union.first_field;
                while(container_fields.getOpt(current_field)) |field| : (current_field = field.next) {
                    const struct_field_name = try field.name.retokenize();
                    defer struct_field_name.deinit();

                    if(std.mem.eql(u8, tiv_field_name.identifier_value(), struct_field_name.identifier_value())) {
                        found_field = true;
                        try result.append(.{
                            .identifier = @intFromEnum(current_field),
                            .assignment = .{.normal = tiv.value},
                        });
                        break;
                    }
                }

                if(!found_field) {
                    std.debug.panic("Union field '{s}' does not exist", .{tiv_field_name.identifier_value()});
                }

                std.debug.assert(tiv.next == .none);
            }

            if(result.len != 1) {
                std.debug.panic("You need to initialize one of the union fields", .{});
            }
        },
        else => |t| std.debug.panic("typeTil for type {s}", .{@tagName(t)}),
    }

    return result;
}

fn isPointerCompatible(value_type: *Type, target_type: *Type) bool {
    if(target_type.* == .anyopaque) return true;
    if(std.meta.activeTag(value_type.*) != std.meta.activeTag(target_type.*)) return false;
    if(std.meta.eql(value_type.*, target_type.*)) return true;
    switch(target_type.*) {
        .void, .noreturn, .anyopaque, .undefined, .bool, .type, .comptime_int, .reference, .type_of_value,
        => unreachable,

        .signed_int, .unsigned_int, .struct_idx, .union_idx, .enum_idx, .array,
        => return false,

        .pointer => |ptr| {
            // TODO: Check pointer alignment
            if(value_type.pointer.is_volatile != ptr.is_volatile) return false;
            if(value_type.pointer.is_const and !ptr.is_const) return false;
            return isPointerCompatible(types.get(value_type.pointer.child), types.get(ptr.child));
        },
        .function => |func| {
            if(value_type.function.return_type != func.return_type) return false;
            var value_type_param_idx = value_type.function.params;
            var target_type_param_idx = func.params;
            while(type_init_values.getOpt(value_type_param_idx)) |value_type_param| : (value_type_param_idx = value_type_param.next) {
                const target_type_param = type_init_values.getOpt(target_type_param_idx) orelse return false;
                target_type_param_idx = target_type_param.next;
                if(!isPointerCompatible(types.get(values.get(target_type_param.value).type_idx), types.get(values.get(value_type_param.value).type_idx))) return false;
            }
            return true;
        },
    }
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

    if(value.* == .undefined) {
        vidx.* = values.addDedupLinear(.{.undefined = target_tidx});
        return;
    }

    if(ty.* == .pointer) {
        const child_type = types.get(ty.pointer.child);
        switch(value_ty.*) {
            .comptime_int, .unsigned_int, .signed_int => {
                if(is_assign) return error.IncompatibleTypes;
                vidx.* = try Value.fromExpression(
                    expressions.insert(.{.multiply = .{
                        .lhs = vidx.*,
                        .rhs = values.addDedupLinear(.{.comptime_int = try child_type.getSize()}),
                    }}),
                    values.addDedupLinear(.{.type_idx = target_tidx}),
                );
            },
            else => if(!isPointerCompatible(value_ty, ty)) {
                std.debug.panic("Invalid assignment from {any} to pointer type {any}!", .{value_ty.*, ty.*});
            },
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
                .unsigned_int => |bits| vidx.* = values.addDedupLinear(.{.unsigned_int = .{
                    .bits = bits,
                    .value = value.comptime_int,
                }}),
                .signed_int => |bits| vidx.* = values.addDedupLinear(.{.signed_int = .{
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
                expressions.insert(.{.zero_extend = .{.value = vidx.*, .type = target_tidx}}),
                values.addDedupLinear(.{.type_idx = target_tidx}),
            );
        },
        .signed_int => |value_bits| {
            const target_bits = ty.signed_int;
            if(value_bits > target_bits) return error.IncompatibleTypes;
            if(value_bits == target_bits) return;
            vidx.* = try Value.fromExpression(
                expressions.insert(.{.sign_extend = .{.value = vidx.*, .type = target_tidx}}),
                values.addDedupLinear(.{.type_idx = target_tidx}),
            );
        },
        .bool, .type, .void => if(value_ty != ty) return error.IncompatibleTypes,
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
    const block_scope_idx = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(parent_scope_idx)});
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
                const new_decl = decl_builder.insert(.{
                    .mutable = decl.mutable,
                    .static = false,
                    .comptime_param = false,
                    .offset = null,
                    .function_param_idx = null,
                    .name = decl.identifier,
                    .init_value = undefined,
                });
                const decl_ref = values.insert(.{.decl_ref = new_decl});
                const return_location_ptr = values.insert(.{.runtime = .{
                    .expr = ExpressionIndex.toOpt(expressions.insert(.{.addr_of = decl_ref})),
                    .value_type = values.addDedupLinear(.{
                        .type_idx = types.addDedupLinear(.{.pointer = .{
                            .is_const = false,
                            .is_volatile = false,
                            .child = .void,
                        }}),
                    }),
                }});
                var init_value = try semaASTExpr(block_scope_idx, decl.init_value, false, decl_type, return_location_ptr);
                try decay(&init_value);
                decls.get(new_decl).init_value = init_value;
                if(decl_type == null) {
                    decl_type = try values.get(init_value).getType();
                }
                if(types.get(decl_type.?).isContainer()) {
                    decls.get(new_decl).offset = @as(u32, undefined);
                }
                _ = stmt_builder.insert(.{.value = .{.declaration = new_decl}});
                if(block_scope.first_decl == .none) block_scope.first_decl = decl_builder.first;
            },
            .block_statement => |blk| {
                const new_scope = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(block_scope_idx)});
                const block = try analyzeStatementChain(new_scope, blk.first_child, return_type, current_break_block);
                _ = stmt_builder.insert(.{.value = .{.block = block}});
            },
            .expression_statement => |ast_expr| {
                const value = try semaASTExpr(block_scope_idx, ast_expr.expr, false, null, null);
                switch(try values.get(value).getType()) {
                    .noreturn => {
                        reaches_end = false;
                    },
                    else => {},
                }
                const expr = expressions.insert(.{.value = value});
                _ = stmt_builder.insert(.{.value = .{.expression = expr}});
            },
            .if_statement => |if_stmt| {
                const condition = try semaASTExpr(block_scope_idx, if_stmt.condition, false, .bool, null);
                const condition_value = values.get(condition);
                const taken_scope = scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const not_taken_scope = scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                if(condition_value.* == .bool) {
                    if(condition_value.bool) {
                        const taken_block = try analyzeStatementChain(taken_scope, if_stmt.first_taken, return_type, current_break_block);
                        _ = stmt_builder.insert(.{.value = .{.block = taken_block}});
                        reaches_end = taken_block.reaches_end;
                    } else {
                        const not_taken_block = try analyzeStatementChain(not_taken_scope, if_stmt.first_not_taken, return_type, current_break_block);
                        _ = stmt_builder.insert(.{.value = .{.block = not_taken_block}});
                        reaches_end = not_taken_block.reaches_end;
                    }
                } else {
                    const taken_block = try analyzeStatementChain(taken_scope, if_stmt.first_taken, return_type, current_break_block);
                    const not_taken_block = try analyzeStatementChain(not_taken_scope, if_stmt.first_not_taken, return_type, current_break_block);
                    _ = stmt_builder.insert(.{.value = .{.if_statement = .{
                        .condition = condition,
                        .taken = taken_block,
                        .not_taken = not_taken_block,
                    }}});
                    reaches_end = taken_block.reaches_end or not_taken_block.reaches_end;
                }
            },
            .loop_statement => |loop| {
                std.debug.assert(loop.condition == .none);
                const body_scope = scopes.insert(.{
                    .outer_scope = ScopeIndex.toOpt(block_scope_idx),
                });
                const loop_stmt_idx = stmt_builder.insert(.{.value = .{.loop_statement = .{.body = undefined, .breaks = false}}});
                const body = try analyzeStatementChain(body_scope, loop.first_child, return_type, StatementIndex.toOpt(loop_stmt_idx));
                const loop_stmt = statements.get(loop_stmt_idx);
                loop_stmt.value.loop_statement.body = body;
                reaches_end = loop_stmt.value.loop_statement.breaks;
            },
            .break_statement => {
                if(StatementIndex.unwrap(current_break_block)) |break_block| {
                    reaches_end = false;
                    statements.get(break_block).value.loop_statement.breaks = true;
                    _ = stmt_builder.insert(.{.value = .{.break_statement = break_block}});
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
                _ = stmt_builder.insert(.{.value = .{.return_statement =  expr}});
            },
            .unreachable_statement => {
                reaches_end = false;
                _ = stmt_builder.insert(.{.value = .unreachable_statement});
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

    std.debug.assert(fn_call.callee != .runtime);

    const callee = fn_call.callee.instantiation;
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
                    decl.offset = @intCast(try init_value.toBytes());
                }
                break :blk values.addDedupLinear(.{.decl_ref = decls.getIndex(decl)});
            }
            std.debug.print("Cannot find identifier {s}\n", .{token.identifier_value()});
            return error.IdentifierNotFound;
        },
        .discard_underscore => .discard_underscore,
        .parenthesized => |uop| try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, type_hint, return_location_ptr),
        .force_comptime_eval => |uop| blk: {
            if(force_comptime_eval) @panic("Redundant comptime expression, already in comptime context");
            break :blk try semaASTExpr(scope_idx, uop.operand, true, type_hint, null);
        },

        .int_literal => |lit| values.addDedupLinear(.{.comptime_int = (try lit.retokenize()).int_literal.value}),
        .char_literal => |lit| values.addDedupLinear(.{.comptime_int = (try lit.retokenize()).char_literal.value}),
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
            const init_value = values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.global = .{
                    .offset = @intCast(offset),
                    .type = .{
                        .is_volatile = false,
                        .is_const = true,
                        .child = .u8,
                    },
                }})),
                .value_type = values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{
                    .reference = .{.is_const = true, .is_volatile = false, .child = .u8},
                })}),
            }});
            _ = decls.insert(.{
                .mutable = false,
                .static = true,
                .comptime_param = false,
                .offset = @intCast(offset),
                .function_param_idx = null,
                .name = sr,
                .init_value = init_value,
            });
            break :blk init_value;
        },

        .bool_literal => |lit| if(lit) .true else .false,
        .void => .void,
        .bool => .bool,
        .type => .type,
        .noreturn => .noreturn,
        .unsigned_int => |bits| values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.unsigned_int = bits})}),
        .signed_int => |bits| values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.signed_int = bits})}),

        .array_type => |arr| blk: {
            const size = try semaASTExpr(scope_idx, arr.lhs, true, .pointer_int, null);
            const child = try semaASTExpr(scope_idx, arr.rhs, true, .type, null);
            break :blk values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.array = .{
                .child = values.get(child).type_idx,
                .size = @intCast(values.get(size).unsigned_int.value),
            }})});
        },
        .pointer_type => |ptr| blk: {
            const child_type = try semaASTExpr(scope_idx, ptr.child, true, .type, null);
            break :blk values.insert(.{.type_idx = types.addDedupLinear(.{.pointer = .{
                .is_const = ptr.is_const,
                .is_volatile = ptr.is_volatile,
                .child = values.get(child_type).type_idx,
            }})});
        },
        .struct_expression => |type_body| blk: {
            std.debug.assert(type_body.tag_type == .none);
            const struct_scope = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            var decl_builder = decls.builder();
            var field_builder = container_fields.builder();
            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        _ = decl_builder.insert(.{
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
                        _ = field_builder.insert(.{
                            .name = field_decl.identifier,
                            .init_value = if(ast.ExprIndex.unwrap(field_decl.init_value)) |iv|
                                    try semaASTExpr(struct_scope, iv, true, values.get(field_type).type_idx, null)
                                else
                                    values.insert(.{.runtime = .{
                                        .expr = .none,
                                        .value_type = field_type,
                                    }}),
                        });
                    },
                    else => unreachable,
                }

                curr_decl = decl.next;
            }

            const struct_idx = structs.insert(.{
                .first_field = field_builder.first,
                .scope = struct_scope,
            });

            const type_idx = types.insert(.{ .struct_idx = struct_idx });

            scopes.get(struct_scope).first_decl = decl_builder.first;
            scopes.get(struct_scope).this_type = TypeIndex.toOpt(type_idx);

            break :blk values.insert(.{.type_idx = type_idx});
        },
        .union_expression => |type_body| blk: {
            std.debug.assert(type_body.tag_type == .none);
            const union_scope = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            var decl_builder = decls.builder();
            var field_builder = container_fields.builder();
            var curr_decl = type_body.first_decl;
            while(ast.statements.getOpt(curr_decl)) |decl| {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        _ = decl_builder.insert(.{
                            .mutable = inner_decl.mutable,
                            .static = true,
                            .offset = null,
                            .comptime_param = false,
                            .function_param_idx = null,
                            .name = inner_decl.identifier,
                            .init_value = try lazyDeclInit(
                                union_scope,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                        });
                    },
                    .field_decl => |field_decl| {
                        std.debug.assert(field_decl.type != .none);
                        std.debug.assert(field_decl.init_value == .none);
                        const field_type = try semaASTExpr(union_scope, ast.ExprIndex.unwrap(field_decl.type).?, true, .type, null);
                        _ = field_builder.insert(.{
                            .name = field_decl.identifier,
                            .init_value = values.insert(.{.runtime = .{.expr = .none, .value_type = field_type}}),
                        });
                    },
                    else => unreachable,
                }

                curr_decl = decl.next;
            }

            const union_idx = unions.insert(.{
                .first_field = field_builder.first,
                .scope = union_scope,
            });

            const type_idx = types.insert(.{.union_idx = union_idx});

            scopes.get(union_scope).first_decl = decl_builder.first;
            scopes.get(union_scope).this_type = TypeIndex.toOpt(type_idx);

            break :blk values.insert(.{.type_idx = type_idx});
        },
        .enum_expression => |type_body| blk: {
            const enum_scope = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            // FIXME: Properly pick a sufficiently sized backing type, u32 might not be able to hold
            // all possible enum variants a user could provide which might cause errors.
            const backing_type = if(ast.ExprIndex.unwrap(type_body.tag_type)) |tag_type|
                values.get(try semaASTExpr(scope_idx, tag_type, true, .type, null)).type_idx
            else .u32;

            var decl_builder = decls.builder();
            var curr_decl = type_body.first_decl;
            var curr_value = try promoteComptimeInt(0, backing_type);
            var enum_idx = enums.insert(undefined);
            while(ast.statements.getOpt(curr_decl)) |decl| : (curr_decl = decl.next) {
                switch(decl.value) {
                    .declaration => |inner_decl| {
                        _ = decl_builder.insert(.{
                            .mutable = inner_decl.mutable,
                            .static = true,
                            .offset = null,
                            .comptime_param = false,
                            .function_param_idx = null,
                            .name = inner_decl.identifier,
                            .init_value = try lazyDeclInit(
                                enum_scope,
                                ast.ExprIndex.toOpt(inner_decl.init_value),
                                inner_decl.type,
                            ),
                        });
                    },
                    .field_decl => |variant_decl| {
                        if(ast.ExprIndex.unwrap(variant_decl.init_value)) |init_value_idx| {
                            curr_value = try semaASTExpr(scope_idx, init_value_idx, true, backing_type, null);
                        }
                        _ = decl_builder.insert(.{
                            .mutable = false,
                            .static = true,
                            .offset = null,
                            .comptime_param = true,
                            .function_param_idx = null,
                            .name = variant_decl.identifier,
                            .init_value = values.insert(.{.enum_variant = .{
                                .value = curr_value,
                                .enum_type = enum_idx,
                            }}),
                        });
                        // TODO: This could probably be improved upon, but I can't think of a better
                        // way to write this to this will have to do for now.
                        curr_value = try promoteComptimeInt(switch(values.get(curr_value).*) {
                            .comptime_int => |int| int,
                            .unsigned_int, .signed_int => |int| int.value,
                            else => unreachable,
                        } +% 1, backing_type);
                    },
                    else => unreachable,
                }
            }

            enums.get(enum_idx).* = .{
                .backing_type = backing_type,
                .scope = enum_scope,
            };

            const type_idx = types.insert(.{.enum_idx = enum_idx});

            scopes.get(enum_scope).first_decl = decl_builder.first;
            scopes.get(enum_scope).this_type = TypeIndex.toOpt(type_idx);

            break :blk values.insert(.{.type_idx = type_idx});
        },
        .function_expression => |func_idx| blk: {
            const func = ast.functions.get(func_idx);
            const param_scope_idx = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});
            if(func.body == .none) {
                var param_builder = type_init_values.builder();
                var curr_ast_param = func.first_param;
                while(ast.function_params.getOpt(curr_ast_param)) |ast_param| : (curr_ast_param = ast_param.next) {
                    _ = param_builder.insert(.{
                        .field_name = ast_param.identifier,
                        .value = try semaASTExpr(scope_idx, ast_param.type, true, .type, null),
                    });
                }
                break :blk values.insert(.{.type_idx = types.insert(.{.function = .{
                    .params = param_builder.first,
                    .return_type = try semaASTExpr(scope_idx, func.return_type, true, .type, null),
                }})});
            } else if(type_hint != null and type_hint.? == .type) {
                return error.FunctionTypeWithBody;
            }

            const param_scope = scopes.get(param_scope_idx);
            var param_builder = decls.builder();
            var curr_ast_param = func.first_param;
            var function_param_idx: u8 = 0;
            while(ast.function_params.getOpt(curr_ast_param)) |ast_param| : (curr_ast_param = ast_param.next) {
                const param_type = values.insert(.{.unresolved = .{
                    .expression = ast_param.type,
                    .requested_type = .type,
                    .scope = undefined,
                }});
                _ = param_builder.insert(.{
                    .mutable = true,
                    .static = false,
                    .offset = null,
                    .comptime_param = ast_param.is_comptime,
                    .function_param_idx = if(ast_param.is_comptime) null else function_param_idx,
                    .name = ast_param.identifier.?,
                    .init_value = values.insert(.{.runtime = .{.expr = .none, .value_type = param_type}}),
                });
                if(!ast_param.is_comptime) function_param_idx += 1;
            }

            param_scope.first_decl = param_builder.first;

            if(func.return_location) |rloc| {
                const return_location_type = values.insert(.{.unresolved = .{
                    .expression = ast.expressions.insert(.{.pointer_type = .{
                        .is_const = false,
                        .is_volatile = false,
                        .child = func.return_type,
                    }}),
                    .requested_type = .void,
                    .scope = undefined,
                }});
                _ = param_builder.insert(.{
                    .mutable = false,
                    .static = false,
                    .offset = null,
                    .comptime_param = false,
                    .function_param_idx = function_param_idx,
                    .name = rloc,
                    .init_value = values.insert(.{.runtime = .{.expr = .none, .value_type = return_location_type}}),
                });
            }

            break :blk values.insert(.{.function = .{
                .ast_function = func_idx,
                .captures_return = func.return_location != null,
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
                    .This => break :outer values.insert(.{.type_idx = scopes.get(scope_idx).getThisType().?}),
                    .size_of => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(type_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        const type_value = types.get(values.get(ty).type_idx);

                        break :outer values.insert(.{.comptime_int = try type_value.getSize()});
                    },
                    .is_pointer => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(type_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        break :outer values.insert(.{.bool = types.get(values.get(ty).type_idx).* == .pointer});
                    },
                    .int_to_ptr => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        const expr_arg = ast.expressions.getOpt(type_arg.next).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        std.debug.assert(types.get(values.get(ty).type_idx).* == .pointer);
                        const value = try semaASTExpr(scope_idx, expr_arg.value, false, null, null);

                        if(force_comptime_eval) @panic("TODO: Comptime int_to_ptr");
                        break :outer values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(expressions.insert(.{
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
                        break :outer values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(expressions.insert(.{
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

                        break :outer values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(expressions.insert(.{.truncate = .{
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
                            _ = arg_builder.insert(.{.function_arg = .{
                                .value = arg_value,
                                .param_decl = undefined,
                            }});
                            curr_ast_arg = func_arg.next;
                        }
                        return_type = .u64_type;
                        break :inner FunctionCall{
                            .callee = .{.instantiation = .{.function_value = .syscall_func, .instantiation = 0}},
                            .first_arg = arg_builder.first,
                        };
                    },
                    .int_to_enum => {
                        const type_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        const expr_arg = ast.expressions.getOpt(type_arg.next).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        const ty = try semaASTExpr(scope_idx, type_arg.value, true, .type, null);
                        std.debug.assert(types.get(values.get(ty).type_idx).* == .enum_idx);
                        const value = try semaASTExpr(scope_idx, expr_arg.value, false, null, null);
                        switch(types.get(try values.get(value).getType()).*) {
                            .comptime_int, .signed_int, .unsigned_int => {},
                            else => @panic("Can't use @int_to_enum with a non-integer value"),
                        }

                        const target_enum_idx = types.get(values.get(ty).type_idx).enum_idx;
                        if(force_comptime_eval) {
                            break :outer try promoteComptimeInt(switch(values.get(value).*) {
                                .comptime_int => |int| int,
                                .unsigned_int, .signed_int => |int| int.value,
                                else => unreachable,
                            }, enums.get(target_enum_idx).backing_type);
                        } else {
                            break :outer values.insert(.{.runtime = .{
                                .expr = ExpressionIndex.toOpt(expressions.insert(.{.value = value})),
                                .value_type = ty,
                            }});
                        }
                    },
                    .enum_to_int => {
                        const expr_arg = ast.expressions.getOpt(curr_ast_arg).?.function_argument;
                        std.debug.assert(expr_arg.next == .none);

                        var value = try semaASTExpr(scope_idx, expr_arg.value, force_comptime_eval, null, null);
                        if (force_comptime_eval) {
                            try promote(&value, try decayValueType(value), true);
                            std.debug.assert(values.get(value).* != .decl_ref);
                            break :outer values.get(value).enum_variant.value;
                        } else {
                            const value_enum = enums.get(types.get(try decayValueType(value)).enum_idx);
                            break :outer values.insert(.{.runtime = .{
                                .expr = ExpressionIndex.toOpt(expressions.insert(.{.value = value})),
                                .value_type = values.addDedupLinear(.{.type_idx = value_enum.backing_type}),
                            }});
                        }
                    },
                },
                else => inner: {
                    var callee_idx = try semaASTExpr(scope_idx, call.callee, false, null, null);
                    var callee = values.get(callee_idx);
                    switch(callee.*) {
                        .function => {
                            const gen = try callFunctionWithArgs(callee_idx, scope_idx, call.first_arg, return_location_ptr);
                            return_type = callee.function.instantiations.items[gen.callee.instantiation.instantiation].return_type;
                            break :inner gen;
                        },
                        .bound_fn => |b| {
                            ast.expressions.get(b.first_arg).function_argument.next = call.first_arg;
                            const gen = try callFunctionWithArgs(b.callee, scope_idx, ast.ExprIndex.toOpt(b.first_arg), return_location_ptr);
                            return_type = values.get(b.callee).function.instantiations.items[gen.callee.instantiation.instantiation].return_type;
                            break :inner gen;
                        },
                        .decl_ref,
                        .runtime => {
                            try decay(&callee_idx);
                            callee = values.get(callee_idx);
                            const value_type = types.get(try callee.getType());
                            const function_type = types.get(value_type.pointer.child);
                            return_type = function_type.function.return_type;
                            var runtime_params_builder = expressions.builderWithPath("function_arg.next");
                            var curr_param_idx = function_type.function.params;
                            var curr_arg = call.first_arg;
                            while(ast.expressions.getOpt(curr_arg)) |ast_arg| {
                                const func_arg = ast_arg.function_argument;
                                const curr_param = type_init_values.getOpt(curr_param_idx) orelse return error.TooManyArguments;
                                _ = runtime_params_builder.insert(.{.function_arg = .{
                                    .value = try semaASTExpr(scope_idx, func_arg.value, false, values.get(curr_param.value).type_idx, null),
                                    .param_decl = undefined,
                                }});
                                curr_arg = func_arg.next;
                                curr_param_idx = curr_param.next;
                            }
                            if(type_init_values.getOpt(curr_param_idx) != null) return error.NotEnoughArguments;
                            break :inner FunctionCall{.callee = .{.runtime = callee_idx}, .first_arg = runtime_params_builder.first};
                        },
                        else => std.debug.panic("Cannot call non-function: {any}", .{callee}),
                    }
                },
            };
            if(force_comptime_eval) {
                break :outer evaluateComptimeCall(sema_call);
            }
            const value = values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.function_call = sema_call})),
                .value_type = return_type,
            }});
            if(return_location_ptr) |_| {
                return value;
            } else {
                break :outer value;
            }
        },

        .array_concat => |bop| {
            std.debug.assert(!force_comptime_eval);
            const lhs = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, return_location_ptr.?);
            const lhs_type = try values.get(lhs).getType();
            const arr = types.get(lhs_type).array;
            const lhs_ptr_type = types.addDedupLinear(.{.pointer = .{
                .child = lhs_type,
                .is_const = false,
                .is_volatile = false,
            }});
            const lhs_ptr_type_value = values.addDedupLinear(.{.type_idx = lhs_ptr_type});
            const rhs_dest = values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.add = .{
                    .lhs = return_location_ptr.?,
                    .rhs = values.addDedupLinear(.{.comptime_int = try types.get(arr.child).getSize() * arr.size}),
                }})),
                .value_type = lhs_ptr_type_value,
            }});
            const rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, lhs_ptr_type, rhs_dest);
            const rhs_type = types.get(try values.get(rhs).getType()).array;
            std.debug.assert(arr.child == rhs_type.child);
            const combined_type = values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.array = .{
                .child = arr.child,
                .size = arr.size + rhs_type.size,
            }})});

            var builder = statements.builder();

            _ = builder.insert(.{.value = .{
                .expression = expressions.insert(.{.assign = .{
                    .lhs = values.insert(.{.runtime = .{
                        .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = return_location_ptr.?})),
                        .value_type = lhs_ptr_type_value,
                    }}),
                    .rhs = lhs,
                }}),
            }});

            _ = builder.insert(.{.value = .{
                .expression = expressions.insert(.{.assign = .{
                    .lhs = values.insert(.{.runtime = .{
                        .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = rhs_dest})),
                        .value_type = lhs_ptr_type_value,
                    }}),
                    .rhs = rhs,
                }}),
            }});

            return values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.block = .{
                    .scope = scope_idx,
                    .first_stmt = builder.first,
                    .reaches_end = true,
                }})),
                .value_type = combined_type,
            }});
        },

        .unary_minus => |uop| blk: {
            const value_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const value = values.get(value_idx);
            if(value.isComptime()) {
                switch(value.*) {
                    .comptime_int => |int| break :blk values.insert(.{.comptime_int = -int & 0xFFFFFFFFFFFFFFFF}),
                    else => unreachable,
                }
            }
            break :blk try Value.fromExpression(expressions.insert(.{.negate = value_idx}), values.insert(.{.type_idx = try value.getType()}));
        },

        .unary_bitnot => |uop| blk: {
            const value_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const value = values.get(value_idx);
            if(value.isComptime()) {
                switch(value.*) {
                    .comptime_int => |int| break :blk values.insert(.{.comptime_int = ~int & 0xFFFFFFFFFFFFFFFF}),
                    else => unreachable,
                }
            }
            break :blk try Value.fromExpression(expressions.insert(.{.bit_not = value_idx}), values.insert(.{.type_idx = try value.getType()}));
        },

        .unary_lognot => |uop| blk: {
            const value_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, .bool, null);
            const value = values.get(value_idx);
            if(value.isComptime()) {
                switch(value.*) {
                    .bool => |b| break :blk values.addDedupLinear(.{.bool = !b}),
                    else => unreachable,
                }
            }
            break :blk try Value.fromExpression(expressions.insert(.{.logical_not = value_idx}), .bool);
        },

        inline
        .plus, .plus_eq, .minus, .minus_eq, .multiply, .multiply_eq,
        .divide, .divide_eq, .modulus, .modulus_eq,
        .shift_left, .shift_left_eq, .shift_right, .shift_right_eq,
        .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq,
        .less, .less_equal, .greater, .greater_equal,
        .equals, .not_equal, .logical_and, .logical_or,
        .assign, .range,
        => |bop, tag| outer: {
            var lhs = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, null);
            var rhs: ValueIndex.Index = undefined;
            if(tag != .assign) {
                rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);
            }

            const value_type: ValueIndex.Index = switch(tag) {
                .assign => blk: {
                    if(lhs == .discard_underscore) {
                        rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);
                        break :blk .void;
                    }
                    const lhs_tidx = try values.get(lhs).getType();
                    const lhs_type = types.get(lhs_tidx);
                    if(lhs_type.* == .reference) {
                        const target_ptr = values.addDedupLinear(.{
                            .type_idx = types.addDedupLinear(.{.pointer = .{
                                .is_const = false,
                                .is_volatile = lhs_type.reference.is_volatile,
                                .child = lhs_type.reference.child,
                            }}),
                        });
                        const result_loc = try Value.fromExpression(expressions.insert(.{.addr_of = lhs}), target_ptr);
                        rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, lhs_type.reference.child, result_loc);
                        switch(values.get(rhs).*) {
                            .runtime => |rt| inner: {
                                if((expressions.getOpt(rt.expr) orelse break :inner).* == .block) {
                                    // We're done. No promotion needed.
                                    return values.insert(.{.runtime = .{
                                        .expr = ExpressionIndex.toOpt(expressions.insert(.{.assign = .{.lhs = lhs, .rhs = rhs}})),
                                        .value_type = .void,
                                    }});
                                }
                            },
                            else => { },
                        }
                        break :blk .void;
                    } else {
                        rhs = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);
                        try inplaceOp(lhs, &rhs, true);
                        break :blk .void;
                    }
                },
                .plus_eq, .minus_eq, .multiply_eq, .divide_eq, .modulus_eq,
                .shift_left_eq, .shift_right_eq, .bitand_eq, .bitxor_eq, .bitor_eq,
                => blk: {
                    try inplaceOp(lhs, &rhs, false);
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
                    break :blk values.addDedupLinear(.{.type_idx = try values.get(lhs).getType()});
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
                break :outer values.insert(switch(tag) {
                    .plus => .{.comptime_int = lhs_int +% rhs_int},
                    .minus => .{.comptime_int = lhs_int -% rhs_int},
                    .multiply => .{.comptime_int = lhs_int *% rhs_int},
                    .divide => .{.comptime_int = @divTrunc(lhs_int, rhs_int)},
                    .modulus => .{.comptime_int = @rem(lhs_int, rhs_int)},
                    .shift_left => .{.comptime_int = lhs_int << @as(u7, @intCast(rhs_int))},
                    .shift_right => .{.comptime_int = lhs_int >> @as(u7, @intCast(rhs_int))},
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

            break :outer values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(
                    @unionInit(Expression, sema_tag, .{.lhs = lhs, .rhs = rhs}),
                )),
                .value_type = value_type,
            }});
        },
        .member_access => |bop| blk: {
            var lhs = try semaASTExpr(scope_idx, bop.lhs, force_comptime_eval, null, null);
            try decay(&lhs);
            const lhs_value = values.get(lhs);
            const rhs_expr = ast.expressions.get(bop.rhs);
            std.debug.assert(rhs_expr.* == .identifier);
            const token = try rhs_expr.identifier.retokenize();
            defer token.deinit();
            switch(lhs_value.*) {
                .runtime, .decl_ref => {
                    const lhs_type = types.get(try lhs_value.getType());
                    const mutable = switch(lhs_value.*) {
                        .decl_ref => |dr| decls.get(dr).mutable,
                        else => switch(lhs_type.*) {
                            .pointer => |pt| !pt.is_const,
                            else => false,
                        },
                    };
                    const field_or_decl = try getFieldOrDecl(lhs, token.identifier_value());
                    if(field_or_decl == null) {
                        return error.MemberNotFound;
                    }
                    switch(field_or_decl.?) {
                        .field => |field| {
                            if(force_comptime_eval) @panic("TODO: Comptime eval field access");
                            const member_ptr = values.addDedupLinear(.{
                                .type_idx = types.addDedupLinear(.{.pointer = .{
                                    .is_const = !mutable,
                                    .is_volatile = false,
                                    .child = try values.get(field.field.init_value).getType(),
                                }}),
                            });
                            const offset_expr = values.insert(.{.unsigned_int = .{
                                .bits = 64,
                                .value = field.offset,
                            }});
                            const addr_of_expr = if(types.get(try decayValueType(lhs)).* == .pointer) lhs else
                                try Value.fromExpression(expressions.insert(.{.addr_of = lhs}), member_ptr);
                            const member_ref = values.addDedupLinear(.{
                                .type_idx = types.addDedupLinear(.{.reference = .{
                                    .is_const = !mutable,
                                    .is_volatile = false,
                                    .child = try values.get(field.field.init_value).getType(),
                                }}),
                            });
                            const add_expr = try Value.fromExpression(expressions.insert(.{.add = .{.lhs = addr_of_expr, .rhs = offset_expr}}), member_ptr);
                            break :blk values.insert(.{.runtime = .{
                                .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = add_expr})),
                                .value_type = member_ref,
                            }});
                        },
                        .decl => |decl| {
                            try values.get(decl.init_value).analyze();
                            const fn_value = &values.get(decl.init_value).function;
                            const first_param = decls.getOpt(scopes.get(fn_value.generic_param_scope).first_decl).?;
                            std.debug.assert(!first_param.comptime_param);

                            const param_type_value = values.get(first_param.init_value).runtime.value_type;
                            const param_type = switch(values.get(param_type_value).*) {
                                .unresolved => |ur| try semaASTExpr(scope_idx, ur.expression, true, .type, null),
                                else => param_type_value,
                            };

                            const first_param_is_ptr = types.get(values.get(param_type).type_idx).* == .pointer;
                            if(lhs_type.* != .pointer and first_param_is_ptr) {
                                break :blk values.insert(.{.bound_fn = .{
                                    .callee = decl.init_value,
                                    .first_arg = ast.expressions.insert(.{.function_argument = .{
                                        .value = ast.expressions.insert(.{.addr_of = .{.operand = bop.lhs}}),
                                    }}),
                                }});
                            } else if(lhs_type.* == .pointer and !first_param_is_ptr) {
                                break :blk values.insert(.{.bound_fn = .{
                                    .callee = decl.init_value,
                                    .first_arg = ast.expressions.insert(.{.function_argument = .{
                                        .value = ast.expressions.insert(.{.deref = .{.operand = bop.lhs}}),
                                    }}),
                                }});
                            } else {
                                break :blk values.insert(.{.bound_fn = .{
                                    .callee = decl.init_value,
                                    .first_arg = ast.expressions.insert(.{.function_argument = .{
                                        .value = bop.lhs,
                                    }}),
                                }});
                            }
                        },
                    }
                },
                .type_idx => |idx| {
                    const lhs_type = types.get(idx);
                    var decl: ?*Decl = null;
                    switch(lhs_type.*) {
                        .struct_idx => |struct_idx| {
                            const lhs_struct = structs.get(struct_idx);
                            decl = try scopes.get(lhs_struct.scope).lookupDecl(token.identifier_value());
                        },
                        .enum_idx => |enum_idx| {
                            const lhs_enum = enums.get(enum_idx);
                            decl = try scopes.get(lhs_enum.scope).lookupDecl(token.identifier_value());
                        },
                        else => unreachable,
                    }
                    if(decl) |static_decl| {
                        std.debug.assert(static_decl.static);
                        try values.get(static_decl.init_value).analyze();
                        if(!static_decl.mutable) {
                            break :blk static_decl.init_value;
                        }
                        if(static_decl.offset == null) {
                            static_decl.offset = @intCast(try values.get(static_decl.init_value).toBytes());
                        }
                        break :blk values.addDedupLinear(.{.decl_ref = decls.getIndex(static_decl)});
                    } else {
                        std.debug.print("Member not found: {s}\n", .{token.identifier_value()});
                        return error.MemberNotFound;
                    }
                },
                else => |other| std.debug.panic("TODO: member_access of {s}", .{@tagName(other)}),
            }
        },
        .addr_of => |uop| outer: {
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
                    break :blk values.addDedupLinear(.{
                        .type_idx = types.addDedupLinear(.{.pointer = .{
                            .is_const = !decl.mutable,
                            .is_volatile = false,
                            .child = try operand.getType(),
                        }}),
                    });
                },
                .runtime => |rt| blk: {
                    const value_type = types.get(values.get(rt.value_type).type_idx);
                    std.debug.assert(value_type.* == .reference);
                    break :blk values.addDedupLinear(.{
                        .type_idx = types.addDedupLinear(.{.pointer = value_type.reference}),
                    });
                },
                .function => blk: {
                    _ = try generateExternRef(operand_idx);
                    break : blk values.addDedupLinear(.{
                        .type_idx = types.addDedupLinear(.{.pointer = .{
                            .is_const = true,
                            .is_volatile = false,
                            .child = try values.get(operand_idx).getType(),
                        }}),
                    });
                },
                else => |other| std.debug.panic("Can't take the addr of {s}", .{@tagName(other)}),
            };

            break :outer values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.addr_of = operand_idx})),
                .value_type = result_type,
            }});
        },
        .deref => |uop| blk: {
            if(force_comptime_eval) @panic("TODO: comptime eval addr_of");
            const operand_idx = try semaASTExpr(scope_idx, uop.operand, force_comptime_eval, null, null);
            const operand = values.get(operand_idx);
            const operand_type = types.get(try operand.getType());
            std.debug.assert(operand_type.* == .pointer);
            break :blk values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = operand_idx})),
                .value_type = values.addDedupLinear(.{
                    .type_idx = types.addDedupLinear(.{.reference = operand_type.pointer})
                }),
            }});
        },
        .array_subscript => |bop| outer: {
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
                    switch(lhs.*) {
                        .runtime => |rt| {
                            const ref = types.get(values.get(rt.value_type).type_idx).reference;
                            break :blk PointerType{
                                .is_const = ref.is_const,
                                .is_volatile = ref.is_volatile,
                                .child = child_type,
                            };
                        },
                        .decl_ref => |dr| {
                            const decl = decls.get(dr);
                            break :blk PointerType{
                                .is_const = !decl.mutable,
                                .is_volatile = false,
                                .child = child_type,
                            };
                        },
                        else => |o| std.debug.panic("wtf {s}", .{@tagName(o)}),
                    }
                },
                else => unreachable,
            };

            const size_expr = values.addDedupLinear(.{.unsigned_int = .{
                .bits = 64,
                .value = @as(i65, @as(i64, @intCast(try types.get(child_type).getSize()))),
            }});
            var rhs_idx = try semaASTExpr(scope_idx, bop.rhs, force_comptime_eval, null, null);
            try inplaceOp(size_expr, &rhs_idx, false);
            const rhs = values.get(rhs_idx);
            const rhs_type = types.get(try rhs.getType());
            std.debug.assert(rhs_type.* == .signed_int or rhs_type.* == .unsigned_int or rhs_type.* == .comptime_int);
            const pointer_expr = if(lhs_type.* != .pointer) blk: {
                break :blk try Value.fromExpression(
                    expressions.insert(.{.addr_of = lhs_idx}),
                     values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.pointer = child_ptr})}),
                );
            } else lhs_idx;
            const offset_expr = try Value.fromExpression(
                expressions.insert(.{.multiply = .{.lhs = rhs_idx, .rhs = size_expr}}),
                 .pointer_int_type,
            );
            const ptr_expr = try Value.fromExpression(
                expressions.insert(.{.add = .{.lhs = pointer_expr, .rhs = offset_expr}}),
                 values.addDedupLinear(.{.type_idx = types.addDedupLinear(.{.pointer = child_ptr})}),
            );
            break :outer values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = ptr_expr})),
                .value_type = values.addDedupLinear(.{
                    .type_idx = types.addDedupLinear(.{.reference = child_ptr})
                }),
            }});
        },
        .imported_file => |import| blk: {
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
            break :blk ValueIndex.unwrap(sf.sema_struct).?;
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
                var typed = try typeTil(til.first_value, ttyp);
                if(return_location_ptr) |rloc| {
                    var builder = statements.builder();
                    for(typed.slice()) |ass| {
                        var field_type: TypeIndex.Index = undefined;
                        var field_offset: u32 = undefined;

                        const fidx: ContainerFieldIndex.Index = @enumFromInt(ass.identifier);
                        switch(types.get(ttyp).*) {
                            .struct_idx => |sidx| {
                                field_type = try values.get(container_fields.get(fidx).init_value).getType();
                                field_offset = try structs.get(sidx).offsetOf(fidx);
                            },
                            .union_idx => {
                                field_type = try values.get(container_fields.get(fidx).init_value).getType();
                                field_offset = 0;
                            },
                            else => unreachable,
                        }

                        // TODO: Propagate pointer qualifiers
                        const field_pointer_type = values.addDedupLinear(.{.type_idx = types.insert(.{.pointer = .{
                            .child = field_type,
                            .is_const = false,
                            .is_volatile = false,
                        }})});

                        const field_reference_type = values.addDedupLinear(.{.type_idx = types.insert(.{.reference = .{
                            .child = field_type,
                            .is_const = false,
                            .is_volatile = false,
                        }})});

                        const field_result_location = values.insert(.{.runtime = .{
                            .expr = ExpressionIndex.toOpt(expressions.insert(.{.add = .{
                                .lhs = rloc,
                                .rhs = values.insert(.{.comptime_int = field_offset}),
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
                            .sema => unreachable,
                        };

                        _ = builder.insert(.{.value = .{
                            .expression = expressions.insert(.{.assign = .{
                                .lhs = values.insert(.{.runtime = .{
                                    .expr = ExpressionIndex.toOpt(expressions.insert(.{.deref = field_result_location})),
                                    .value_type = field_reference_type,
                                }}),
                                .rhs = value,
                            }}),
                        }});
                    }

                    break :blk values.insert(.{.runtime = .{
                        .expr = ExpressionIndex.toOpt(expressions.insert(.{.block = .{
                            .scope = scope_idx,
                            .first_stmt = builder.first,
                            .reaches_end = true,
                        }})),
                        .value_type = values.addDedupLinear(.{.type_idx = ttyp}),
                    }});
                } else {
                    for(typed.slice()) |*ass| {
                        switch(ass.assignment) {
                            .normal => |expr| {
                                std.debug.assert(types.get(ttyp).* == .struct_idx);
                                const field = container_fields.get(@enumFromInt(ass.identifier));
                                ass.assignment = .{.sema = try semaASTExpr(scope_idx, expr, false, try values.get(field.init_value).getType(), null)};
                            },
                            .default => {},
                            .sema => unreachable,
                        }
                    }

                    break :blk values.insert(.{.typed_til = .{
                        .init_type = ttyp,
                        .values = try til_allocator.allocator().dupe(TilAssignment, typed.slice()),
                    }});
                }
            }
            break :blk values.insert(.{.type_init = til.first_value});
        },
        .block_expression => |ast_blk| blk: {
            const new_scope_idx = scopes.insert(.{.outer_scope = ScopeIndex.toOpt(scope_idx)});

            break :blk values.insert(.{.runtime = .{
                .expr = ExpressionIndex.toOpt(expressions.insert(.{.block = try analyzeStatementChain(
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
    noreturn,
    anyopaque,
    undefined,
    bool,
    type,
    comptime_int,
    unsigned_int: u32,
    signed_int: u32,
    struct_idx: StructIndex.Index,
    union_idx: UnionIndex.Index,
    enum_idx: EnumIndex.Index,
    pointer: PointerType,
    reference: PointerType,
    type_of_value: ValueIndex.Index,
    function: struct {
        params: TypeInitValueIndex.OptIndex,
        return_type: ValueIndex.Index,
    },
    array: struct {
        child: TypeIndex.Index,
        size: u32,
    },

    pub fn getSize(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type, .noreturn => 0,
            .anyopaque => error.AnyopaqueHasNoSize,
            .type_of_value => @panic("type_of_value size"),
            .bool => 1,
            .unsigned_int, .signed_int => |bits| @as(u32, 1) << @as(u5, @intCast(std.math.log2_int_ceil(u32, @divTrunc(bits + 7, 8)))),
            .pointer, .reference => switch(backends.current_backend.pointer_type) {
                .u64 => 8,
                .u32 => 4,
                .u16 => 2,
                .u8 => 1,
            },
            .array => |arr| try types.get(arr.child).getSize() * arr.size,
            .struct_idx => |struct_idx| try structs.get(struct_idx).offsetOf(null),
            .union_idx => |union_idx| blk: {
                var biggest_field: u32 = 0;
                var curr_field = unions.get(union_idx).first_field;
                while(container_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
                    const field_type = try values.get(field.init_value).getType();
                    const field_size = try types.get(field_type).getSize();
                    if(field_size > biggest_field) {
                        biggest_field = field_size;
                    }
                }
                break :blk biggest_field;
            },
            .enum_idx => |enum_idx| try types.get(enums.get(enum_idx).backing_type).getSize(),
            .function => 0,
        };
    }

    pub fn getAlignment(self: @This()) !u32 {
        return switch(self) {
            .void, .undefined, .comptime_int, .type, .anyopaque, .noreturn => 1,
            .type_of_value => @panic("type_of_value align"),
            .bool, .unsigned_int, .signed_int, .pointer, .reference => self.getSize(),
            .struct_idx => |struct_idx| structs.get(struct_idx).getAlignment(),
            .union_idx => |union_idx| unions.get(union_idx).getAlignment(),
            .enum_idx => |enum_idx| types.get(enums.get(enum_idx).backing_type).getAlignment(),
            .array => |arr| types.get(arr.child).getAlignment(),
            .function => 0,
        };
    }

    pub fn isContainer(self: @This()) bool {
        return switch(self) {
            .reference => |r| types.get(r.child).isContainer(),
            .void, .undefined, .comptime_int, .type, .anyopaque,
            .bool, .unsigned_int, .signed_int, .pointer, .noreturn,
            .function, .enum_idx,
            => false,
            .struct_idx, .union_idx, .array, .type_of_value,
            => true,
        };
    }

    pub fn writeTo(self: @This(), writer: anytype) !void {
        switch(self) {
            inline
            .void, .anyopaque, .undefined, .bool, .type, .comptime_int, .noreturn,
            => |_, tag| try writer.writeAll(@tagName(tag)),
            .unsigned_int => |bits| try writer.print("u{d}", .{bits}),
            .signed_int => |bits| try writer.print("i{d}", .{bits}),
            .struct_idx => |idx| try writer.print("struct_{d}", .{@intFromEnum(idx)}),
            .union_idx => |idx| try writer.print("union_{d}", .{@intFromEnum(idx)}),
            .enum_idx => |idx| try writer.print("enum_{d}", .{@intFromEnum(idx)}),
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
            .function => try writer.print("function_type", .{}),
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
    enum_variant: struct {
        value: ValueIndex.Index,
        enum_type: EnumIndex.Index,
    },
    function: Function,
    discard_underscore,
    empty_tuple,
    type_init: ast.TypeInitValueIndex.OptIndex,
    typed_til: struct {
        init_type: TypeIndex.Index,
        values: []TilAssignment,
    },

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
            .unsigned_int => |int| types.addDedupLinear(.{.unsigned_int = int.bits}),
            .signed_int => |int| types.addDedupLinear(.{.signed_int = int.bits}),
            .enum_variant => |ev| types.addDedupLinear(.{.enum_idx = ev.enum_type}),
            .runtime => |rt| values.get(rt.value_type).type_idx,
            .decl_ref => |dr| return values.get(decls.get(dr).init_value).getType(),
            .type_init => return types.addDedupLinear(.{.type_of_value = values.getIndex(self)}),
            .typed_til => |ti| ti.init_type,
            .function => |func| {
                std.debug.assert(!func.hasComptimeParams());
                var param_builder = type_init_values.builder();
                var curr_param = scopes.get(func.generic_param_scope).first_decl;
                while(decls.getOpt(curr_param)) |param| : (curr_param = param.next) {
                    _ = param_builder.insert(.{
                        .field_name = param.name,
                        .value = values.addDedupLinear(.{.type_idx = try values.get(param.init_value).getType()}),
                    });
                }
                return types.insert(.{.function = .{
                    .params = param_builder.first,
                    .return_type = try semaASTExpr(func.generic_param_scope, func.generic_return_type, true, .type, null),
                }});
            },
            else => |other| std.debug.panic("TODO: Get type of {s}", .{@tagName(other)}),
        };
    }

    fn writeBytesAtOffset(self: *@This(), offset: usize) !void {
        switch(self.*) {
            .undefined => {}, // TODO: .bss
            .unsigned_int, .signed_int => |*i| { // TODO: This assumes little endian
                const num_bytes = @divTrunc(i.bits + 7, 8);
                std.mem.copy(u8, backends.writer.output_bytes.items[offset..][0..num_bytes], std.mem.asBytes(&i.value)[0..num_bytes]);
            },
            .typed_til => |ti| {
                var init_type = structs.get(types.get(ti.init_type).struct_idx);
                for(ti.values) |value| {
                    switch(value.assignment) {
                        .sema, .default => |val| try values.get(val).writeBytesAtOffset(try init_type.offsetOf(@enumFromInt(value.identifier))),
                        .normal => unreachable,
                    }
                }
            },
            else => |other| std.debug.panic("TODO: Get bytes from {s} (type {any})", .{@tagName(other), types.get(try self.getType())}),
        }
    }

    pub fn toBytes(self: *@This()) !usize {
        const offset = backends.writer.currentOffset();
        try backends.writer.output_bytes.appendNTimes(backends.writer.allocator, 0xAA, try types.get(try self.getType()).getSize());
        try self.writeBytesAtOffset(offset);
        return offset;
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

pub const ContainerField = struct {
    name: ast.SourceRef,
    init_value: ValueIndex.Index,
    next: ContainerFieldIndex.OptIndex = .none,
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
    first_field: ContainerFieldIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn lookupField(self: *@This(), name: []const u8) !?*ContainerField {
        return genericChainLookup(ContainerFieldIndex, ContainerField, &container_fields, self.first_field, name);
    }

    pub fn getAlignment(self: *@This()) anyerror!u32 {
        var alignment: u32 = 0;
        var curr_field = self.first_field;
        while(container_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            alignment = @max(alignment, try field_type.getAlignment());
        }
        return alignment;
    }

    pub fn offsetOf(self: *@This(), field_idx: ?ContainerFieldIndex.Index) anyerror!u32 {
        var offset: u32 = 0;
        var curr_field = self.first_field;
        while(container_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            const alignment = try field_type.getAlignment();
            offset += alignment - 1;
            offset &= ~(alignment - 1);
            if(field_idx == container_fields.getIndex(field)) return offset;
            offset += try field_type.getSize();
        }
        std.debug.assert(field_idx == null);
        const alignment = try self.getAlignment();
        offset += alignment - 1;
        offset &= ~(alignment - 1);
        return offset;
    }
};

pub const Union = struct {
    first_field: ContainerFieldIndex.OptIndex,
    scope: ScopeIndex.Index,

    pub fn lookupField(self: *@This(), name: []const u8) !?*ContainerField {
        return genericChainLookup(ContainerFieldIndex, ContainerField, &container_fields, self.first_field, name);
    }

    pub fn getAlignment(self: *@This()) anyerror!u32 {
        var alignment: u32 = 0;
        var curr_field = self.first_field;
        while(container_fields.getOpt(curr_field)) |field| : (curr_field = field.next) {
            const field_type = types.get(try values.get(field.init_value).getType());
            alignment = @max(alignment, try field_type.getAlignment());
        }
        return alignment;
    }
};

pub const Enum = struct {
    backing_type: TypeIndex.Index,
    scope: ScopeIndex.Index,
};

var func_instantiation_alloc = std.heap.GeneralPurposeAllocator(.{}){
    .backing_allocator = std.heap.page_allocator,
};

pub fn callFunctionWithArgs(fn_idx: ValueIndex.Index, arg_scope: ?ScopeIndex.Index, first_arg: ast.ExprIndex.OptIndex, return_location: ?ValueIndex.Index) !FunctionCall {
    const func = &values.get(fn_idx).function;

    var runtime_params_builder = expressions.builderWithPath("function_arg.next");
    if(func.hasComptimeParams()) {
        const new_scope_idx = scopes.insert(.{.outer_scope = scopes.get(func.generic_param_scope).outer_scope});
        const new_scope = scopes.get(new_scope_idx);
        var scope_builder = decls.builder();

        {
            var curr_param = scopes.get(func.generic_param_scope).first_decl;
            var curr_arg = first_arg;
            while(decls.getOpt(curr_param)) |param| : (blk: {
                curr_param = param.next;
                curr_arg = (ast.expressions.getOpt(curr_arg) orelse break :blk).function_argument.next;
            }) {
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
                        try semaASTExpr(
                            arg_scope.?,
                            ast.expressions.getOpt(curr_arg).?.function_argument.value,
                            true,
                            values.get(param_type).type_idx,
                            null,
                        ) else values.insert(.{.runtime = .{
                            .expr = .none,
                            .value_type = param_type,
                        }}),
                };
                const new_param_idx = scope_builder.insert(new_param);

                if(!param.comptime_param) {
                    _ = runtime_params_builder.insert(.{.function_arg = .{
                        .value = if(ast.expressions.getOpt(curr_arg)) |arg| try semaASTExpr(
                            arg_scope.?,
                            arg.function_argument.value,
                            false,
                            values.get(param_type).type_idx,
                            null
                        ) else return_location.?,
                        .param_decl = new_param_idx,
                    }});
                }

                new_scope.first_decl = scope_builder.first;
            }
            if(curr_arg != .none) @panic("Too many arguments!");
        }

        for(func.instantiations.items, 0..) |inst, i| {
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
                    .callee = .{.instantiation = .{.function_value = fn_idx, .instantiation = @intCast(i)}},
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
            .callee = .{.instantiation = .{.function_value = fn_idx, .instantiation = @intCast(instantiation)}},
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
                if(func.captures_return) .void else values.get(return_type).type_idx,
                .none,
            );
        }
        var curr_param_decl = scopes.get(func.generic_param_scope).first_decl;
        var curr_arg = first_arg;
        while(ast.expressions.getOpt(curr_arg)) |ast_arg| {
            const func_arg = ast_arg.function_argument;
            const curr_param = decls.getOpt(curr_param_decl) orelse return error.TooManyArguments;
            _ = runtime_params_builder.insert(.{.function_arg = .{
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
        if(decls.getOpt(curr_param_decl)) |curr_param| {
            if(return_location) |rloc| {
                _ = runtime_params_builder.insert(.{.function_arg = .{
                    .value = rloc,
                    .param_decl = decls.getIndex(curr_param),
                }});
            } else {
                return error.NotEnoughArguments;
            }
        }
        std.debug.assert(func.instantiations.items.len == 1);
        return .{
            .callee = .{.instantiation = .{.function_value = fn_idx, .instantiation = 0}},
            .first_arg = runtime_params_builder.first,
        };
    }
}

var undefined_arg_list: ast.ExprIndex.OptIndex = .none;
var num_undefineds: usize = 0;

// Call a function with no comptime parameters with a bunch of undefined values.
// Used to analyze a function without a call site.
// Can be used for exporting extern function decls, entry points or function pointers.
pub fn generateExternRef(fn_idx: ValueIndex.Index) !InstantiatedFunction {
    const func = values.get(fn_idx).function;

    var argument_count: usize = 0;

    var curr_param = scopes.get(func.generic_param_scope).first_decl;
    while(decls.getOpt(curr_param)) |param| : (curr_param = param.next) {
        std.debug.assert(!param.comptime_param);
        argument_count += 1;
    }

    while(num_undefineds < argument_count) {
        undefined_arg_list = ast.ExprIndex.toOpt(ast.expressions.insert(.{.function_argument = .{
            .value = .undefined,
            .next = undefined_arg_list,
        }}));
        num_undefineds += 1;
    }

    var arg_list = undefined_arg_list;
    var arg_list_count = num_undefineds;
    while(argument_count < arg_list_count) {
        arg_list = ast.expressions.getOpt(arg_list).?.function_argument.next;
        arg_list_count -= 1;
    }

    const result = try callFunctionWithArgs(fn_idx, @as(ScopeIndex.Index, undefined), arg_list, null);
    return result.callee.instantiation;
}

pub const Function = struct {
    ast_function: ast.FunctionIndex.Index,
    captures_return: bool,
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
    callee: union(enum) {
        instantiation: InstantiatedFunction,
        runtime: ValueIndex.Index,
    },
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
    negate: ValueIndex.Index,

    function_arg: FunctionArgument,
    function_call: FunctionCall,

    block: Block,
};

pub const TypeInitValue = struct {
    field_name: ?ast.SourceRef,
    value: ValueIndex.Index,
    next: TypeInitValueIndex.OptIndex = .none,
};

var til_allocator = std.heap.ArenaAllocator.init(std.heap.page_allocator);

pub var types: TypeList = undefined;
pub var values: ValueList = undefined;
pub var decls: DeclList = undefined;
pub var container_fields: ContainerFieldList = undefined;
pub var structs: StructList = undefined;
pub var unions: UnionList = undefined;
pub var enums: EnumList = undefined;
pub var scopes: ScopeList = undefined;
pub var statements: StatementList = undefined;
pub var expressions: ExpressionList = undefined;
pub var type_init_values: TypeInitValueList = undefined;

pub fn init() !void {
    types = try TypeList.init(std.heap.page_allocator, 0x1000);
    values = try ValueList.init(std.heap.page_allocator, 0x100000);
    decls = try DeclList.init(std.heap.page_allocator, 0x10000);
    container_fields = try ContainerFieldList.init(std.heap.page_allocator, 0x100000);
    structs = try StructList.init(std.heap.page_allocator, 0x1000);
    unions = try UnionList.init(std.heap.page_allocator, 0x1000);
    enums = try EnumList.init(std.heap.page_allocator, 0x1000);
    scopes = try ScopeList.init(std.heap.page_allocator, 0x10000);
    statements = try StatementList.init(std.heap.page_allocator, 0x100000);
    expressions = try ExpressionList.init(std.heap.page_allocator, 0x100000);
    type_init_values = try TypeInitValueList.init(std.heap.page_allocator, 0x10000);

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
        break :blk ValueIndex.toOpt(values.insert(.{.unresolved = .{
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

const FieldOrDeclResult = union(enum) {
    field: struct {
        field: *ContainerField,
        offset: u32,
    },
    decl: *Decl,
};

fn getFieldOrDecl(value_idx: ValueIndex.Index, name: []const u8) !?FieldOrDeclResult {
    var value_type = types.get(try values.get(value_idx).getType());
    if(value_type.* == .pointer) {
        value_type = types.get(value_type.pointer.child);
    }

    var field_opt: ?*ContainerField = null;
    var field_offset: u32 = 0;
    switch(value_type.*) {
        .struct_idx => |idx| {
            const struct_type = structs.get(idx);
            field_opt = try struct_type.lookupField(name);
            if(field_opt) |field| {
                field_offset = try struct_type.offsetOf(container_fields.getIndex(field));
            }
        },
        .union_idx => |idx| field_opt = try unions.get(idx).lookupField(name),
        else => |other| std.debug.panic("Can't do member access on {any}", .{other}),
    }

    if(field_opt) |field| {
        return .{.field = .{.field = field, .offset = field_offset}};
    }

    var scope: *Scope = undefined;
    switch(value_type.*) {
        .struct_idx => |idx| scope = scopes.get(structs.get(idx).scope),
        .union_idx => |idx| scope = scopes.get(unions.get(idx).scope),
        else => unreachable,
    }

    if(try scope.lookupDecl(name)) |decl| {
        return .{.decl = decl};
    }

    return null;
}

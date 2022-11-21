const std = @import("std");

const ast = @import("ast.zig");
const sources = @import("sources.zig");
const tokenizer = @import("tokenizer.zig");

fn errorType(comptime f: anytype) type {
    const f_type = if(@TypeOf(f) == type) f else @TypeOf(f);
    const ret_type = @typeInfo(f_type).Fn.return_type.?;
    return @typeInfo(ret_type).ErrorUnion.error_set;
}

source_file_index: sources.SourceIndex.Index,
peeked_token: ?tokenizer.Token = null,
current_content: [*:0]const u8,

fn expect(
    self: *@This(),
    comptime token_tag: std.meta.Tag(tokenizer.Token),
) !std.meta.TagPayload(tokenizer.Token, token_tag) {
    const tok = try self.peekToken();
    errdefer tok.deinit();
    if(tok == token_tag) {
        //std.debug.assert(tok == try self.tokenize());
        self.peeked_token = null;
        return @field(tok, @tagName(token_tag));
    } else {
        std.debug.print("Expected {s}, found {s}\n", .{@tagName(token_tag), @tagName(tok)});
        return error.UnexpectedToken;
    }
}

fn tryConsume(
    self: *@This(),
    comptime token_tag: std.meta.Tag(tokenizer.Token),
) !?std.meta.TagPayload(tokenizer.Token, token_tag) {
    const tok = try self.peekToken();
    if(tok == token_tag) {
        //std.debug.assert(tok == try self.tokenize());
        self.peeked_token = null;
        return @field(tok, @tagName(token_tag));
    } else {
        tok.deinit();
        return null;
    }
}

fn tokenize(self: *@This()) !tokenizer.Token {
    const retval = self.peekToken();
    self.peeked_token = null;
    return retval;
}

fn peekToken(self: *@This()) !tokenizer.Token {
    if(self.peeked_token == null) {
        self.peeked_token = try tokenizer.tokenize(&self.current_content);
    }
    return self.peeked_token.?;
}

fn identToAstNode(self: *@This(), tok: anytype) !ast.ExprIndex.Index {
    if(std.mem.eql(u8, tok.body, "u8")) return .u8;
    if(std.mem.eql(u8, tok.body, "u16")) return .u16;
    if(std.mem.eql(u8, tok.body, "u32")) return .u32;
    if(std.mem.eql(u8, tok.body, "u64")) return .u64;
    if(std.mem.eql(u8, tok.body, "i8")) return .i8;
    if(std.mem.eql(u8, tok.body, "i16")) return .i16;
    if(std.mem.eql(u8, tok.body, "i32")) return .i32;
    if(std.mem.eql(u8, tok.body, "i64")) return .i64;
    if(std.mem.eql(u8, tok.body, "bool")) return .bool;
    if(std.mem.eql(u8, tok.body, "type")) return .type;
    if(std.mem.eql(u8, tok.body, "void")) return .void;
    if(std.mem.eql(u8, tok.body, "anyopaque")) return .anyopaque;
    if(std.mem.eql(u8, tok.body, "@import")) return .import;

    return ast.expressions.insert(.{ .identifier = self.toAstIdent(tok) });
}

fn checkDecl(ident_expr_idx: ast.ExprIndex.Index) !void {
    if(@enumToInt(ident_expr_idx) < @enumToInt(ast.ExprIndex.OptIndex.none))
        return error.ReservedIdentifier;
}

fn toAstIdent(self: *@This(), tok: anytype) ast.SourceRef {
    const source_file = sources.source_files.get(self.source_file_index);

    const base_ptr = @ptrToInt(source_file.contents.ptr);
    const offset_ptr = @ptrToInt(tok.body.ptr);
    const file_offset = offset_ptr - base_ptr;

    return .{
        .file_offset = @intCast(u32, file_offset),
        .source_file = self.source_file_index,
    };
}

// Starts parsing at the parameter list
//   fn abc(123) T {}
//         ^ Here
// or
//   fn(123) T {}
//     ^ Here
fn parseFunctionExpr(self: *@This()) anyerror!ast.FunctionIndex.Index {
    _ = try self.expect(.@"(_ch");

    var param_builder = ast.function_params.builder();
    while((try self.peekToken()) != .@")_ch") {
        const ident = try self.expect(.identifier);
        defer ident.deinit();

        _ = try self.expect(.@":_ch");
        _ = try param_builder.insert(.{
            .identifier = self.toAstIdent(ident),
            .type = try self.parseExpression(null),
        });

        if((try self.tryConsume(.@",_ch")) == null) break;
    }

    _ = try self.expect(.@")_ch");
    const return_type = try self.parseExpression(null);

    return ast.functions.insert(.{
        .first_param = param_builder.first,
        .return_type = return_type,
        .body = try self.parseBlockStatement(),
    });
}

// {
//   ^ Call this after open curly
//   var a = 5;
//   ^ Returns first statement in block
//   Next chain contains rest of the statements
// }
fn parseBlockStatementBody(self: *@This()) anyerror!ast.StmtIndex.OptIndex {
    var stmt_builder = ast.statements.builder();
    while((try self.peekToken()) != .@"}_ch") {
        stmt_builder.insertIndex(try self.parseStatement());
    }
    return stmt_builder.first;
}

fn parseBlockStatement(self: *@This()) anyerror!ast.StmtIndex.OptIndex {
    _ = try self.expect(.@"{_ch");
    const body = try self.parseBlockStatementBody();
    _ = try self.expect(.@"}_ch");
    return body;
}

fn parseStatement(self: *@This()) anyerror!ast.StmtIndex.Index {
    const token = try self.peekToken();
    switch(token) {
        .@"{_ch" => {
            return ast.statements.insert(.{.value = .{
                .block_statement = .{.first_child = try self.parseBlockStatement()},
            }});
        },
        .break_keyword => {
            _ = try self.tokenize();
            _ = try self.expect(.@";_ch");
            return ast.statements.insert(.{.value = .break_statement});
        },
        .case_keyword => @panic("TODO: case statement"),
        .const_keyword, .var_keyword => return self.parseDeclaration(token),
        .continue_keyword => @panic("TODO: continue statement"),
        .endcase_keyword => @panic("TODO: endcase statement"),
        .if_keyword => {
            _ = try self.tokenize();
            _ = try self.expect(.@"(_ch");
            const condition = try self.parseExpression(null);
            _ = try self.expect(.@")_ch");
            const first_taken = try self.parseBlockStatement();
            const first_not_taken = if((try self.peekToken()) == .else_keyword) blk: {
                _ = try self.tokenize();
                break :blk switch(try self.peekToken()) {
                    .@"{_ch" => try self.parseBlockStatement(),
                    .if_keyword => ast.StmtIndex.toOpt(try self.parseStatement()),
                    else => |inner_tok| {
                        std.debug.print("Expected `{{` or `if` after `else`, got {s}\n", .{@tagName(inner_tok)});
                        return error.UnexpectedToken;
                    },
                };
            } else .none;
            return ast.statements.insert(.{.value = .{
                .if_statement = .{
                    .condition = condition,
                    .first_taken = first_taken,
                    .first_not_taken = first_not_taken,
                },
            }});
        },
        .loop_keyword => {
            _ = try self.tokenize();
            const condition = if ((try self.peekToken()) == .@"(_ch") blk: {
                _ = try self.tokenize();
                const res = try self.parseExpression(null);
                _ = try self.expect(.@")_ch");
                break :blk ast.ExprIndex.toOpt(res);
            } else .none;
            const body = try self.parseBlockStatement();
            return ast.statements.insert(.{.value = .{
                .loop_statement = .{
                    .condition = condition,
                    .first_child = body,
                },
            }});
        },
        .return_keyword => {
            var expr = ast.ExprIndex.OptIndex.none;
            _ = try self.tokenize();
            if((try self.peekToken()) != .@";_ch") {
                expr = ast.ExprIndex.toOpt(try self.parseExpression(null));
            }
            _ = try self.expect(.@";_ch");
            return ast.statements.insert(.{.value = .{.return_statement = .{.expr = expr}}});
        },
        .switch_keyword => @panic("TODO: switch statement"),
        .identifier, .__keyword, .@"(_ch",
        => { // Expression statement
            const expr_idx = try self.parseExpression(null);
            _ = try self.expect(.@";_ch");
            return ast.statements.insert(.{.value = .{.expression_statement = .{.expr = expr_idx}}});
        },

        inline
        .int_literal, .char_literal, .string_literal,
        .@".._ch", .@"._ch", .@",_ch", .@":_ch",
        .@"++_ch", .@"++=_ch", .@"=_ch", .@";_ch",
        .@"+_ch", .@"+=_ch", .@"+%_ch", .@"+%=_ch",
        .@"-_ch", .@"-=_ch", .@"-%_ch", .@"-%=_ch",
        .@"*_ch", .@"*=_ch", .@"*%_ch", .@"*%=_ch",
        .@"/_ch", .@"/=_ch", .@"%_ch", .@"%=_ch",
        .@"}_ch", .@")_ch", .@"[_ch", .@"]_ch",
        .@"==_ch", .@"!=_ch",
        .@"<_ch", .@"<<_ch", .@"<=_ch", .@"<<=_ch",
        .@">_ch", .@">>_ch", .@">=_ch", .@">>=_ch",
        .@"|_ch", .@"|=_ch", .@"&_ch", .@"&=_ch",
        .@"^_ch", .@"^=_ch", .@"~_ch", .@"!_ch",
        .@"||_ch", .@"&&_ch",
        .end_of_file, .else_keyword, .enum_keyword, .fn_keyword,
        .struct_keyword, .bool_keyword, .type_keyword, .void_keyword,
        .anyopaque_keyword, .volatile_keyword, .true_keyword, .false_keyword, .undefined_keyword,
        => |_, tag| {
            std.debug.print("Unexpected statement token: {s}\n", .{@tagName(tag)});
            return error.UnexpectedToken;
        },
    }
}

fn parseExpression(self: *@This(), precedence_in: ?usize) anyerror!ast.ExprIndex.Index {
    const precedence = precedence_in orelse 99999;

    var lhs: ast.ExprIndex.Index = switch(try self.tokenize()) {
        // Literals
        .int_literal => |lit| try ast.expressions.insert(.{.int_literal = self.toAstIdent(lit)}),
        .char_literal => |lit| try ast.expressions.insert(.{.char_literal = self.toAstIdent(lit)}),
        .string_literal => |lit| try ast.expressions.insert(.{.string_literal = self.toAstIdent(lit)}),
        .true_keyword => try ast.expressions.insert(.{.bool_literal = true}),
        .false_keyword => try ast.expressions.insert(.{.bool_literal = false}),

        // Atom keyword literal expressions
        .void_keyword => .void,
        .bool_keyword => .bool,
        .type_keyword => .type,
        .anyopaque_keyword => .anyopaque,
        .undefined_keyword => .undefined,

        // Control flow expressions
        .break_keyword => @panic("TODO: Break expressions"),
        .continue_keyword => @panic("TODO: Continue expressions"),
        .endcase_keyword => @panic("TODO: Endcase expressions"),
        .if_keyword => @panic("TODO: If expressions"),
        .loop_keyword => @panic("TODO: Loop expressions"),
        .switch_keyword => @panic("TODO: Switch expressions"),

        // Type expressions
        .enum_keyword => @panic("TODO: Enum type expression"),
        .struct_keyword => blk: {
            _ = try self.expect(.@"{_ch");

            const user_type = try ast.expressions.insert(.{ .struct_expression = .{
                .first_decl = try self.parseTypeBody(),
            }});

            _ = try self.expect(.@"}_ch");

            break :blk user_type;
        },

        .fn_keyword => blk: {
            const fidx = try self.parseFunctionExpr();
            break :blk try ast.expressions.insert(.{ .function_expression = fidx });
        },

        .@"(_ch" => blk: {
            const expr = try self.parseExpression(null);
            _ = try self.expect(.@")_ch");
            break :blk try ast.expressions.insert(.{ .parenthesized = .{ .operand = expr }});
        },

        inline
        .@"+_ch", .@"-_ch", .@"~_ch", .@"!_ch",
        => |_, uop| blk: {
            const expr = try self.parseExpression(0);
            const kind: std.meta.Tag(ast.ExpressionNode) = switch(uop) {
                .@"+_ch" => .unary_plus,
                .@"-_ch" => .unary_minus,
                .@"~_ch" => .unary_bitnot,
                .@"!_ch" => .unary_lognot,
                .@"*_ch" => .pointer_type,
                else => unreachable,
            };

            break :blk try ast.expressions.insert(@unionInit(ast.ExpressionNode, @tagName(kind), .{
                .operand = expr,
            }));
        },

        .@"*_ch" => blk: {
            var pointer_type: ast.PointerType = .{
                .is_const = false,
                .is_volatile = false,
                .item = undefined,
            };
            while(true) {
                switch(try self.peekToken()) {
                    .const_keyword => pointer_type.is_const = true,
                    .volatile_keyword => pointer_type.is_volatile = true,
                    else => break,
                }
                _ = try self.tokenize();
            }
            pointer_type.item = try self.parseExpression(0);
            break :blk try ast.expressions.insert(.{ .pointer_type = pointer_type });
        },

        .__keyword => .discard_underscore,
        .identifier => |ident| blk: {
            defer ident.deinit();
            break :blk try self.identToAstNode(ident);
        },

        inline
        .@".._ch", .@",_ch", .@"._ch", .@":_ch", .@";_ch",
        .@"=_ch", .@"==_ch", .@"!=_ch",
        .@"++_ch", .@"++=_ch",
        .@"+=_ch", .@"+%_ch", .@"+%=_ch",
        .@"-=_ch", .@"-%_ch", .@"-%=_ch",
        .@"*=_ch", .@"*%_ch", .@"*%=_ch",
        .@"/_ch", .@"/=_ch", .@"%_ch", .@"%=_ch",
        .@"}_ch", .@")_ch", .@"[_ch", .@"]_ch",
        .@"<_ch", .@"<<_ch", .@"<=_ch", .@"<<=_ch",
        .@">_ch", .@">>_ch", .@">=_ch", .@">>=_ch",
        .@"|_ch", .@"|=_ch", .@"&_ch", .@"&=_ch",
        .@"^_ch", .@"^=_ch", .@"||_ch", .@"&&_ch", .@"{_ch",
        .case_keyword, .const_keyword, .var_keyword, .volatile_keyword, .else_keyword,
        .end_of_file, .return_keyword,
        => |_, tag| {
            std.debug.print("Unexpected primary-expression token: {s}\n", .{@tagName(tag)});
            return error.UnexpectedToken;
        },
    };

    while(true) {
        switch(try self.peekToken()) {
            .@"._ch" => {
                _ = try self.tokenize();
                switch(try self.tokenize()) {
                    .identifier => |token| {
                        lhs = try ast.expressions.insert(.{ .member_access = .{
                            .lhs = lhs,
                            .rhs = try self.identToAstNode(token),
                        }});
                        token.deinit();
                    },
                    .@"&_ch" => {
                        lhs = try ast.expressions.insert(.{ .addr_of = .{ .operand = lhs } });
                    },
                    .@"*_ch" => {
                        lhs = try ast.expressions.insert(.{ .deref = .{ .operand = lhs } });
                    },
                    else => |token|  {
                        std.debug.print("Unexpected postfix token: {s}\n", .{@tagName(token)});
                        return error.UnexpectedToken;
                    },
                }
            },
            .@"(_ch" => {
                _ = try self.tokenize();
                var arg_builder = ast.expressions.builderWithPath("function_argument.next");
                while((try self.peekToken()) != .@")_ch") {
                    _ = try arg_builder.insert(.{ .function_argument = .{.value = try self.parseExpression(null)}});
                    if ((try self.tryConsume(.@",_ch")) == null) {
                        break;
                    }
                }
                _ = try self.expect(.@")_ch");

                if(lhs == .import) {
                    std.debug.assert(arg_builder.first == arg_builder.last);
                    const arg = ast.expressions.getOpt(arg_builder.first).?;
                    const arg_expr = arg.function_argument.value;
                    const strlit = ast.expressions.get(arg_expr).string_literal;
                    const path_string = try strlit.retokenize();
                    defer path_string.deinit();

                    const dir = sources.source_files.get(self.source_file_index).dir;
                    const parsed_file = try parseFileIn(path_string.string_literal.value, dir);
                    arg.* = .{ .import_call = parsed_file };
                    lhs = ast.expressions.getIndex(arg);
                } else {
                    lhs = try ast.expressions.insert(.{ .function_call = .{
                        .callee = lhs,
                        .first_arg = arg_builder.first,
                    }});
                }

            },
            .@"[_ch" => {
                _ = try self.tokenize();
                const index = try self.parseExpression(null);
                _ = try self.expect(.@"]_ch");
                lhs = try ast.expressions.insert(.{.array_subscript = .{
                    .lhs = lhs,
                    .rhs = index,
                }});
            },
            else => break,
        }
    }

    while(true) {
        switch(try self.peekToken()) {
            // Binary operators
            inline
            .@".._ch", .@"=_ch", .@"==_ch", .@"!=_ch",
            .@"++_ch", .@"++=_ch",
            .@"+_ch", .@"+=_ch", .@"+%_ch", .@"+%=_ch",
            .@"-_ch", .@"-=_ch", .@"-%_ch", .@"-%=_ch",
            .@"*_ch", .@"*=_ch", .@"*%_ch", .@"*%=_ch",
            .@"/_ch", .@"/=_ch", .@"%_ch", .@"%=_ch",
            .@"<_ch", .@"<<_ch", .@"<=_ch", .@"<<=_ch",
            .@">_ch", .@">>_ch", .@">=_ch", .@">>=_ch",
            .@"|_ch", .@"|=_ch", .@"&_ch", .@"&=_ch",
            .@"^_ch", .@"^=_ch",
            .@"||_ch", .@"&&_ch",
            => |_, op| {
                const op_prec: usize = switch(op) {
                    .@"*_ch", .@"*%_ch", .@"/_ch", .@"%_ch", => 3,
                    .@"++_ch", .@"+_ch", .@"+%_ch", .@"-_ch", .@"-%_ch", => 4,
                    .@"<<_ch", .@">>_ch" => 5,
                    .@"&_ch", .@"^_ch", .@"|_ch" => 6,
                    .@"==_ch", .@"!=_ch", .@"<_ch", .@"<=_ch", .@">_ch", .@">=_ch" => 7,
                    .@"&&_ch", .@"||_ch" => 8,
                    .@".._ch" => 9,

                    .@"=_ch", .@"++=_ch",
                    .@"+=_ch", .@"+%=_ch",
                    .@"-=_ch", .@"-%=_ch",
                    .@"*=_ch", .@"*%=_ch",
                    .@"/=_ch", .@"%=_ch",
                    .@"|=_ch", .@"&=_ch", .@"^=_ch",
                    .@"<<=_ch", .@">>=_ch",
                    => 10,

                    else => unreachable,
                };

                if(op_prec > precedence) {
                    return lhs;
                }

                if(op_prec == precedence and op_prec != 10) {
                    return lhs;
                }

                const kind: std.meta.Tag(ast.ExpressionNode) = switch(op) {
                    .@"*_ch" => .multiply,
                    .@"*=_ch" => .multiply_eq,
                    .@"*%_ch" => .multiply_mod,
                    .@"*%=_ch" => .multiply_mod_eq,
                    .@"/_ch" => .divide,
                    .@"/=_ch" => .divide_eq,
                    .@"%_ch" => .modulus,
                    .@"%=_ch" => .modulus_eq,
                    .@"+_ch" => .plus,
                    .@"+=_ch" => .plus_eq,
                    .@"+%_ch" => .plus_mod,
                    .@"+%=_ch" => .plus_mod_eq,
                    .@"-_ch" => .minus,
                    .@"-=_ch" => .minus_eq,
                    .@"-%_ch" => .minus_mod,
                    .@"-%=_ch" => .minus_mod_eq,
                    .@"<<_ch" => .shift_left,
                    .@"<<=_ch" => .shift_left_eq,
                    .@">>_ch" => .shift_right,
                    .@">>=_ch" => .shift_right_eq,
                    .@"&_ch" => .bitand,
                    .@"&=_ch" => .bitand_eq,
                    .@"|_ch" => .bitor,
                    .@"|=_ch" => .bitor_eq,
                    .@"^_ch" => .bitxor,
                    .@"^=_ch" => .bitxor_eq,
                    .@"<_ch" => .less,
                    .@"<=_ch" => .less_equal,
                    .@">_ch" => .greater,
                    .@">=_ch" => .greater_equal,
                    .@"==_ch" => .equals,
                    .@"!=_ch" => .not_equal,
                    .@"&&_ch" => .logical_and,
                    .@"||_ch" => .logical_or,
                    .@"=_ch" => .assign,
                    .@".._ch" => .range,
                    else => unreachable,
                };

                _ = try self.tokenize();
                const rhs = try self.parseExpression(op_prec);
                lhs = try ast.expressions.insert(@unionInit(ast.ExpressionNode, @tagName(kind), .{
                    .lhs = lhs,
                    .rhs = rhs,
                }));
            },

            // Terminate the expression, regardless of precedence
            .@")_ch", .@"]_ch", .@";_ch", .@",_ch", .@"{_ch",
            => return lhs,

            // Following tokens are unreachable because they are handled in the
            // postfix operators above
            .@"._ch", .@"(_ch", .@"[_ch",
            => unreachable,

            inline
            .identifier, .int_literal, .char_literal, .string_literal,
            .@":_ch", .@"}_ch", .@"~_ch", .@"!_ch",
            .break_keyword, .case_keyword, .const_keyword, .continue_keyword,
            .else_keyword, .endcase_keyword, .enum_keyword, .fn_keyword,
            .if_keyword, .loop_keyword, .return_keyword, .struct_keyword,
            .switch_keyword, .var_keyword, .volatile_keyword, .__keyword, .bool_keyword,
            .type_keyword, .void_keyword, .anyopaque_keyword,
            .end_of_file, .true_keyword, .false_keyword, .undefined_keyword,
            => |_, tag| {
                std.debug.panic("Unexpected post-primary expression token: {s}\n", .{@tagName(tag)});
            },
        }
    }
}

fn parseDeclaration(self: *@This(), token: tokenizer.Token) !ast.StmtIndex.Index {
    _ = try self.tokenize();
    const ident = try self.expect(.identifier);
    defer ident.deinit();

    var type_expr = ast.ExprIndex.OptIndex.none;
    var init_expr: ast.ExprIndex.Index = undefined;
    if(token == .fn_keyword) {
        const fidx = try self.parseFunctionExpr();
        init_expr = try ast.expressions.insert(.{ .function_expression = fidx });
    } else {
        if(try self.tryConsume(.@":_ch")) |_| {
            type_expr = ast.ExprIndex.toOpt(try self.parseExpression(0));
        }
        _ = try self.expect(.@"=_ch");

        init_expr = try self.parseExpression(null);

        _ = try self.expect(.@";_ch");
    }

    return ast.statements.insert(.{.value = .{ .declaration = .{
        .identifier = self.toAstIdent(ident),
        .type = type_expr,
        .init_value = init_expr,
        .mutable = token == .var_keyword,
    }}});
}

fn parseTypeBody(self: *@This()) !ast.StmtIndex.OptIndex {
    var decl_builder = ast.statements.builder();

    while(true) {
        const token = try self.peekToken();
        switch(token) {
            .identifier => |ident| {
                _ = try self.tokenize();
                defer ident.deinit();

                var type_expr = ast.ExprIndex.OptIndex.none;
                if((try self.peekToken()) == .@":_ch") {
                    _ = try self.tokenize();
                    type_expr = ast.ExprIndex.toOpt(try self.parseExpression(0));
                }

                var init_expr = ast.ExprIndex.OptIndex.none;
                if((try self.peekToken()) == .@"=_ch") {
                    _ = try self.tokenize();
                    init_expr = ast.ExprIndex.toOpt(try self.parseExpression(null));
                }

                _ = try self.expect(.@",_ch");
                _ = try decl_builder.insert(.{.value = .{ .field_decl = .{
                    .identifier = self.toAstIdent(ident),
                    .type = type_expr,
                    .init_value = init_expr,
                }}});
            },
            .const_keyword, .var_keyword, .fn_keyword => decl_builder.insertIndex(try self.parseDeclaration(token)),
            .end_of_file, .@"}_ch" => return decl_builder.first,
            else => std.debug.panic("Unhandled top-level token {any}", .{token}),
        }
    }
}

fn parseFile(fidx: sources.SourceIndex.Index) !ast.ExprIndex.Index {
    var parser = @This() {
        .source_file_index = fidx,
        .current_content = sources.source_files.get(fidx).contents.ptr,
    };

    return ast.expressions.insert(.{ .struct_expression = .{.first_decl = try parser.parseTypeBody()}});
}

pub fn parseFileIn(path: [:0]u8, current_dir: std.fs.Dir) !sources.SourceIndex.Index {
    var realpath_buf: [std.os.PATH_MAX]u8 = undefined;
    const realpath_stack = try current_dir.realpathZ(path.ptr, &realpath_buf);
    const realpath = try std.heap.page_allocator.dupe(u8, realpath_stack);

    if(sources.path_map.get(realpath)) |parsed_file| {
        return parsed_file;
    }

    const file_handle = try current_dir.openFileZ(path.ptr, .{});

    const dir_handle = if(std.fs.path.dirname(path)) |dirname| blk: {
        path[dirname.len] = 0;
        // Split out into a local here because of compiler bug
        const dir_path = path[0..dirname.len:0];
        break :blk try current_dir.openDirZ(dir_path, .{
            .access_sub_paths = true,
        }, false);
    }
    else blk: {
        break :blk current_dir;
    };

    const file_size = try file_handle.getEndPos();
    const fidx = try sources.source_files.insert(.{
        .file = file_handle,
        .dir = dir_handle,
        .realpath = realpath,
        .contents = try file_handle.readToEndAllocOptions(
            std.heap.page_allocator,
            file_size,
            file_size,
            @alignOf(u8),
            0,
        ),
        .top_level_struct = undefined,
    });

    try sources.path_map.put(realpath, fidx);

    std.debug.print("Starting parse of file: {s}\n", .{realpath});

    sources.source_files.get(fidx).top_level_struct = try parseFile(fidx);

    return fidx;
}

fn makeIndent(indent_level: usize) []const u8 {
    return (" " ** 4096)[0..indent_level * 2];
}

fn dumpStatementChain(first_stmt: ast.StmtIndex.OptIndex, indent_level: usize) anyerror!void {
    if(first_stmt == .empty_block or first_stmt == .none) {
        std.debug.print("{{}}", .{});
        return;
    }

    std.debug.print("{{", .{});

    var curr_stmt = first_stmt;
    while(ast.statements.getOpt(curr_stmt)) |stmt| {
        std.debug.print("\n{s}", .{makeIndent(indent_level + 1)});
        try dumpNode(curr_stmt, stmt, indent_level + 1);
        curr_stmt = stmt.next;
    }

    std.debug.print("\n{s}}}", .{makeIndent(indent_level)});
}

fn dumpNode(index: anytype, node: anytype, indent_level: usize) anyerror!void {
    switch(@TypeOf(node)) {
        *sources.SourceFile => {
            std.debug.print("SourceFile#{d} {s}", .{@enumToInt(index), node.realpath});
        },
        *ast.ExpressionNode => switch(node.*) {
            .identifier, .int_literal, .char_literal, .string_literal => |ident| std.debug.print("{s}", .{try ident.toSlice()}),
            .bool_literal => |value| std.debug.print("{}", .{value}),
            .void, .anyopaque, .bool, .type, .undefined => std.debug.print("{s}", .{@tagName(node.*)}),
            .unsigned_int => |bits| std.debug.print("u{d}", .{bits}),
            .signed_int => |bits| std.debug.print("i{d}", .{bits}),
            .pointer_type => |ptr_type| {
                std.debug.print("*", .{});
                if (ptr_type.is_const) {
                    std.debug.print("const ", .{});
                }
                if (ptr_type.is_volatile) {
                    std.debug.print("volatile ", .{});
                }
                try dumpNode(ptr_type.item, ast.expressions.get(ptr_type.item), indent_level);
            },
            .import_call => |file_index| {
                std.debug.print("(", .{});
                try dumpNode(file_index, sources.source_files.get(file_index), indent_level);
                std.debug.print(")", .{});
            },
            .function_call => |call| {
                try dumpNode(call.callee, ast.expressions.get(call.callee), indent_level);
                std.debug.print("(", .{});
                var curr_arg = call.first_arg;
                while(ast.expressions.getOpt(curr_arg)) |arg| {
                    const func_arg = arg.function_argument;
                    try dumpNode(curr_arg, ast.expressions.get(func_arg.value), indent_level);
                    if(func_arg.next != .none) {
                        std.debug.print(", ", .{});
                    }
                    curr_arg = func_arg.next;
                }
                std.debug.print(")", .{});
            },
            .addr_of, .deref => |uop| {
                try dumpNode(uop.operand, ast.expressions.get(uop.operand), indent_level);
                switch(node.*) {
                    .addr_of => std.debug.print(".&", .{}),
                    .deref => std.debug.print(".*", .{}),
                    else => unreachable,
                }
            },
            .member_access => |bop| {
                try dumpNode(bop.lhs, ast.expressions.get(bop.lhs), indent_level);
                std.debug.print(".", .{});
                try dumpNode(bop.rhs, ast.expressions.get(bop.rhs), indent_level);
            },
            .parenthesized => |uop| {
                std.debug.print("(", .{});
                try dumpNode(uop.operand, ast.expressions.get(uop.operand), indent_level);
                std.debug.print(")", .{});
            },
            .multiply, .multiply_eq, .multiply_mod, .multiply_mod_eq,
            .divide, .divide_eq, .modulus, .modulus_eq,
            .plus, .plus_eq, .plus_mod, .plus_mod_eq,
            .minus, .minus_eq, .minus_mod, .minus_mod_eq,
            .shift_left, .shift_left_eq, .shift_right, .shift_right_eq,
            .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq,
            .less, .less_equal, .greater, .greater_equal, .equals, .not_equal,
            .logical_and, .logical_or, .assign, .range,
            => |bop| {
                const op = switch(node.*) {
                    .multiply => "*",
                    .multiply_eq => "*=",
                    .multiply_mod => "*%",
                    .multiply_mod_eq => "*%=",
                    .divide => "/",
                    .divide_eq => "/=",
                    .modulus => "%",
                    .modulus_eq => "%=",
                    .plus => "+",
                    .plus_eq => "+=",
                    .plus_mod => "+%",
                    .plus_mod_eq => "+%=",
                    .minus => "-",
                    .minus_eq => "-=",
                    .minus_mod => "-%",
                    .minus_mod_eq => "-%=",
                    .shift_left => "<<",
                    .shift_left_eq => "<<=",
                    .shift_right => ">>",
                    .shift_right_eq => ">>=",
                    .bitand => "&",
                    .bitand_eq => "&=",
                    .bitor => "|",
                    .bitxor_eq => "|=",
                    .bitxor => "^",
                    .bitor_eq => "^=",
                    .less => "<",
                    .less_equal => "<=",
                    .greater => ">",
                    .greater_equal => ">=",
                    .equals => "==",
                    .not_equal => "!=",
                    .logical_and => "&&",
                    .logical_or => "||",
                    .assign => "=",
                    .range => "..",
                    else => unreachable,
                };

                try dumpNode(bop.lhs, ast.expressions.get(bop.lhs), indent_level);
                std.debug.print(" {s} ", .{op});
                try dumpNode(bop.rhs, ast.expressions.get(bop.rhs), indent_level);
            },
            .discard_underscore => std.debug.print("_", .{}),
            .function_expression => |func_idx| try dumpNode(func_idx, ast.functions.get(func_idx), indent_level),
            .struct_expression => |expr| {
                std.debug.print("struct ", .{});
                try dumpStatementChain(expr.first_decl, indent_level);
            },
            .array_subscript => |bop| {
                try dumpNode(bop.lhs, ast.expressions.get(bop.lhs), indent_level);
                std.debug.print("[", .{});
                try dumpNode(bop.rhs, ast.expressions.get(bop.rhs), indent_level);
                std.debug.print("]", .{});
            },
            else => |expr| std.debug.panic("Cannot dump expression of type {s}", .{@tagName(expr)}),
        },
        *ast.StatementNode => switch(node.value) {
            .expression_statement => |expr| {
                try dumpNode(expr.expr, ast.expressions.get(expr.expr), indent_level);
                std.debug.print(";", .{});
            },
            .block_statement => |blk| try dumpStatementChain(blk.first_child, indent_level),
            .declaration => |decl| {
                const decl_kw = if (decl.mutable) "var" else "const";
                std.debug.print("{s} {s}", .{decl_kw, try decl.identifier.toSlice()});
                if(ast.ExprIndex.unwrap(decl.type)) |type_idx| {
                    std.debug.print(": ", .{});
                    try dumpNode(type_idx, ast.expressions.get(type_idx), indent_level);
                }
                std.debug.print(" = ", .{});
                try dumpNode(decl.init_value, ast.expressions.get(decl.init_value), indent_level);
                std.debug.print(";", .{});
            },
            .field_decl => |decl| {
                std.debug.print("{s}", .{try decl.identifier.toSlice()});
                if(ast.ExprIndex.unwrap(decl.type)) |type_idx| {
                    std.debug.print(": ", .{});
                    try dumpNode(type_idx, ast.expressions.get(type_idx), indent_level);
                }
                if(ast.ExprIndex.unwrap(decl.init_value)) |init_idx| {
                    std.debug.print(" = ", .{});
                    try dumpNode(init_idx, ast.expressions.get(init_idx), indent_level);
                }
                std.debug.print(",", .{});
            },
            .if_statement => |stmt| {
                std.debug.print("if (", .{});
                try dumpNode(stmt.condition, ast.expressions.get(stmt.condition), indent_level);
                std.debug.print(") ", .{});
                try dumpStatementChain(stmt.first_taken, indent_level);
                std.debug.print(" else ", .{});
                try dumpStatementChain(stmt.first_not_taken, indent_level);
            },
            .loop_statement => |stmt| {
                std.debug.print("loop ", .{});
                if(ast.ExprIndex.unwrap(stmt.condition)) |cond_idx| {
                    std.debug.print("(", .{});
                    try dumpNode(stmt.condition, ast.expressions.get(cond_idx), indent_level);
                    std.debug.print(") ", .{});
                }
                try dumpStatementChain(stmt.first_child, indent_level);
            },
            .break_statement => std.debug.print("break;", .{}),
            .return_statement => |stmt| {
                std.debug.print("return", .{});
                if(ast.expressions.getOpt(stmt.expr)) |expr| {
                    std.debug.print(" ", .{});
                    try dumpNode(stmt.expr, expr, indent_level);
                }
                std.debug.print(";", .{});
            },
            else => |stmt| std.debug.panic("Cannot dump statement of type {s}", .{@tagName(stmt)}),
        },
        *ast.FunctionExpression => {
            std.debug.print("fn(", .{});
            var curr_param = node.first_param;
            while(ast.function_params.getOpt(curr_param)) |param| {
                std.debug.print("{s}: ", .{try param.identifier.toSlice()});
                try dumpNode(param.type, ast.expressions.get(param.type), indent_level);
                if(param.next != .none) {
                    std.debug.print(", ", .{});
                }
                curr_param = param.next;
            }
            std.debug.print(") ", .{});
            try dumpNode(node.return_type, ast.expressions.get(node.return_type), indent_level);
            std.debug.print(" ", .{});
            try dumpStatementChain(node.body, indent_level);
        },
        else => @compileError("Cannot dump type " ++ @typeName(@TypeOf(node))),
    }
}

pub fn parseRootFile(path: [:0]u8) !ast.ExprIndex.Index {
    const fidx = try parseFileIn(path, std.fs.cwd());
    for(sources.source_files.elements.items[sources.SourceIndex.alloc_base..]) |*file| {
        try dumpNode(sources.source_files.getIndex(file), file, 0);
        std.debug.print("\n{s}", .{makeIndent(1)});
        try dumpNode(file.top_level_struct, ast.expressions.get(file.top_level_struct), 1);
        std.debug.print("\n", .{});
    }
    return sources.source_files.get(fidx).top_level_struct;
}

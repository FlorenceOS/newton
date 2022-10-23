const std = @import("std");

const ast = @import("ast.zig");
const sources = @import("sources.zig");
const tokenizer = @import("tokenizer.zig");
const values = @import("values.zig");

fn errorType(comptime f: anytype) type {
    const f_type = if(@TypeOf(f) == type) f else @TypeOf(f);
    const ret_type = @typeInfo(f_type).Fn.return_type.?;
    return @typeInfo(ret_type).ErrorUnion.error_set;
}

source_file_index: sources.SourceIndex.Index,
peeked_token: ?tokenizer.Token = null,
current_content: [*:0]const u8,

const ParseError = errorType(tokenizer.tokenize) || error{
    UnexpectedToken,
};

fn expect(
    self: *@This(),
    comptime token_tag: std.meta.Tag(tokenizer.Token),
) ParseError!std.meta.TagPayload(tokenizer.Token, token_tag) {
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
) ParseError!?std.meta.TagPayload(tokenizer.Token, token_tag) {
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

fn tokenize(self: *@This()) ParseError!tokenizer.Token {
    const retval = self.peekToken();
    self.peeked_token = null;
    return retval;
}

fn peekToken(self: *@This()) ParseError!tokenizer.Token {
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
fn parseFunctionExpr(self: *@This(),) ParseError!ast.FunctionIndex.Index {
    _ = try self.expect(.@"(_ch");
    var first_param = ast.FunctionParamIndex.OptIndex.none;
    var last_param = ast.FunctionParamIndex.OptIndex.none;
    while(true) {
        const ident = try self.expect(.identifier);
        defer ident.deinit();
        _ = try self.expect(.@":_ch");
        const param_type = try self.parseExpression(null);

        const curr_param_idx = ast.FunctionParamIndex.toOpt(
            try ast.function_params.insert(.{
                .identifier = self.toAstIdent(ident),
                .type = param_type,
                .next = .none,
            })
        );
        if(first_param == .none) {
            first_param = curr_param_idx;
        }
        if(ast.FunctionParamIndex.unwrap(last_param)) |lp_idx| {
            ast.function_params.get(lp_idx).next = curr_param_idx;
        }
        last_param = curr_param_idx;

        if((try self.tryConsume(.@",_ch")) == null) {
            break;
        }
    }

    _ = try self.expect(.@")_ch");
    
    const return_type = try self.parseExpression(null);

    _ = try self.expect(.@"{_ch");

    const first_statement = try self.parseBlockStatementBody();

    _ = try self.expect(.@"}_ch");

    return ast.functions.insert(.{
        .first_param = first_param,
        .return_type = return_type,
        .first_statement = first_statement,
    });
}

// {
//   ^ Call this after open curly
//   var a = 5;
//   ^ Returns first statement in block
//   Next chain contains rest of the statements
// }
fn parseBlockStatementBody(self: *@This()) ParseError!ast.StmtIndex.Index {
    var first_statement = ast.StmtIndex.OptIndex.none;
    var last_statement = ast.StmtIndex.OptIndex.none;
    while(true) {
        if((try self.peekToken()) == .@"}_ch") {
            if(ast.StmtIndex.unwrap(first_statement)) |fs| {
                return fs;
            } else {
                return .empty_block;
            }
        }

        const stmt = try self.parseStatement();
        const ostmt = ast.StmtIndex.toOpt(stmt);

        if(first_statement == .none) {
            first_statement = ostmt;
        }
        if(ast.StmtIndex.unwrap(last_statement)) |ls_idx| {
            ast.statements.get(ls_idx).next = ostmt;
        }
        last_statement = ostmt;
    }
}

fn parseStatement(self: *@This()) ParseError!ast.StmtIndex.Index {
    switch(try self.peekToken()) {
        .@"{_ch" => return self.parseBlockStatementBody(),
        .break_keyword => @panic("TODO: break statement"),
        .case_keyword => @panic("TODO: case statement"),
        .const_keyword, .var_keyword => |tok| {
            _ = tok;
            @panic("TODO: decl statement");
        },
        .continue_keyword => @panic("TODO: continue statement"),
        .endcase_keyword => @panic("TODO: endcase statement"),
        .if_keyword => @panic("TODO: if statement"),
        .loop_keyword => @panic("TODO: loop statement"),
        .return_keyword => @panic("TODO: return statement"),
        .switch_keyword => @panic("TODO: switch statement"),
        .identifier, .__keyword, .@"(_ch",
        => { // Expression statement
            const expr_idx = try self.parseExpression(null);
            _ = try self.expect(.@";_ch");
            return ast.statements.insert(.{ .next = .none, 
                .value = .{ .expression_statement = .{
                    .expr = expr_idx,
                } },
            });
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
        .anyopaque_keyword,
        => |_, tag| {
            std.debug.print("Unexpected statement token: {s}\n", .{@tagName(tag)});
            return error.UnexpectedToken;
        },
    }
}

fn parseExpression(self: *@This(), precedence_in: ?usize) ParseError!ast.ExprIndex.Index {
    const precedence = precedence_in orelse 99999;

    var lhs: ast.ExprIndex.Index = switch(try self.tokenize()) {
        // Literals
        .int_literal => |lit| {
            return ast.expressions.insert(.{.int_literal = self.toAstIdent(lit)});
        },
        .char_literal => |lit| {
            return ast.expressions.insert(.{.char_literal = self.toAstIdent(lit)});
        },
        .string_literal => |_| @panic("TODO: String literal expression"),

        // Atom keyword literal expressions
        .void_keyword => .void,
        .bool_keyword => .bool,
        .type_keyword => .type,
        .anyopaque_keyword => .anyopaque,

        // Control flow expressions
        .break_keyword => @panic("TODO: Break expressions"),
        .continue_keyword => @panic("TODO: Continue expressions"),
        .endcase_keyword => @panic("TODO: Endcase expressions"),
        .if_keyword => @panic("TODO: If expressions"),
        .loop_keyword => @panic("TODO: Loop expressions"),
        .switch_keyword => @panic("TODO: Switch expressions"),

        // Type expressions
        .enum_keyword => @panic("TODO: Enum type expression"),
        .struct_keyword => @panic("TODO: Struct type expression"),

        .fn_keyword => {
            const fidx = try self.parseFunctionExpr();
            return ast.expressions.insert(.{ .function_expression = fidx });
        },

        .@"+_ch" => @panic("TODO: Unary plus expression"),
        .@"-_ch" => @panic("TODO: Unary minus expression"),
        .@"(_ch" => @panic("TODO: Paren expression"),

        .__keyword => .discard_underscore,

        .@"*_ch" => @panic("TODO: Pointer type expressions"),
        .identifier => |ident| try self.identToAstNode(ident),

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
        .@"^_ch", .@"^=_ch", .@"~_ch", .@"!_ch",
        .@"||_ch", .@"&&_ch",
        .@"{_ch",
        .case_keyword, .const_keyword, .var_keyword, .else_keyword,
        .end_of_file, .return_keyword,
        => |_, tag| {
            std.debug.print("Unexpected primary-expression token: {s}\n", .{@tagName(tag)});
            return error.UnexpectedToken;
        },
    };

    // TODO: Postfix operators
    // while(true) {
    //     switch(try self.peekToken()) {
    //
    //     }
    // }

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
            .switch_keyword, .var_keyword, .__keyword, .bool_keyword,
            .type_keyword, .void_keyword, .anyopaque_keyword,
            .end_of_file,
            => |_, tag| {
                std.debug.print("Unexpected post-primary expression token: {s}\n", .{@tagName(tag)});
                return error.UnexpectedToken;
            },
        }
    }
}

fn parseTypeBody(self: *@This()) !ast.UserStructIndex.Index {
    var first_decl = ast.StmtIndex.OptIndex.none;
    var last_decl = ast.StmtIndex.OptIndex.none;

    while(true) {
        const token = try self.tokenize();
        switch(token) {
            .const_keyword, .var_keyword, .fn_keyword => {
                const ident = try self.expect(.identifier);
                defer ident.deinit();

                var type_expr = ast.ExprIndex.OptIndex.none;
                var init_expr: ast.ExprIndex.Index = undefined;
                if(token == .fn_keyword) {
                    const fidx = try self.parseFunctionExpr();
                    init_expr = try ast.expressions.insert(.{ .function_expression = fidx });
                } else {
                    if(try self.tryConsume(.@":_ch")) |_| {
                        type_expr = ast.ExprIndex.toOpt(try self.parseExpression(null));
                    }
                    _ = try self.expect(.@"=_ch");

                    init_expr = try self.parseExpression(null);

                    _ = try self.expect(.@";_ch");
                }
                
                const curr_decl = try ast.statements.insert(.{ .next = .none, .value = .{ .declaration = .{
                    .identifier = self.toAstIdent(ident),
                    .type = type_expr,
                    .init_value = init_expr,
                    .mutable = token == .var_keyword,
                } } });
                const odecl = ast.StmtIndex.toOpt(curr_decl);

                if(first_decl == .none) {
                    first_decl = odecl;
                }

                if(ast.StmtIndex.unwrap(last_decl)) |ld_idx| {
                    ast.statements.get(ld_idx).next = odecl;
                }

                last_decl = odecl;
            },
            .end_of_file, .@"}_ch" => {
                return ast.user_structs.insert(.{
                    .first_decl = first_decl,
                });
            },
            else => std.debug.panic("Unhandled top-level token {any}", .{token}),
        }
        token.deinit();
    }
}



fn parseFile(fidx: sources.SourceIndex.Index) !ast.UserStructIndex.Index {
    const file = sources.source_files.get(fidx);
    var parser = @This() {
        .source_file_index = fidx,
        .current_content = file.contents.ptr,
    };
    return parser.parseTypeBody();
}

fn parseFileWithHandles(file: std.fs.File, dir: std.fs.Dir) !sources.SourceIndex.Index {
    const file_size = try file.getEndPos();
    const fidx = try sources.source_files.insert(.{
        .file = file,
        .dir = dir,
        .contents = try file.readToEndAllocOptions(
            std.heap.page_allocator,
            file_size,
            file_size,
            @alignOf(u8),
            0,
        ),
        .top_level_struct = .none,
    });

    const top_level_struct = try parseFile(fidx);
    sources.source_files.get(fidx).top_level_struct = top_level_struct;
    return fidx;
}

pub fn parseFileIn(path: [:0]u8, current_dir: std.fs.Dir) !sources.SourceIndex.Index {
    const file_handle = try current_dir.openFileZ(path.ptr, .{});

    if(std.fs.path.dirname(path)) |dirname| {
        path[dirname.len] = 0;
        // Split out into a local here because of compiler bug
        const dir_path = path[0..dirname.len:0];
        return parseFileWithHandles(file_handle, try current_dir.openDirZ(dir_path, .{
            .access_sub_paths = true,
        }, false));
    }
    else {
        return parseFileWithHandles(file_handle, current_dir);
    }
}

pub fn dump(obj: anytype, indentation: usize) !void {
    const indent = (" " ** 1000)[0..indentation];
    switch(@TypeOf(obj)) {
        *sources.SourceFile => {
            std.debug.print("{s}source file #{}:\n", .{indent, @enumToInt(sources.source_files.getIndex(obj))});
            std.debug.print("{s} root object:\n", .{indent});
            try dump(ast.user_structs.get(obj.top_level_struct), indentation + 2);
        },

        *ast.UserDefinedStruct => {
            std.debug.print("{s}struct {{\n", .{indent});

            var current_decl = obj.first_decl;
            while(ast.StmtIndex.unwrap(current_decl)) |cidx| {
                const decl = ast.statements.get(cidx);
                try dump(decl, indentation + 1);
                current_decl = decl.next;
            }

            std.debug.print("{s}}}\n", .{indent});
        },

        *ast.StatementNode => {
            switch(obj.value) {
                .declaration => |decl| {
                    std.debug.print("{s}{s} ", .{indent, if(decl.mutable) "var" else "const"});
                    try dump(decl.identifier, indentation);
                    if(ast.ExprIndex.unwrap(decl.type)) |decl_t| {
                        std.debug.print(": ", .{});
                        try dump(ast.expressions.get(decl_t), indentation);
                    }
                    std.debug.print(" = ", .{});
                    try dump(ast.expressions.get(decl.init_value), indentation);
                    std.debug.print(";\n", .{});
                },
                inline else => |_, tag| std.debug.panic("Can't dump statement type {s}", .{@tagName(tag)}),
            }
        },

        *ast.ExpressionNode => {
            switch(obj.*) {
                .function_expression => {
                    std.debug.print("fn(...)T{{...}}", .{});
                },
                .type_expression => |T| {
                    try dump(values.all_types.get(T), indentation);
                },
                inline else => |_, tag| std.debug.panic("Can't dump expression type {s}", .{@tagName(tag)}),
            }
        },

        *values.Type => {
    // pointer_to_var: PointerType,
    // pointer_to_volatile_var: PointerType,
    // pointer_to_const: PointerType,
    // pointer_to_volatile_const: PointerType,

            switch(obj.*) {
                .bool, .void, .anyopaque, .type => {
                    std.debug.print("{s}", .{@tagName(obj.*)});
                },
                .signed_int => |i| {
                    std.debug.print("i{d}", .{i.num_bits});
                },
                .unsigned_int => |u| {
                    std.debug.print("u{d}", .{u.num_bits});
                },
                .pointer_to_var => |ptr| {
                    std.debug.print("*", .{});
                    try dump(values.all_types.get(ptr.child), indentation);
                },
                .pointer_to_volatile_var => |ptr| {
                    std.debug.print("*volatile ", .{});
                    try dump(values.all_types.get(ptr.child), indentation);
                },
                .pointer_to_const => |ptr| {
                    std.debug.print("*const ", .{});
                    try dump(values.all_types.get(ptr.child), indentation);
                },
                .pointer_to_volatile_const => |ptr| {
                    std.debug.print("*const volatile ", .{});
                    try dump(values.all_types.get(ptr.child), indentation);
                },
            }
        },

        ast.SourceRef => {
            std.debug.print("'{s}'", .{std.fmt.fmtSliceEscapeUpper(try obj.toSlice())});
        },

        else => @compileError("Invalid type: " ++ @typeName(@TypeOf(obj))),
    }
}

pub fn parseRootFile(path: [:0]u8) !ast.UserStructIndex.Index {
    const fidx = try parseFileIn(path, std.fs.cwd());
    for(sources.source_files.elements.items[sources.SourceIndex.alloc_base..]) |*source_file| {
        try dump(source_file, 0);
    }
    return sources.source_files.get(fidx).top_level_struct;
}

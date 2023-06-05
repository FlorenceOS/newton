const std = @import("std");

const indexed_list = @import("indexed_list.zig");
const sources = @import("sources.zig");
const tokenizer = @import("tokenizer.zig");

const ExpressionList = indexed_list.IndexedList(ExprIndex, ExpressionNode);
const StatementList = indexed_list.IndexedList(StmtIndex, StatementNode);
const FunctionList = indexed_list.IndexedList(FunctionIndex, FunctionExpression);
const FunctionParamList = indexed_list.IndexedList(FunctionParamIndex, FunctionParameter);
const TypeInitValueList = indexed_list.IndexedList(TypeInitValueIndex, TypeInitValue);

pub const ExprIndex = indexed_list.Indices(u32, opaque{}, .{
    // Commonly used constants
    .undefined = .{ .undefined = {}},
    .@"unreachable" = .{ .unreachable_expr = {}},

    // Commonly used types
    .void = .{ .void = {} },
    .anyopaque = .{ .anyopaque = {} },
    .bool = .{ .bool = {} },
    .type = .{ .type = {} },
    .noreturn = .{ .noreturn = {} },
    .u8 = .{ .unsigned_int = 8 },
    .u16 = .{ .unsigned_int = 16 },
    .u32 = .{ .unsigned_int = 32 },
    .u64 = .{ .unsigned_int = 64 },
    .i8 = .{ .signed_int = 8 },
    .i16 = .{ .signed_int = 16 },
    .i32 = .{ .signed_int = 32 },
    .i64 = .{ .signed_int = 64 },

    // _ = a;
    // ^ This thing
    .discard_underscore = .{ .discard_underscore = {} },
});
pub const StmtIndex = indexed_list.Indices(u32, opaque{}, .{
    .empty_return = .{.value = .{.return_statement = .{.expr = .none}}},
    .empty_block = .{.value = .{.block_statement = .{.first_child = .none}}},
});
pub const FunctionIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const FunctionParamIndex = indexed_list.Indices(u32, opaque{}, .{});
pub const TypeInitValueIndex = indexed_list.Indices(u32, opaque{}, .{});

pub const TypeBody = struct {
    first_decl: StmtIndex.OptIndex,
};

pub const Bop = struct {
    lhs: ExprIndex.Index,
    rhs: ExprIndex.Index,
};

pub const Uop = struct {
    operand: ExprIndex.Index,
};

pub const PointerType = struct {
    is_const: bool,
    is_volatile: bool,
    child: ExprIndex.Index,
};

pub const SourceRef = struct {
    source_file: sources.SourceIndex.Index,
    file_offset: u32,

    pub fn toSlice(self: @This()) ![]const u8 {
        const source = sources.source_files.get(self.source_file).contents[self.file_offset..];
        const len = try tokenizer.tokenLength(source);
        return source[0..len];
    }

    pub fn retokenize(self: @This()) !tokenizer.Token {
        const source = sources.source_files.get(self.source_file).contents[self.file_offset..];
        var source_ptr = source.ptr;
        return tokenizer.tokenize(&source_ptr);
    }
};

pub const FunctionArgument = struct {
    value: ExprIndex.Index,
    next: ExprIndex.OptIndex = .none,
};

pub const FunctionCall = struct {
    callee: ExprIndex.Index,
    first_arg: ExprIndex.OptIndex,
};

pub const BuiltinFunction = enum {
    import,
    int_to_ptr,
    is_pointer,
    ptr_to_int,
    size_of,
    syscall,
    This,
    truncate,
};

pub const ExpressionNode = union(enum) {
    identifier: SourceRef,
    int_literal: SourceRef,
    char_literal: SourceRef,
    string_literal: SourceRef,
    bool_literal: bool,

    parenthesized: Uop,
    force_comptime_eval: Uop,
    unary_plus: Uop,
    unary_minus: Uop,
    unary_bitnot: Uop,
    unary_lognot: Uop,
    pointer_type: PointerType,

    addr_of: Uop,
    deref: Uop,

    undefined,
    unreachable_expr,
    discard_underscore,

    void,
    noreturn,
    anyopaque,
    bool,
    type,
    unsigned_int: u32,
    signed_int: u32,
    builtin_function: BuiltinFunction,
    imported_file: sources.SourceIndex.Index,

    type_init_list: struct {
        specified_type: ExprIndex.OptIndex,
        first_value: TypeInitValueIndex.OptIndex,
    },

    // Binary expressions, has lhs and rhs populated
    array_concat: Bop,
    array_subscript: Bop,
    array_type: Bop,
    member_access: Bop,
    multiply: Bop,
    multiply_eq: Bop,
    multiply_mod: Bop,
    multiply_mod_eq: Bop,
    divide: Bop,
    divide_eq: Bop,
    modulus: Bop,
    modulus_eq: Bop,
    plus: Bop,
    plus_eq: Bop,
    plus_mod: Bop,
    plus_mod_eq: Bop,
    minus: Bop,
    minus_eq: Bop,
    minus_mod: Bop,
    minus_mod_eq: Bop,
    shift_left: Bop,
    shift_left_eq: Bop,
    shift_right: Bop,
    shift_right_eq: Bop,
    bitand: Bop,
    bitand_eq: Bop,
    bitor: Bop,
    bitxor_eq: Bop,
    bitxor: Bop,
    bitor_eq: Bop,
    less: Bop,
    less_equal: Bop,
    greater: Bop,
    greater_equal: Bop,
    equals: Bop,
    not_equal: Bop,
    logical_and: Bop,
    logical_or: Bop,
    assign: Bop,
    range: Bop,

    block_expression: struct {
        block: StmtIndex.OptIndex,
        label: ExprIndex.OptIndex,
    },

    function_expression: FunctionIndex.Index,

    // Function calls
    function_call: FunctionCall,
    function_argument: FunctionArgument,

    struct_expression: TypeBody,
};

pub const StatementNode = struct {
    next: StmtIndex.OptIndex = .none,

    value: union (enum) {
        declaration: struct {
            identifier: SourceRef,
            type: ExprIndex.OptIndex,
            init_value: ExprIndex.Index,
            mutable: bool,
        },
        field_decl: struct {
            identifier: SourceRef,
            type: ExprIndex.OptIndex,
            init_value: ExprIndex.OptIndex,
        },
        block_statement: struct {
            first_child: StmtIndex.OptIndex,
        },
        expression_statement: struct {
            expr: ExprIndex.Index,
        },
        return_statement: struct {
            expr: ExprIndex.OptIndex,
        },
        if_statement: struct {
            condition: ExprIndex.Index,
            first_taken: StmtIndex.OptIndex,
            first_not_taken: StmtIndex.OptIndex,
        },
        loop_statement: struct {
            condition: ExprIndex.OptIndex,
            first_child: StmtIndex.OptIndex,
        },
        switch_statement: struct {
            first_child: ExprIndex.OptIndex,
        },
        case_label: struct {
            expr: ExprIndex.Index,
        },
        unreachable_statement,
        break_statement: struct {
            //label: ?SourceRef,
            value: ExprIndex.OptIndex,
        },
    },
};

pub const FunctionExpression = struct {
    first_param: FunctionParamIndex.OptIndex,
    return_type: ExprIndex.Index,
    body: StmtIndex.OptIndex,
    return_location: ?SourceRef,
    is_inline: bool,
};

pub const FunctionParameter = struct {
    identifier: ?SourceRef,
    type: ExprIndex.Index,
    next: FunctionParamIndex.OptIndex = .none,
    is_comptime: bool,
};

pub const TypeInitValue = struct {
    identifier: ?SourceRef,
    value: ExprIndex.Index,
    next: TypeInitValueIndex.OptIndex = .none,
};

fn makeIndent(indent_level: usize) []const u8 {
    return (" " ** 4096)[0..indent_level * 2];
}

fn dumpStatementChain(first_stmt: StmtIndex.OptIndex, indent_level: usize) anyerror!void {
    if(first_stmt == .empty_block or first_stmt == .none) {
        std.debug.print("{{}}", .{});
        return;
    }

    std.debug.print("{{", .{});

    var curr_stmt = first_stmt;
    while(statements.getOpt(curr_stmt)) |stmt| {
        std.debug.print("\n{s}", .{makeIndent(indent_level + 1)});
        try dumpNode(stmt, indent_level + 1);
        curr_stmt = stmt.next;
    }

    std.debug.print("\n{s}}}", .{makeIndent(indent_level)});
}

fn dumpNode(node: anytype, indent_level: usize) anyerror!void {
    switch(@TypeOf(node)) {
        *sources.SourceFile => {
            const index = sources.source_files.getIndex(node);
            std.debug.print("SourceFile#{d} {s}", .{@enumToInt(index), node.realpath});
        },
        *ExpressionNode => switch(node.*) {
            .identifier, .int_literal, .char_literal, .string_literal => |ident| std.debug.print("{s}", .{try ident.toSlice()}),
            .bool_literal => |value| std.debug.print("{}", .{value}),
            .void, .anyopaque, .bool, .type, .undefined, .noreturn => std.debug.print("{s}", .{@tagName(node.*)}),
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
                try dumpNode(expressions.get(ptr_type.child), indent_level);
            },
            .imported_file => |file_index| {
                std.debug.print("(", .{});
                try dumpNode(sources.source_files.get(file_index), indent_level);
                std.debug.print(")", .{});
            },
            .function_call => |call| {
                try dumpNode(expressions.get(call.callee), indent_level);
                std.debug.print("(", .{});
                var curr_arg = call.first_arg;
                while(expressions.getOpt(curr_arg)) |arg| {
                    const func_arg = arg.function_argument;
                    try dumpNode(expressions.get(func_arg.value), indent_level);
                    if(func_arg.next != .none) {
                        std.debug.print(", ", .{});
                    }
                    curr_arg = func_arg.next;
                }
                std.debug.print(")", .{});
            },
            .addr_of, .deref => |uop| {
                try dumpNode(expressions.get(uop.operand), indent_level);
                switch(node.*) {
                    .addr_of => std.debug.print(".&", .{}),
                    .deref => std.debug.print(".*", .{}),
                    else => unreachable,
                }
            },
            .member_access => |bop| {
                try dumpNode(expressions.get(bop.lhs), indent_level);
                std.debug.print(".", .{});
                try dumpNode(expressions.get(bop.rhs), indent_level);
            },
            .parenthesized => |uop| {
                std.debug.print("(", .{});
                try dumpNode(expressions.get(uop.operand), indent_level);
                std.debug.print(")", .{});
            },
            .multiply, .multiply_eq, .multiply_mod, .multiply_mod_eq,
            .divide, .divide_eq, .modulus, .modulus_eq,
            .plus, .plus_eq, .plus_mod, .plus_mod_eq,
            .minus, .minus_eq, .minus_mod, .minus_mod_eq,
            .shift_left, .shift_left_eq, .shift_right, .shift_right_eq,
            .bitand, .bitand_eq, .bitor, .bitxor_eq, .bitxor, .bitor_eq,
            .less, .less_equal, .greater, .greater_equal, .equals, .not_equal,
            .logical_and, .logical_or, .assign, .range, .array_concat,
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
                    .array_concat => "++",
                    else => unreachable,
                };

                try dumpNode(expressions.get(bop.lhs), indent_level);
                std.debug.print(" {s} ", .{op});
                try dumpNode(expressions.get(bop.rhs), indent_level);
            },
            .discard_underscore => std.debug.print("_", .{}),
            .unary_plus, .unary_minus, .unary_bitnot, .unary_lognot => |uop| {
                const op: u8 = switch(node.*) {
                    .unary_plus => '+',
                    .unary_minus => '-',
                    .unary_bitnot => '~',
                    .unary_lognot => '!',
                    else => unreachable,
                };
                std.debug.print("{c}", .{op});
                try dumpNode(expressions.get(uop.operand), indent_level);
            },
            .function_expression => |func_idx| try dumpNode(functions.get(func_idx), indent_level),
            .struct_expression => |expr| {
                std.debug.print("struct ", .{});
                try dumpStatementChain(expr.first_decl, indent_level);
            },
            .array_subscript => |bop| {
                try dumpNode(expressions.get(bop.lhs), indent_level);
                std.debug.print("[", .{});
                try dumpNode(expressions.get(bop.rhs), indent_level);
                std.debug.print("]", .{});
            },
            .array_type => |bop| {
                std.debug.print("[", .{});
                try dumpNode(expressions.get(bop.lhs), indent_level);
                std.debug.print("]", .{});
                try dumpNode(expressions.get(bop.rhs), indent_level);
            },
            .force_comptime_eval => |uop| {
                std.debug.print("comptime ", .{});
                try dumpNode(expressions.get(uop.operand), indent_level);
            },
            .builtin_function => |bi| std.debug.print("@{s}", .{@tagName(bi)}),
            .type_init_list => |til| {
                if(ExprIndex.unwrap(til.specified_type)) |st| {
                    try dumpNode(expressions.get(st), indent_level);
                } else {
                    std.debug.print(".", .{});
                }
                std.debug.print("{{", .{});
                var curr = til.first_value;
                if(curr == .none) {
                    std.debug.print("}}", .{});
                    return;
                }
                std.debug.print("\n", .{});
                while(type_init_values.getOpt(curr)) |value| : (curr = value.next) {
                    std.debug.print("{s}", .{makeIndent(indent_level + 1)});
                    if(value.identifier) |ident| {
                        std.debug.print(".{s} = ", .{try ident.toSlice()});
                    }
                    try dumpNode(expressions.get(value.value), indent_level + 1);
                    std.debug.print(",\n", .{});
                }
                std.debug.print("{s}}}", .{makeIndent(indent_level)});
            },
            .block_expression => |blk| try dumpStatementChain(blk.block, indent_level),
            else => |expr| std.debug.panic("Cannot dump expression of type {s}", .{@tagName(expr)}),
        },
        *StatementNode => switch(node.value) {
            .expression_statement => |expr| {
                try dumpNode(expressions.get(expr.expr), indent_level);
                std.debug.print(";", .{});
            },
            .block_statement => |blk| try dumpStatementChain(blk.first_child, indent_level),
            .declaration => |decl| {
                const decl_kw = if (decl.mutable) "var" else "const";
                std.debug.print("{s} {s}", .{decl_kw, try decl.identifier.toSlice()});
                if(ExprIndex.unwrap(decl.type)) |type_idx| {
                    std.debug.print(": ", .{});
                    try dumpNode(expressions.get(type_idx), indent_level);
                }
                std.debug.print(" = ", .{});
                try dumpNode(expressions.get(decl.init_value), indent_level);
                std.debug.print(";", .{});
            },
            .field_decl => |decl| {
                std.debug.print("{s}", .{try decl.identifier.toSlice()});
                if(ExprIndex.unwrap(decl.type)) |type_idx| {
                    std.debug.print(": ", .{});
                    try dumpNode(expressions.get(type_idx), indent_level);
                }
                if(ExprIndex.unwrap(decl.init_value)) |init_idx| {
                    std.debug.print(" = ", .{});
                    try dumpNode(expressions.get(init_idx), indent_level);
                }
                std.debug.print(",", .{});
            },
            .if_statement => |stmt| {
                std.debug.print("if (", .{});
                try dumpNode(expressions.get(stmt.condition), indent_level);
                std.debug.print(") ", .{});
                try dumpStatementChain(stmt.first_taken, indent_level);
                if(stmt.first_not_taken != .empty_block and stmt.first_not_taken != .none) {
                    std.debug.print(" else ", .{});
                    try dumpStatementChain(stmt.first_not_taken, indent_level);
                }
            },
            .loop_statement => |stmt| {
                std.debug.print("loop ", .{});
                if(ExprIndex.unwrap(stmt.condition)) |cond_idx| {
                    std.debug.print("(", .{});
                    try dumpNode(expressions.get(cond_idx), indent_level);
                    std.debug.print(") ", .{});
                }
                try dumpStatementChain(stmt.first_child, indent_level);
            },
            .break_statement => |stmt| {
                std.debug.print("break", .{});
                if(ExprIndex.unwrap(stmt.value)) |value| {
                    std.debug.print(" ", .{});
                    try dumpNode(expressions.get(value), indent_level);
                }
                std.debug.print(";", .{});
            },
            .return_statement => |stmt| {
                std.debug.print("return", .{});
                if(expressions.getOpt(stmt.expr)) |expr| {
                    std.debug.print(" ", .{});
                    try dumpNode(expr, indent_level);
                }
                std.debug.print(";", .{});
            },
            .unreachable_statement => std.debug.print("unreachable;", .{}),
            else => |stmt| std.debug.panic("Cannot dump statement of type {s}", .{@tagName(stmt)}),
        },
        *FunctionExpression => {
            std.debug.print("fn(", .{});
            var curr_param = node.first_param;
            while(function_params.getOpt(curr_param)) |param| {
                if(param.identifier) |ident| std.debug.print("{s}: ", .{try ident.toSlice()});
                try dumpNode(expressions.get(param.type), indent_level);
                if(param.next != .none) {
                    std.debug.print(", ", .{});
                }
                curr_param = param.next;
            }
            std.debug.print(") ", .{});
            if(node.return_location) |ret_loc| {
                std.debug.print("|{s}| ", .{try ret_loc.toSlice()});
            }
            try dumpNode(expressions.get(node.return_type), indent_level);
            std.debug.print(" ", .{});
            try dumpStatementChain(node.body, indent_level);
        },
        else => @compileError("Cannot dump type " ++ @typeName(@TypeOf(node))),
    }
}

pub fn dumpFile(file: *sources.SourceFile) !void {
    try dumpNode(file, 0);
    std.debug.print("\n{s}", .{makeIndent(1)});
    try dumpNode(expressions.get(file.top_level_struct), 1);
    std.debug.print("\n", .{});
}

pub var expressions: ExpressionList = undefined;
pub var statements: StatementList = undefined;
pub var functions: FunctionList = undefined;
pub var function_params: FunctionParamList = undefined;
pub var type_init_values: TypeInitValueList = undefined;

pub fn init() !void {
    expressions = try ExpressionList.init(std.heap.page_allocator);
    statements = try StatementList.init(std.heap.page_allocator);
    functions = try FunctionList.init(std.heap.page_allocator);
    function_params = try FunctionParamList.init(std.heap.page_allocator);
    type_init_values = try TypeInitValueList.init(std.heap.page_allocator);
}

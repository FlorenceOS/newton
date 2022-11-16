const std = @import("std");

const indexed_list = @import("indexed_list.zig");
const sources = @import("sources.zig");
const tokenizer = @import("tokenizer.zig");
const values = @import("values.zig");

const ExpressionList = indexed_list.IndexedList(ExprIndex, ExpressionNode);
const StatementList = indexed_list.IndexedList(StmtIndex, StatementNode);
const FunctionList = indexed_list.IndexedList(FunctionIndex, FunctionExpression);
const FunctionParamList = indexed_list.IndexedList(FunctionParamIndex, FunctionParameter);

pub const ExprIndex = indexed_list.Indices(u32, .{
    // Commonly used constants
    .@"undefined" = .{ .undefined_expr = {}},
    .@"unreachable" = .{ .unreachable_expr = {}},

    // Commonly used types
    .void = .{ .void = {} },
    .anyopaque = .{ .anyopaque = {} },
    .bool = .{ .bool = {} },
    .type = .{ .type = {} },
    .u8 = .{ .unsigned_int = 8 },
    .u16 = .{ .unsigned_int = 16 },
    .u32 = .{ .unsigned_int = 32 },
    .u64 = .{ .unsigned_int = 64 },
    .i8 = .{ .signed_int = 8 },
    .i16 = .{ .signed_int = 16 },
    .i32 = .{ .signed_int = 32 },
    .i64 = .{ .signed_int = 64 },

    .import = .{.import = {}},

    // _ = a;
    // ^ This thing
    .discard_underscore = .{ .discard_underscore = {} },
});
pub const StmtIndex = indexed_list.Indices(u32, .{
    .empty_return = .{ .next = .none, .value = .{
        .return_statement = .{ .expr = .none },
    } },
    .empty_block = .{ .next = .none, .value = .{
        .block_statement = .{ .first_child = .none },
    } },
});
pub const FunctionIndex = indexed_list.Indices(u32, .{});
pub const FunctionParamIndex = indexed_list.Indices(u32, .{});

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
    item: ExprIndex.Index,
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
    next: ExprIndex.OptIndex,
};

pub const FunctionCall = struct {
    callee: ExprIndex.Index,
    first_arg: ExprIndex.OptIndex,
};

pub const ExpressionNode = union(enum) {
    identifier: SourceRef,
    int_literal: SourceRef,
    char_literal: SourceRef,
    string_literal: SourceRef,
    bool_literal: bool,

    // @import
    import,
    // @import("whatever")
    import_call: sources.SourceIndex.Index,

    parenthesized: Uop,
    unary_plus: Uop,
    unary_minus: Uop,
    unary_bitnot: Uop,
    unary_lognot: Uop,
    pointer_type: PointerType,

    addr_of: Uop,
    deref: Uop,

    undefined_expr,
    unreachable_expr,
    discard_underscore,

    void,
    anyopaque,
    bool,
    type,
    unsigned_int: u32,
    signed_int: u32,

    // Binary expressions, has lhs and rhs populated
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

    function_expression: FunctionIndex.Index,

    // Function calls
    function_call: FunctionCall,
    function_argument: FunctionArgument,

    struct_expression: TypeBody,
};

pub const StatementNode = struct {
    next: StmtIndex.OptIndex,

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
    },
};

pub const FunctionExpression = struct {
    first_param: FunctionParamIndex.OptIndex,
    return_type: ExprIndex.Index,
    body: StmtIndex.OptIndex,
};

pub const FunctionParameter = struct {
    identifier: SourceRef,
    type: ExprIndex.Index,
    next: FunctionParamIndex.OptIndex,
};

pub var expressions: ExpressionList = undefined;
pub var statements: StatementList = undefined;
pub var functions: FunctionList = undefined;
pub var function_params: FunctionParamList = undefined;

pub fn init() !void {
    expressions = try ExpressionList.init(std.heap.page_allocator);
    statements = try StatementList.init(std.heap.page_allocator);
    functions = try FunctionList.init(std.heap.page_allocator);
    function_params = try FunctionParamList.init(std.heap.page_allocator);
}

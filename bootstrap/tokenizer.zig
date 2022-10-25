const std = @import("std");

pub const Token = union(enum) {
    end_of_file,

    identifier: struct {
        owned: bool,
        body: []const u8,
        value: []const u8,

        pub fn format(
            self: @This(),
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            _ = fmt;
            _ = options;
            try writer.print("'{s}'", .{std.fmt.fmtSliceEscapeUpper(self.value)});
        }


        pub fn deinit(self: @This()) void {
            if(self.owned) {
                gpa.allocator().free(self.value);
            }
        }
    },
    int_literal: struct {
        body: []const u8,
        value: usize,
    },
    char_literal: struct {
        body: []const u8,
        value: usize,
    },
    string_literal: struct {
        body: []const u8,
        value: [:0]u8,

        pub fn deinit(self: @This()) void {
            gpa.allocator().free(self.value);
        }
    },

    @".._ch",
    @"._ch",
    @",_ch",
    @":_ch",
    @";_ch",

    @"=_ch",
    @"+_ch",
    @"+=_ch",
    @"+%_ch",
    @"+%=_ch",
    @"++_ch",
    @"++=_ch",
    @"-_ch",
    @"-=_ch",
    @"-%_ch",
    @"-%=_ch",
    @"*_ch",
    @"*=_ch",
    @"*%_ch",
    @"*%=_ch",
    @"/_ch",
    @"/=_ch",
    @"%_ch",
    @"%=_ch",
    @"{_ch",
    @"}_ch",
    @"(_ch",
    @")_ch",
    @"[_ch",
    @"]_ch",

    @"==_ch",
    @"!=_ch",

    @"<_ch",
    @"<=_ch",
    @"<<_ch",
    @"<<=_ch",

    @">_ch",
    @">=_ch",
    @">>_ch",
    @">>=_ch",

    @"&_ch",
    @"&=_ch",
    @"|_ch",
    @"|=_ch",
    @"^_ch",
    @"^=_ch",

    @"&&_ch",
    @"||_ch",
    @"!_ch",

    @"~_ch",

    break_keyword,
    case_keyword,
    const_keyword,
    continue_keyword,
    else_keyword,
    endcase_keyword,
    enum_keyword,
    fn_keyword,
    if_keyword,
    loop_keyword,
    return_keyword,
    struct_keyword,
    switch_keyword,
    var_keyword,
    volatile_keyword,
    __keyword,


    bool_keyword,
    type_keyword,
    void_keyword,
    anyopaque_keyword,

    pub fn deinit(self: @This()) void {
        switch(self) {
            .string_literal => |sl| sl.deinit(),
            .identifier => |i| i.deinit(),
            else => {},
        }
    }

    pub fn identifier_value(self: @This()) []const u8 {
        switch(self) {
            .identifier => |i| return i.value,
            else => unreachable,
        }
    }
};

fn skipWhitespace(input: *[*:0]const u8) void {
    while(true) {
        switch(input.*[0]) {
            ' ', '\t', '\n', '\r' => input.* += 1,
            '/' => {
                if(input.*[1] == '/') { // Line comment
                    input.* += 2;
                    while(input.*[0] != '\n') {
                        input.* += 1;
                    }
                    continue;
                } else return;
            },
            else => return,
        }
    }
}

fn lengthSort(_: void, lhs: []const u8, rhs: []const u8) bool {
    return !(lhs.len < rhs.len);
}

const keywords = blk: {
    @setEvalBranchQuota(9999999);
    comptime var result: []const []const u8 = &[_][]const u8{};

    inline for(@typeInfo(Token).Union.fields) |ef| {
        if(std.mem.endsWith(u8, ef.name, "_keyword")) {
            result = result ++ [_][]const u8{ef.name[0..ef.name.len-8]};
        }
    }

    var sorted_result = result[0..result.len].*;
    std.sort.sort([]const u8, &sorted_result, {}, lengthSort);
    break :blk sorted_result;
};

const character_tokens = blk: {
    @setEvalBranchQuota(9999999);
    comptime var result: []const []const u8 = &[_][]const u8{};

    inline for(@typeInfo(Token).Union.fields) |ef| {
        if(std.mem.endsWith(u8, ef.name, "_ch")) {
            result = result ++ [_][]const u8{ef.name[0..ef.name.len-3]};
        }
    }

    var sorted_result = result[0..result.len].*;
    std.sort.sort([]const u8, &sorted_result, {}, lengthSort);
    break :blk sorted_result;
};

fn startsWith(haystack: [*:0]const u8, needle: []const u8) bool {
    for(needle) |c, i| {
        std.debug.assert(haystack[i] != 0);
        if(c != haystack[i]) return false;
    }
    return true;
}

fn isIdentChar(value: u8) bool {
    switch(value) {
        'a'...'z',
        'A'...'Z',
        '0'...'9',
        '_', '@' => return true,
        else => return false,
    }
}

fn keywordOrIdent(input: *[*:0]const u8) !Token {
    inline for(keywords) |kw| {
        if(startsWith(input.*, kw) and !isIdentChar(input.*[kw.len])) {
            input.* += kw.len;
            return @unionInit(Token, kw ++ "_keyword", {});
        }
    }

    if(std.mem.eql(u8, input.*[0..2], "@\"")) {
        var value = std.ArrayList(u8).init(gpa.allocator());
        input.* += 2;

        const body_start = @ptrCast([*]const u8, input.*);
        while(input.*[0] != '"') {
            try value.append(try parseLiteralChar(input));
        }

        input.* += 1; // Also skip end quote

        return Token{ .identifier = .{
            .body = body_start[0..(@ptrToInt(input.*) - 1) - @ptrToInt(body_start)],
            .value = value.toOwnedSlice(),
            .owned = true,
        } };
    } else {
        const start = @ptrCast([*]const u8, input.*);

        while(isIdentChar(input.*[0])) {
            input.* += 1;
        }

        const ident_slice = start[0..@ptrToInt(input.*) - @ptrToInt(start)];

        return Token{ .identifier = .{
            .body = ident_slice,
            .value = ident_slice,
            .owned = false,
        } };
    }
}

var gpa = std.heap.GeneralPurposeAllocator(.{}){.backing_allocator = std.heap.page_allocator};

fn parseLiteralChar(input: *[*:0]const u8) !u8 {
    switch(input.*[0]) {
        '\\' => {
            if(input.*[1] == 'x') {
                const retval = std.fmt.parseUnsigned(u8, input.*[2..4], 16);
                input.* += 4;
                return retval;
            }
            else {
                const retval = input.*[1];
                input.* += 2;
                return retval;
            }
        },
        0 => return error.UnterminatedLiteral,
        else => {
            const retval = input.*[0];
            input.* += 1;
            return retval;
        },
    }
}

fn digitValue(ch: u8, radix: usize) ?usize {
    const value = switch(ch) {
        inline '0'...'9' => |val| val - '0',
        inline 'a'...'z' => |val| val - 'a' + 10,
        inline 'A'...'Z' => |val| val - 'A' + 10,
        else => return null,
    };

    if(value >= radix) return null;
    return value;
}

fn parseIntLiteralWithRadix(input: *[*:0]const u8, offset: usize, comptime radix: comptime_int) !Token {
    var current_value: usize = 0;
    var current_offset: usize = offset;

    while(digitValue(input.*[current_offset], radix)) |digit| : (current_offset += 1) {
        current_value *= radix;
        current_value += digit;
    }

    const body = input.*[0..current_offset];
    input.* += current_offset;
    return .{ .int_literal = .{
        .body = body,
        .value = current_value,
    }};
}

fn parseIntLiteral(input: *[*:0]const u8) !Token {
    if(input.*[0] == '0') {
        switch(input.*[1]) {
            'x' => return parseIntLiteralWithRadix(input, 2, 16),
            'o' => return parseIntLiteralWithRadix(input, 2, 8),
            'b' => return parseIntLiteralWithRadix(input, 2, 2),
            else => return parseIntLiteralWithRadix(input, 1, 8),
        }
    } else {
        return parseIntLiteralWithRadix(input, 0, 10);
    }
}

pub fn tokenize(input: *[*:0]const u8) !Token {
    skipWhitespace(input);

    switch(input.*[0]) {
        0 => return Token{.end_of_file = {}},
        '~', '!', '|', '&', '^', '>', '<', '=', '[', ']', '(', ')', '{', '}',
        '%', '/', '*', '-', '+', ';', ':', ',', '.',
        => {
            inline for (character_tokens) |ch| {
                if(startsWith(input.*, ch)) {
                    input.* += ch.len;
                    return @unionInit(Token, ch ++ "_ch", {});
                }
            }
            unreachable;
        },
        'a'...'z',
        'A'...'Z',
        '@', '_',
        => return keywordOrIdent(input),
        '"' => {
            var value = std.ArrayList(u8).init(gpa.allocator());

            const body_start = @ptrCast([*]const u8, input.*);
            input.* += 1;

            while(input.*[0] != '"') {
                try value.append(try parseLiteralChar(input));
            }

            input.* += 1; // Also skip quotes

            return Token{ .string_literal = .{
                .body = body_start[0..(@ptrToInt(input.*) - 1) - @ptrToInt(body_start)],
                .value = try value.toOwnedSliceSentinel(0),
            } };
        },

        '\'' => {
            const body_start = @ptrCast([*]const u8, input.*);
            input.* += 1;
            const value = try parseLiteralChar(input);

            std.debug.assert(input.*[0] == '\'');
            input.* += 1;

            return Token{ .char_literal = . {
                .body = body_start[0..(@ptrToInt(input.*) - 1) - @ptrToInt(body_start)],
                .value = value,
            } };
        },
        '0'...'9' => return parseIntLiteral(input),
        else => |ch| std.debug.panic("Unknown first chr '{c}' (0x{X})", .{ch, ch}),
    }
}

pub fn tokenLength(input_c: [*:0]const u8) !usize {
    var input = input_c;
    skipWhitespace(&input);

    const prev = input;
    _ = try tokenize(&input);
    return @ptrToInt(input) - @ptrToInt(prev);
}

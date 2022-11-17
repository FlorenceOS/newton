const std = @import("std");

const indexed_list = @import("indexed_list.zig");

pub const TypeIndex = indexed_list.Indices(u32, opaque{}, .{
    .bool = .{.bool = {}},
    .type = .{.type = {}},
    .void = .{.void = {}},
    .anyopaque  = .{.anyopaque = {}},
    .u8 = .{.unsigned_int = .{ .num_bits = 8 }},
    .u16 = .{.unsigned_int = .{ .num_bits = 16 }},
    .u32 = .{.unsigned_int = .{ .num_bits = 32 }},
    .u64 = .{.unsigned_int = .{ .num_bits = 64 }},
    .i8 = .{.signed_int = .{ .num_bits = 8 }},
    .i16 = .{.signed_int = .{ .num_bits = 16 }},
    .i32 = .{.signed_int = .{ .num_bits = 32 }},
    .i64 = .{.signed_int = .{ .num_bits = 64 }},
});
const TypeList = indexed_list.IndexedList(TypeIndex, Type);
pub var all_types: TypeList = undefined;

pub fn init() !void {
    all_types = try TypeList.init(std.heap.page_allocator);
}

pub const PointerIndex = indexed_list.Indices(u32, opaque{}, .{});

pub const PointerType = struct {
    child: TypeIndex.Index,

    // TODO
    //memory_island: memory_island.Index,
    //offset: memory_island.Offset,
};

// pub const PointerValue = struct {
//     child: TypeIndex.Index,

//     // TODO
//     //memory_island: memory_island.Index,
//     //offset: memory_island.Offset,
// };

pub const IntegerType = struct {
    num_bits: u32,
};

// pub const IntegerValue = struct {
//     bits: ?usize,
//     num_bits: u32,
// };

// pub const BooleanValue = struct {
//     value: ?bool,
// };

pub const Type = union(enum) {
    bool,
    type,
    void,
    anyopaque,
    signed_int: IntegerType,
    unsigned_int: IntegerType,
    pointer_to_var: PointerType,
    pointer_to_volatile_var: PointerType,
    pointer_to_const: PointerType,
    pointer_to_volatile_const: PointerType,
};

pub fn unsigned(num_bits: u32) TypeIndex.Index {
    return switch(num_bits) {
        8 => .u8,
        16 => .u16,
        32 => .u32,
        64 => .u64,
        else => all_types.addDedupLinear(.{.unsigned_int = .{.num_bits = num_bits}}),
    };
}

pub fn signed(num_bits: u32) TypeIndex.Index {
    return switch(num_bits) {
        8 => .i8,
        16 => .i16,
        32 => .i32,
        64 => .i64,
        else => all_types.addDedupLinear(.{.signed_int = .{.num_bits = num_bits}}),
    };
}

// pub const ExpressionValue = union(enum) {
//     @"undefined",
//     type: TypeIndex.Index,
//     void,
//     anyopaque,
//     bool: bool,
//     scope,
// };

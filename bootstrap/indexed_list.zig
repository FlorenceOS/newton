const std = @import("std");
const builtin = @import("builtin");

fn sliceIndex(comptime T: type, ptr: *T, slice: []T) usize {
    return @divExact((@ptrToInt(ptr) - @ptrToInt(slice.ptr)), @sizeOf(T));
}

pub fn Indices(comptime IndexType: type, comptime extra_field_tags: anytype) type {
    comptime var extra_fields: []const std.builtin.Type.EnumField = &[_]std.builtin.Type.EnumField{};
    comptime var current_value = 0;

    inline for(@typeInfo(@TypeOf(extra_field_tags)).Struct.fields) |tag_field| {
        extra_fields = extra_fields ++ &[_]std.builtin.Type.EnumField{.{
            .name = tag_field.name,
            .value = current_value,
        } };
        current_value += 1;
    }

    const _Index = @Type(std.builtin.Type{ .Enum = .{
        .layout = .Auto,
        .tag_type = IndexType,
        .fields = extra_fields,
        .decls = &[_]std.builtin.Type.Declaration{},
        .is_exhaustive = false,
    }});

    extra_fields = extra_fields ++ &[_]std.builtin.Type.EnumField{.{
        .name = "none",
        .value = current_value,
    } };
    current_value += 1;

    const _OptIndex = @Type(std.builtin.Type{ .Enum = .{
        .layout = .Auto,
        .tag_type = IndexType,
        .fields = extra_fields,
        .decls = &[_]std.builtin.Type.Declaration{},
        .is_exhaustive = false,
    }});

    return struct {
        pub const Index = _Index;
        pub const OptIndex = _OptIndex;
        pub const ExtraFieldTags = extra_field_tags;
        pub const alloc_base = current_value;

        pub fn unwrap(oi: _OptIndex) ?_Index {
            if(oi == .none) return null;
            return @intToEnum(_Index, @enumToInt(oi));
        }

        pub fn toOpt(i: _Index) _OptIndex {
            return @intToEnum(_OptIndex, @enumToInt(i));
        }
    };
}

pub fn IndexedList(comptime _Indices: type, comptime T: anytype) type {
    std.debug.assert(@sizeOf(T) >= @sizeOf(_Indices.Index));

    return struct {
        const List = @This();
        pub const Index = _Indices.Index;
        pub const OptIndex = _Indices.OptIndex;

        elements: std.ArrayList(T),
        first_free: OptIndex,

        pub fn init(allocator: std.mem.Allocator) !@This() {
            var result = @This() {
                .elements = try std.ArrayList(T).initCapacity(allocator, 2048),
                .first_free = .none,
            };
            errdefer result.deinit();

            inline for(@typeInfo(@TypeOf(_Indices.ExtraFieldTags)).Struct.fields) |tag_field| {
                try result.elements.append(@field(_Indices.ExtraFieldTags, tag_field.name));
            }

            _ = try result.elements.addOne();
            std.debug.assert(result.elements.items.len == _Indices.alloc_base);

            return result;
        }

        pub fn deinit(self: *@This()) void {
            self.elements.deinit();
        }

        pub fn clear(self: *@This()) void {
            self.elements.shrinkRetainingCapacity(_Indices.alloc_base);
            self.first_free = .none;
        }

        /// Allocate a slot for a new object
        pub fn addOne(self: *@This()) !*T {
            if (self.getOpt(self.first_free)) |first_free| {
                self.first_free = @ptrCast(*OptIndex, first_free).*;
                return first_free;
            }
            return try self.elements.addOne();
        }

        pub fn addDedupLinear(self: *@This(), val: T) !Index {
            // Skip .none
            for(self.elements.items[1..]) |item, i| {
                if(item == val) {
                    return @intToEnum(Index, i);
                }
            }
            return self.insert(val);
        }

        /// Add an object to the list and return its id
        pub fn insert(self: *@This(), b: T) !Index {
            const ptr = try self.addOne();
            ptr.* = b;
            return self.getIndex(ptr);
        }

        /// Free a slot by index
        pub fn free(self: *@This(), idx: Index) void {
            @ptrCast(*OptIndex, self.get(idx)).* = self.first_free;
            self.first_free = idx.toOpt();
        }

        /// Free a slot by pointer
        pub fn delete(self: *@This(), obj: *T) void {
            self.free(self.getIndex(obj));
        }

        /// Get a slot index by pointer
        pub fn getIndex(self: *@This(), val: *T) Index {
            return @intToEnum(Index, sliceIndex(T, val, self.elements.items));
        }

        /// Get a slot pointer by index
        pub fn get(self: *@This(), idx: Index) *T {
            return &self.elements.items[@enumToInt(idx)];
        }

        /// Get an optional slot pointer by optional index
        pub fn getOpt(self: *@This(), idx: OptIndex) ?*T {
            return self.get(_Indices.unwrap(idx) orelse return null);
        }
    };
}

fn testImpl(l: anytype) !void {
    // Add some objects
    const idx_one = try l.insert(.{});
    try std.testing.expectEqual(idx_one, 1);

    const ptr_two = try l.addOne();
    try std.testing.expectEqual(l.getIndex(ptr_two), 2);

    try std.testing.expectEqual(l.elements.items.len, 3);

    // Make sure freelist works
    try std.testing.expectEqual(l.free_list, 0);
    l.delete(ptr_two);
    try std.testing.expectEqual(l.free_list, 2);
    try std.testing.expectEqual(l.get(2).next, 0);
    l.free(idx_one);
    try std.testing.expectEqual(l.free_list, 1);
    try std.testing.expectEqual(l.get(1).next, 2);
    try std.testing.expectEqual(l.get(2).next, 0);

    // Make sure freed objects are reused
    try std.testing.expectEqual(try l.insert(.{}), 1);

    try std.testing.expectEqual(l.free_list, 2);
    try std.testing.expectEqual(l.get(2).next, 0);

    try std.testing.expectEqual(try l.addOne(), l.get(2));
    try std.testing.expectEqual(l.free_list, 0);
}

fn testList(l: anytype) !void {
    try testImpl(l);
    l.clear();
    try testImpl(l);
}

test "IndexedList" {
    const TestT = struct {
        next: u32 = undefined,
    };

    var l = try IndexedList(TestT).init(std.testing.allocator);
    defer l.deinit();

    try testList(&l);
}

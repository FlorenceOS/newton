const std = @import("std");

const ir = @import("ir.zig");
const rega = @import("rega.zig");

pub const x86_64 = @import("x86_64.zig");

const RelocationType = enum {
    rel32_post_0,
};

const Relocation = struct {
    relocation_type: RelocationType,
    output_offset: usize,

    fn size(self: @This()) usize {
        return switch(self.relocation_type) {
            .rel32_post_0 => 4,
        };
    }

    fn resolve(self: @This(), output_bytes: []u8, relocation_target_offset: usize) void {
        switch(self.relocation_type) {
            .rel32_post_0 => {
                const rel = relocation_target_offset -% (self.output_offset +% 4);
                output_bytes[self.output_offset..][0..4].* = std.mem.toBytes(@intCast(i32, @bitCast(i64, rel)));
            },
        }
    }
};

pub fn Writer(comptime Platform: type) type {
    return struct {
        allocator: std.mem.Allocator = std.heap.page_allocator,
        output_bytes: std.ArrayListUnmanaged(u8) = .{},
        enqueued_blocks: std.AutoArrayHashMapUnmanaged(ir.BlockIndex.Index, std.ArrayListUnmanaged(Relocation)) = .{},
        placed_blocks: std.AutoHashMapUnmanaged(ir.BlockIndex.Index, usize) = .{},
        uf: rega.UnionFind,

        pub fn attemptInlineEdge(self: *@This(), edge: ir.BlockEdgeIndex.Index) !?ir.BlockIndex.Index {
            const target_block = ir.edges.get(edge).target_block;
            if(self.placed_blocks.get(target_block)) |_| {
                return null;
            }
            if(!self.placed_blocks.contains(target_block)) {
                _ = try self.enqueued_blocks.getOrPutValue(self.allocator, target_block, .{});
            }
            return target_block;
        }

        pub fn writeRelocatedValue(self: *@This(), edge: ir.BlockEdgeIndex.Index, reloc_type: RelocationType) !void {
            const reloc_target = ir.edges.get(edge).target_block;
            const reloc = Relocation{
                .output_offset = self.output_bytes.items.len,
                .relocation_type = reloc_type,
            };

            const sz = reloc.size();
            try self.output_bytes.appendNTimes(self.allocator, 0xCC, sz);

            if(self.placed_blocks.get(reloc_target)) |offset| {
                reloc.resolve(self.output_bytes.items, offset);
            } else if(self.enqueued_blocks.getPtr(reloc_target)) |q| {
                try q.append(self.allocator, reloc);
            } else {
                var queue = std.ArrayListUnmanaged(Relocation){};
                try queue.append(self.allocator, reloc);
                try self.enqueued_blocks.put(self.allocator, reloc_target, queue);
            }
        }

        pub fn writeInt(self: *@This(), comptime T: type, value: T) !void {
            try self.output_bytes.appendSlice(self.allocator, &std.mem.toBytes(value));
        }

        fn writeBlock(self: *@This(), bidx: ir.BlockIndex.Index) !?ir.BlockIndex.Index {
            var block = ir.blocks.get(bidx);
            var current_instr = block.first_decl;

            try self.placed_blocks.put(self.allocator, bidx, self.output_bytes.items.len);
            while(ir.decls.getOpt(current_instr)) |instr| {
                const next_block: ?ir.BlockIndex.Index = try Platform.writeDecl(self, ir.decls.getIndex(instr), self.uf);
                if(next_block) |nb| return nb;
                current_instr = instr.next;
            }
            return null;
        }

        pub fn writeFunction(self: *@This(), head_block: ir.BlockIndex.Index) !void {
            try self.enqueued_blocks.put(self.allocator, head_block, .{});
            var preferred_block: ?ir.BlockIndex.Index = null;

            while(true) {
                var current_block: ir.BlockIndex.Index = undefined;
                var block_relocs: std.ArrayListUnmanaged(Relocation) = undefined;

                if(preferred_block) |blk| {
                    current_block = blk;
                    block_relocs = self.enqueued_blocks.fetchSwapRemove(current_block).?.value;
                    preferred_block = null;
                } else {
                    const block = self.enqueued_blocks.popOrNull() orelse break;
                    current_block = block.key;
                    block_relocs = block.value;
                }

                for(block_relocs.items) |reloc| {
                    reloc.resolve(self.output_bytes.items, self.output_bytes.items.len);
                }
                block_relocs.deinit(self.allocator);

                preferred_block = try self.writeBlock(current_block);
            }

            std.debug.print("Output: {}\n", .{std.fmt.fmtSliceHexUpper(self.output_bytes.items)});
        }
    };
}

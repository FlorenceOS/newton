const std = @import("std");

const backends = @import("backends.zig");

pub const BASE_VADDR = 0x100000;

const SH_NULL = 0;
const SH_TEXT = 1;
const SH_SHSTRTAB = 2;
const SH_SYMTAB = 3;
const SH_SYMSTRTAB = 4;

const ShStrTab = extern struct {
    null_name: u8 = 0,
    text_name: [6]u8 = ".text\x00".*,
    shstrtab_name: [10]u8 = ".shstrtab\x00".*,
    symtab_name: [8]u8 = ".symtab\x00".*,
    symstrtab_name: [11]u8 = ".symstrtab\x00".*,
};

const File = extern struct {
    header: std.elf.Elf64_Ehdr,
    phdrs: [1]std.elf.Elf64_Phdr,
    shdrs: [5]std.elf.Elf64_Shdr,
};

pub const Writer = struct {
    allocator: std.mem.Allocator,
    symtab: std.ArrayListUnmanaged(std.elf.Elf64_Sym) = .{},
    symstrtab: std.ArrayListUnmanaged(u8) = .{},

    pub fn init(allocator: std.mem.Allocator) !@This() {
        var self: @This() = .{.allocator = allocator};
        try self.symtab.append(self.allocator, std.mem.zeroes(std.elf.Elf64_Sym));
        try self.symstrtab.append(self.allocator, 0);
        return self;
    }

    pub fn addSymbol(self: *@This(), name: []const u8, offset: u64) !void {
        try self.symtab.append(self.allocator, .{
            .st_name = @intCast(u32, self.symstrtab.items.len),
            .st_info = 0x2,
            .st_other = 0,
            .st_shndx = SH_TEXT,
            .st_value = BASE_VADDR + offset,
            .st_size = 0,
        });
        try self.symstrtab.appendSlice(self.allocator, name);
        try self.symstrtab.append(self.allocator, 0);
    }

    fn compareSyms(_: void, lhs: std.elf.Elf64_Sym, rhs: std.elf.Elf64_Sym) bool {
        return lhs.st_value < rhs.st_value;
    }

    pub fn finalize(self: *const @This(), file: *std.fs.File, code: []const u8, entry: u64) !void {
        std.sort.sort(std.elf.Elf64_Sym, self.symtab.items, {}, compareSyms);

        var current_offset: usize = @sizeOf(File);
        var elf: File = .{
            .header = undefined,
            .phdrs = undefined,
            .shdrs = undefined,
        };

        elf.header = .{
            .e_ident = "\x7FELF\x02\x01\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00".*,
            .e_type = .EXEC,
            .e_machine = backends.current_backend.elf_machine,
            .e_version = 1,
            .e_entry = BASE_VADDR + entry,
            .e_phoff = @offsetOf(File, "phdrs"),
            .e_shoff = @offsetOf(File, "shdrs"),
            .e_flags = 0,
            .e_ehsize = @sizeOf(std.elf.Elf64_Ehdr),
            .e_phentsize = @sizeOf(std.elf.Elf64_Phdr),
            .e_phnum = elf.phdrs.len,
            .e_shentsize = @sizeOf(std.elf.Elf64_Shdr),
            .e_shnum = elf.shdrs.len,
            .e_shstrndx = SH_SHSTRTAB,
        };

        const shstrtab: ShStrTab = .{};
        const shstrtab_offset = current_offset;
        current_offset += @sizeOf(ShStrTab);

        const symtab_offset = current_offset;
        const symtab_size = self.symtab.items.len * @sizeOf(std.elf.Elf64_Sym);
        current_offset += symtab_size;

        const symstrtab_offset = current_offset;
        current_offset += self.symstrtab.items.len;

        current_offset += 0xFFF;
        current_offset &= ~@as(usize, 0xFFF);

        const code_offset = current_offset;
        current_offset += code.len;

        elf.phdrs[0] = .{
            .p_type = std.elf.PT_LOAD,
            .p_flags = std.elf.PF_R | std.elf.PF_W | std.elf.PF_X,
            .p_offset = code_offset,
            .p_vaddr = BASE_VADDR,
            .p_paddr = 0x0,
            .p_filesz = code.len,
            .p_memsz = (code.len + 0xFFF) & ~@as(usize, 0xFFF),
            .p_align = 0x1000,
        };

        elf.shdrs[SH_NULL] = std.mem.zeroes(std.elf.Elf64_Shdr);
        elf.shdrs[SH_TEXT] = .{
            .sh_name = @offsetOf(ShStrTab, "text_name"),
            .sh_type = std.elf.SHT_PROGBITS,
            .sh_flags = std.elf.SHF_ALLOC | std.elf.SHF_WRITE | std.elf.SHF_EXECINSTR,
            .sh_addr = BASE_VADDR,
            .sh_offset = code_offset,
            .sh_size = code.len,
            .sh_link = 0,
            .sh_info = 0,
            .sh_addralign = 0x1000,
            .sh_entsize = 0,
        };

        elf.shdrs[SH_SHSTRTAB] = .{
            .sh_name = @offsetOf(ShStrTab, "shstrtab_name"),
            .sh_type = std.elf.SHT_STRTAB,
            .sh_flags = 0,
            .sh_addr = 0,
            .sh_offset = shstrtab_offset,
            .sh_size = @sizeOf(ShStrTab),
            .sh_link = 0,
            .sh_info = 0,
            .sh_addralign = 0,
            .sh_entsize = 0,
        };

        elf.shdrs[SH_SYMTAB] = .{
            .sh_name = @offsetOf(ShStrTab, "symtab_name"),
            .sh_type = std.elf.SHT_SYMTAB,
            .sh_flags = 0,
            .sh_addr = 0,
            .sh_offset = symtab_offset,
            .sh_size = symtab_size,
            .sh_link = SH_SYMSTRTAB,
            .sh_info = @intCast(u32, self.symtab.items.len),
            .sh_addralign = 0,
            .sh_entsize = @sizeOf(std.elf.Elf64_Sym),
        };

        elf.shdrs[SH_SYMSTRTAB] = .{
            .sh_name = @offsetOf(ShStrTab, "symstrtab_name"),
            .sh_type = std.elf.SHT_STRTAB,
            .sh_flags = 0,
            .sh_addr = 0,
            .sh_offset = symstrtab_offset,
            .sh_size = self.symstrtab.items.len,
            .sh_link = 0,
            .sh_info = 0,
            .sh_addralign = 0,
            .sh_entsize = 0,
        };

        try file.pwriteAll(std.mem.asBytes(&elf), 0);
        try file.pwriteAll(std.mem.asBytes(&shstrtab), shstrtab_offset);
        try file.pwriteAll(std.mem.sliceAsBytes(self.symtab.items), symtab_offset);
        try file.pwriteAll(self.symstrtab.items, symstrtab_offset);
        try file.pwriteAll(code, code_offset);
    }
};

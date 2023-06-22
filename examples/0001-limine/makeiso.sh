set -xeo pipefail

THIS_DIR=$(dirname $(realpath $0))

zig build run -- $THIS_DIR/entry.n -o $THIS_DIR/kernel -base 0xffffffff80000000
pushd $THIS_DIR

if [ ! -d limine ]; then
    git clone https://github.com/limine-bootloader/limine.git --branch=v4.x-branch-binary --depth=1
    make -C limine
fi

rm -rf iso_root
mkdir -p iso_root
cp kernel limine.cfg limine/limine.sys limine/limine-cd.bin limine/limine-cd-efi.bin iso_root/
mkdir -p iso_root/EFI/BOOT
cp limine/BOOT*.EFI iso_root/EFI/BOOT/
xorriso -as mkisofs -b limine-cd.bin \
    -no-emul-boot -boot-load-size 4 -boot-info-table \
    --efi-boot limine-cd-efi.bin \
    -efi-boot-part --efi-boot-image --protective-msdos-label \
    iso_root -o kernel.iso
limine/limine-deploy kernel.iso
rm -rf iso_root

popd

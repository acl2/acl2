# Done on osprey (see ../compilation-toolchains.md):
docker run --rm -v "$(pwd)":/src -w /src arm32-musl gcc -marm -O0 -static -o wiki.arm32.elf32 wiki.c

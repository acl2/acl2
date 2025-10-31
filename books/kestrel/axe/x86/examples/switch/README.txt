switch.c is a simple example with a 5-case (including default) switch statement.
switch-complex.c is a more complex example with a 10-case switch statement that modifies a global variable to prevent optimization.

The Clang compiler on macOS generates a jump table for switch.c, which uses
indirect jumps (jmpq *%rax). GCC on Linux only generates a jump table for
switch-complex.c (with -O1 optimization), not for the simpler switch.c.
Jump tables with indirect jumps are currently not supported by the Axe x86
lifter. The lifting code in switch-macho64.lisp is commented out until jump
table support is implemented.

switch.macho64 was produced by:

  gcc -arch x86_64 switch.c -o switch.macho64

with "Apple clang version 16.0.0 (clang-1600.0.26.6)"
(gcc is aliased to clang on macOS)

switch.elf64 was produced on Linux by:

  gcc -o switch.elf64 switch.c

with GCC 15.2.0 (from gcc:latest Docker image) on an ARM Mac.

switch-complex.elf64 was produced on Linux by:

  gcc -O1 -o switch-complex.elf64 switch-complex.c

with GCC 15.2.0 (from gcc:latest Docker image) on an ARM Mac.

----------------
Note #1

Note that switch.elf64 is much larger than switch.macho64.
I asked Claude Opus 4.1 why.  Here is the interesting answer.

  ⏺ Why switch.elf64 is Much Larger Than switch.macho64

    The ELF binary (15KB) is approximately 3.6x larger than the Mach-O binary (4.2KB). Here are the key reasons:

    1. Symbol Tables and Debug Information

    - ELF: Not stripped (contains full symbol table with 816 bytes and string table with 416 bytes)
    - Mach-O: Already stripped (only 3 symbols remain)
    - Stripping the ELF reduces it from 15KB to 14KB (saves ~1KB)

    2. More Sections and Metadata

    - ELF: 27 sections including separate sections for initialization, finalization, GOT, PLT, dynamic linking info, etc.
    - Mach-O: Much simpler structure with just TEXT segment containing code and unwind info

    3. Dynamic Linking Overhead

    - ELF: Contains extensive dynamic linking infrastructure:
      - .dynamic section (400 bytes)
      - .gnu.hash, .dynsym, .dynstr for symbol resolution
      - .got and .got.plt for position-independent code
      - Interpreter path /lib64/ld-linux-x86-64.so.2
    - Mach-O: Minimal - just references libSystem.B.dylib

    4. Initialization/Finalization Code

    - ELF: Has separate .init and .fini sections, plus .init_array and .fini_array
    - Mach-O: No visible initialization code in the binary

    5. Code Size Difference

    - ELF: ~107 instruction lines in disassembly
    - Mach-O: ~50 instruction lines
    - The ELF has over 2x the code, likely due to GCC including more runtime initialization code

    6. Default Compilation Differences

    - GCC on Linux: Includes more runtime support code by default, GNU-specific sections
    - Clang on macOS: More aggressive optimization and dead-code elimination by default

    Summary

    The size difference is primarily due to:
    1. Unstripped symbols in the ELF (1KB)
    2. Dynamic linking infrastructure (2-3KB)
    3. Additional runtime initialization code (2-3KB)
    4. More metadata sections for ELF format (2-3KB)
    5. Less aggressive optimization by default GCC vs Clang

    The core switch statement logic is the same, but the ELF binary includes significantly more infrastructure for Linux's dynamic linking model and runtime environment.

----------------
Note #2

I asked Claude Opus 4.1 if both binaries use a jump table for the switch statement.

The short answer is that the Mach-O binary uses a jump table but the ELF binary uses sequential comparisons.

Claude took the initiative of recompiling the ELF with -O2 optimization and then observed:

  ⏺ Interesting! With -O2 optimization, GCC actually eliminated the switch entirely and replaced it with arithmetic:
    - add $0x1,%edi - adds 1 to the input
    - imul $0x64,%edi,%eax - multiplies by 100 (0x64)
    - This works because the cases return 100, 200, 300, 400 for inputs 0, 1, 2, 3!

(The full output is available from Eric M.)

----------------
Note #3

I then asked Claude Opus 4.1 to get GCC on linux to create a binary with jump tables,
which is where switch-complex.c and switch-complex.elf64 came from.

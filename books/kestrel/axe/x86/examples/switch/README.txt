switch.c is a simple example with a 5-case (including default) switch statement.

The compiler generates a jump table for this switch statement, which uses
indirect jumps (jmpq *%rax). This is currently not supported by the Axe x86
lifter. The lifting code in switch-macho64.lisp is commented out until jump
table support is implemented.

switch.macho64 was produced by:

  gcc -arch x86_64 switch.c -o switch.macho64

with "Apple clang version 16.0.0 (clang-1600.0.26.6)"
(gcc is aliased to clang on macOS)

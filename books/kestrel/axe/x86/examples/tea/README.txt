wiki.c is the code from https://en.wikipedia.org/wiki/Tiny_Encryption_Algorithm
(retrieved May 5, 2017), with a simple testing main() added

tea.macho64 is (essentially) the result of compiling wiki.c on macOS:
gcc -o tea.macho64 wiki.c

tea.elf64 is the result of compiling wiki.c on Linux:
gcc -o tea.elf64 wiki.c

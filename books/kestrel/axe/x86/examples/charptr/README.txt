This directory contains examples for testing the Axe x86 lifter's handling
of char* pointers and string operations.

================================================================================
TEST CASES
================================================================================

simple-byte.c / simple-byte.elf64 / simple-byte-elf64.lisp
----------------------------------
Very simple char* test - a single function that reads one byte
from a pointer without null checks.

Binary was produced on Linux by:
  gcc -O0 -fno-omit-frame-pointer -o simple-byte.elf64 simple-byte.c

Lifting file: simple-byte-elf64.lisp
Status: SUCCESS - get_byte lifts and reads a byte from a pointer


return-literal.c / return-literal.elf64 / return-literal-elf64.lisp
---------------------------------------
Tests functions that return string literal pointers and access string
literals from .rodata section.

Binary was produced on Linux by:
  gcc -O0 -fno-omit-frame-pointer -o return-literal.elf64 return-literal.c

Lifting file: return-literal-elf64.lisp
Status: partial SUCCESS - don't know how to check memory


charptr-locations.c / charptr-locations.elf64 / charptr-locations-elf64.lisp
----------------------------------------------
Comprehensive test file with multiple functions testing char* pointers
from different memory locations:
- String literals (.rodata section)
- Global variables (.data section)
- BSS segment (.bss section)
- Stack-allocated strings
- Heap-allocated strings (malloc)
- Static local variables

Binary was produced on Linux by:
  gcc -o charptr-locations.elf64 charptr-locations.c

Lifting file: charptr-locations-elf64.lisp
Status: Partial success

Available lifting targets include:
- `read_only_byte` - Takes const char* parameter
- `read_write_byte` - Takes non-const char* parameter
- `process_string` - Reads up to 4 bytes and sums them
- `test_literal` - Uses string literal
- `test_global` - Uses global variable
- `test_const_global` - Uses const global variable
- `test_bss` - Uses BSS segment
- `test_stack` - Uses stack-allocated string
- `test_heap` - Uses heap allocation (malloc/free)
- `test_static` - Uses static local variable

Each function presents different lifting challenges and can be used to test
various aspects of the Axe lifter's handling of memory and pointers.


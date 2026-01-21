;  y86-code.lisp                              Warren A. Hunt, Jr.

(in-package "ACL2")

(include-book "y86-asm")
(include-book "y86")
(include-book "y86-mem-init")

; The CS352 class specification for the Y86 processor is written in
; the ACL2 formal logic.  This logic allows the Y86 specification to
; be both precise and executable.  We will use this specification for
; our labs.

; This specification is likely different from other specifications you
; may have encountered.  First, it is written in a Lisp-style
; language.  Second, the specification is complete; that is, for every
; possible configuration of the memory, the registers, and the flags,
; our Y86 specification specifies exactly what the values of the
; memory, registers, and flags, will be after executing one or more
; instructions.

; There are several parts to the Y86 specification.  Before we can
; define the ISA for the Y86, we need to define the state for our
; processor.  We represent the memory as an array (formally, a list)
; of 8-bit bytes, where each there are 2^32 distinct byte addresses.
; Thus, an address is is a natural number between 0 and 4,294,967,295
; ((2^32)-1) inclusive, and the content of every memory location
; is a natural number between 0 and 255 inclusive.

; We sometimes use an address-value pair to represent a memory
; location and it corresponding value, such as:

;   (  ADDRESS  .  CONTENTS  )

; where the 32-bit ADDRESS identifies the 8-bit CONTENTS.  The X86 has
; representation conventions for numbers that are aggreagates of 1, 2,
; and 4 bytes.  So, given a "little-ending" ordering convention, we
; would represent the number 65793 as four bytes, starting located at
; address 12:

;  (( 12 . 1 )
;   ( 13 . 1 )
;   ( 14 . 1 )
;   ( 15 . 0 ))

; With this model, the order of the pairs in a list is irrelevant.
; Thus, the following list is equalivant.

;  (( 14 . 1 )
;   ( 13 . 1 )
;   ( 12 . 1 )
;   ( 15 . 0 ))

; With a model, we need to decide what takes precedence.  If there are
; duplicate keys (addresses), the value associated with the first time
; an address appears is the value in the memory.  So, the memory

;  (( 22 . 3 )
;   ( 23 . 4 )
;   ( 22 . 5 ))

; has a value of 3 in location 22.

; As a part of our Y86 assembler, we have defined functions to read
; and write such a memory representation.  The RO8 function reads one
; byte from a list of address-contents pairs.  We actually write:

;(r08 23
;     '(( 22 . 3 )
;       ( 23 . 4 )
;       ( 22 . 5 )))

; To write a value to this memory, we use the W08 function.  An
; example is:

;(w08 6 25
;     '(( 22 . 3 )
;       ( 23 . 4 )
;       ( 22 . 5 )))

; After using the assembler to create a memory image (a list of
; address-content pairs), we then copy those contents into an
; array-like object that we use to simulate the Y86 memory.

; Some times, it is useful to temporarily assigning values to
; variables; for such, we use the "!" command.

(! var 9)

; and we use the "@" command to read a previously assigned variable.

(@ var)

; Before we simulate a Y86 program, we represent it as assembly code.
; Well formed assembly programs are first checked to see if they are
; syntatically correct; we don't attempt to assemble a syntatically
; incorrect program.

; Thus, the first check we do is to see if the program we want to run
; is well formed.  This is like the first stage of a compiler, which
; checks the syntax of the program.  Below is a program that doesn't
; perform any useful work, but it shows how addresses are associated
; with labels.  Below, we assign our program to the variable CODE, so
; we may refer to it later.

(! code
   '(zero
     (nop)
     (nop)
     (halt)
     three
     (nop)
     (halt)
     (dword 4)
     nine
     (align 16)
     (nop)
     (nop)
     eighteen
     (nop)
     nineteen
     (call 3)
     (call nine)
     (nop)
     thirty
     (halt)))

; We check to see if our program is syntatically well-formed using the
; Y86-CODE function.

(y86-prog (@ code))

; Our assembler requires a symbol table, that associating addresses
; with labels.  Thus, before we can assemble a program, we first much
; construct its symbol table.  Thus, after seeing that our program is
; well-formed, we may generate the symbol table for our program.  For
; our assembler, this is the first pass.

(! symbol-table
   (hons-shrink-alist        ; Function to remove any duplicate entries
    (y86-symbol-table        ; Function to create symbol table
     (@ code)                ; The initial memory image (and program)
     0                       ; The starting memory location for the program
     'symbol-table)          ; The "name" of the symbol table
    'shrunk-symbol-table))   ; The "name" of the "compressed" symbol table

; The symbol table associates labels with a memory address.  We use
; labels as a symbolic representation of some natural number.  It is
; possible, in fact, easy, to redefine labels, to ask the assembler to
; assemble different pieces of code that are destined to occupy the
; same location in memory, etc.  Thus, we only keep the last
; association for every label.  The function HONS-SHRINK-ALIST (used
; just below) removes duplicates and reverses its entries.

(hons-shrink-alist
 (y86-asm                    ; Function to assemble Y86 program
  (@ code)                   ; The initial memory image (and program)
  0                          ; The starting location
  (@ symbol-table)           ; The symbol table -- same starting location
  'program-bytes)            ; The "name" of the assembled program
 'shrunk-program-bytes)      ; The "name" of the "compressed" program


; Now, let's consider a more interesting assembly program; this
; program is designed to sum the numbers from 1 to <n>, where <n> is
; place in %edx.  Below, after setting %eax to 0, we initialize our
; sum program by setting %edx to 9; that is, we expect our program to
; sum the numbers from 1 to 9.

; To the right of the assembler, there is both a summary of what the
; instruction does as well as the byte codes that we expect from our
; assembler.  Once, we run the assembler (below), we can check to see
; if our comment is consistent with the output from the assembler.

(! code
   '(
     sum_loop
     (xorl    %eax %eax)    ; %eax <- 0                   ((0 . 99)
                            ;                              (1 . 0)
     irmovl-9-edx
     (irmovl  9    %edx)    ; %edx <- 9 -- <n>             (2 . 48)
                            ;                              (3 . 242)
                            ;                              (4 . 9)
                            ;                              (5 . 0)
                            ;                              (6 . 0)
                            ;                              (7 . 0)
     xorl-esi-esi
     (xorl    %esi %esi)    ; %esi <- 0                    (8 . 99)
                            ;                              (9 . 102)
     irmovl-1-ecx
     (irmovl  1    %ecx)    ; %ecx <- 1                    (10 . 48)
                            ;                              (11 . 241)
                            ;                              (12 . 1)
                            ;                              (13 . 0)
                            ;                              (14 . 0)
                            ;                              (15 . 0)
     sub-ecx-esi
     (subl    %ecx %esi)    ; %esi <- -1                   (16 . 97)
                            ;                              (17 . 22)
     loop
     addl-edx-eax
     (addl   %edx %eax)     ; Accumulate %edx into %eax    (18 . 96)
                            ;                              (19 . 32)

     addl-esi-edx
     (addl   %esi %edx)     ; Subtract 1 from %edx         (20 . 96)
                            ;                              (21 . 98)
     jg-loop
     (jg loop)              ; Loop if greater than zero    (22 . 118)
                            ;                              (23 . 18)
                            ;                              (24 . 0)
                            ;                              (25 . 0)
                            ;                              (26 . 0)
     halt
     (halt)                 ; Halt                         (27 . 0)
     ))                     ;                              . SUM-1-TO-N)

; Create the symbol table.  In our program (above) we have put a
; label before every instruction.

(y86-prog (@ code))
(! location 0)
(! symbol-table
   (hons-shrink-alist
    (y86-symbol-table (@ code)        ; The sum-1-to-n program
                      (@ location)    ; Beginning program location
                      'symbol-table)  ; Name of this symbol table
    'shrunk-symbol-table))            ; Name of reversed, compressed symbol table

; The function Y86-ASM assembles a program into a memory image.  Note,
; that the assembler requires the SYMBOL-TABLE as an argument.  Our
; Y86-ASM assembler does indeed assemble it program in one pass given
; a symbol table (the first pass).  Thus, our assembler is a two-pass
; assembler.

(! init-mem
   (hons-shrink-alist
    (y86-asm (@ code)          ; The same, sum-1-to-n program
             (@ location)      ; Same beginning program location
             (@ symbol-table)  ; The contents of our symbol table
             'sum-1-to-n)      ; Name of the assembler output
    'shrunk-sum-1-to-n))       ; Name of reversed, compressed assembler output

; Now, what happens if we were to change the initial location from
; what its value was for the first pass?  Interesting problem.  Could
; this be done to relocate a program?  Or, do we just create a mess?

; Up to this point, we have only been concerned with creating an
; appropriate memory image.  But, our Y86 processor has internal
; registers.  We need to initialize the entire Y86 state, or at
; least the part we are going to use.  Since, we want to execute
; our program, we need to initialize the program counter.  In fact,
; we choose to initialize all of the registers.  note we need
; initial values for various registers.

(! init-pc 0)
(! y86-status nil)   ; Initial value for the Y86 status register

(init-y86-state
 (@ y86-status)  ; Y86 status
 (@ init-pc)     ; Initial program counter
 nil             ; Initial registers, if NIL, then registers set to zero
 nil             ; Initial flags, if NIL, then flags set zero
 (@ init-mem)    ; Initialize memory with the assembler output
 x86-32          ; Name for the entire Y86 processor state
 )

; Line that can be typed that executes only one instruction and then
; shows the Y86 machine registers after single step.
; (y86-step x86-32) (m32-get-regs-and-flags x86-32)

; Step ISA 100 steps or to HALT.
(y86 x86-32 100) (m32-get-regs-and-flags x86-32)


; Our next Y86 assembler program is the Fibonacci program.  Our
; implementation is recursive; that is, this assembler program calls
; itself.  How does one create such a program?  Well, an easy way is
; to write an algorithm of interest in, for example, the C-language,
; and then use a compiler to produce a X86 assembly listing.  Then,
; once can just hand-translate the X86 assembly listing into Y86
; assembler.


; Fibonacci

(!! fib-code
    `(fib
      ;; Subroutine setup
      (pushl  %ebp)         ;   0: Save superior frame pointer
      (rrmovl %esp %ebp)    ;   2: Set frame pointer
      (pushl  %ebx)         ;   4: Save callee-save registers on stack
      (pushl  %esi)         ;   6:

      (mrmovl 8(%ebp) %ebx) ;   8: Get <N>

      (xorl   %eax %eax)    ;  14: %eax := 0
      (andl   %ebx %ebx)    ;  16: Set flags
      (jle    fib_leave)    ;  18: Return 0, if <N> <= 0

      (irmovl 1 %eax)       ;  23: %eax := 1
      (rrmovl %ebx %ecx)    ;  29: %ecx := <N>
      (subl   %eax %ecx)    ;  31: %ecx := <N> - 1
      (je     fib_leave)    ;  33: Return 1, if <N> == 0

      (pushl  %ecx)         ;  38: Push (<N> - 1)
      fib-1
      (call   fib)          ;  40: Recursively call fib(<N> - 1)
      (popl   %ecx)         ;  45: Restore stack pointer
      (rrmovl %eax %esi)    ;  47: Save fib(<N> - 1)

      (irmovl 2 %ecx)       ;  49:
      (subl   %ecx %ebx)    ;  55: <N> - 2
      (pushl  %ebx)         ;  57: Push (<N> - 2)
      fib-2
      (call   fib)          ;  59: Recursively call fib(<N> - 2)
      (popl   %ecx)         ;  64: Restore stack pointer

      (addl   %esi %eax)    ;  66: fib(<N> - 2) + fib(<N> - 1)

      ;; Subroutine leave
      fib_leave
      (popl   %esi)         ;  68: Restore callee-save register
      (popl   %ebx)         ;  70: Restore frame pointer
      (rrmovl %ebp %esp)    ;  72: Restore stack pointer
      (popl   %ebp)         ;  74: Restore previous frame pointer
      (ret)                 ;  76: Subroutine return

      ;; Main program
      (align   16)          ;  80: Align to 16-byte address
      main                  ;  80: "main" program
      (irmovl  stack %esp)  ;  80: Initialize stack pointer (%esp)
      (rrmovl  %esp %ebp)   ;  86: Initialize frame pointer (%ebp)
      (irmovl  30 %eax)     ;  88: <N>:  fibonacci( <N> )
      (pushl   %eax)        ;  94: Push argument on stack
      (call    fib)         ;  96: Call Fibonacci subroutine
      (popl    %ebx)        ; 101: Restore local stack position
      (halt)                ; 103: Halt

      ;; Stack
      (pos 8192)            ; 8192: Assemble position
      stack                 ; 8192: Thus, "stack" has value 8192
      ))

; Program OK?

(y86-prog (@ fib-code))

(! location 0)
(! symbol-table
   (hons-shrink-alist
    (y86-symbol-table (@ fib-code) (@ location) 'symbol-table)
    'shrunk-symbol-table))

; The function Y86-ASM assembles a program into a memory image.

(!! init-mem
    (hons-shrink-alist
     (y86-asm (@ fib-code) (@ location) (@ symbol-table) 'sum-1-to-n)
     'shrunk-sum-1-to-n))

; Initialize the Y86 state, note we need initial values for various
; registers.  Here, we clear the registers (not really necessary) and
; the memory

(m86-clear-regs x86-32)       ; Clear registers
(m86-clear-mem  x86-32 8192)  ; Clear memory location 0 to 8192

(! init-pc (cdr (hons-get 'main (@ symbol-table))))
(! y86-status nil)   ; Initial value for the Y86 status register

(init-y86-state
 (@ y86-status)  ; Y86 status
 (@ init-pc)     ; Initial program counter
 nil             ; Initial registers, if NIL, then all zeros
 nil             ; Initial flags, if NIL, then all zeros
 (@ init-mem)    ; Initial memory
 x86-32
 )

; Lines that can be typed that just shows the Y86 machine status and
; some of the memory after single stepping.
; (y86-step x86-32) (m32-get-regs-and-flags x86-32)
; (rmb 4 (rgfi *mr-esp* x86-32) x86-32)

; Step ISA 10,000,000,000 (about 20 minutes) steps or to HALT.
(time$ (y86 x86-32 10000000000)) (m32-get-regs-and-flags x86-32)

;      x  0  1  2  3  4  5  6  7  8  9 10 11  12  13  14  15  16   17   18
;  fib(x) 0  1  1  2  3  5  8 13 21 34 55 89 144 233 377 610 987 1597 2584

; Model 0.0 ;; (Modified by Shilpi)
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.07  0.70     7.66    83.46     938.59

; Model 0.1
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.00  2.84   31.56

; Model 0.2
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.12  1.13   12.50   138.87    1528.94

; Model 0.3 -- Y86 with 32-bit memory model
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.11  1.23   13.71   151.83

; Model 0.4 -- Y86 with DECLARE forms in rm08 rm32 wm08 wm32
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.08  0.91   10.10   111.88

; Model 0.5 -- Removed MEMOIZE-FLUSH (by setting it to NIL).
;       x      20     25      30       35         40
;   fib(x)   6765  75025  832040  9227465  102334155
;   C-time   0.00  0.002   0.020    0.218      2.413
; Y86-time   0.07  0.81    9.02    99.91    1108.31



; Below is a test program for measuing instruction dispatch
; performance.

; NOP verses NOOP

(!!
 nop-test-code
 `(nop-100
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop) (nop)
   (subl :ecx :eax)
   (jg nop-100)
   (ret)
   nop-100-end

   (align 32)

   noop-100
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop) (noop)
   (subl :ecx :eax)
   (jg noop-100)
   (ret)
   noop-100-end

   (align   32) ;      Align to 16-byte address
   ;; Main program
   main
   (irmovl  stack :esp)   ; Initialize stack pointer (%esp)
   (rrmovl  :esp  :ebp)   ; Initialize frame pointer (%ebp)

   (irmovl  1     :ecx)
   (irmovl  1000000 :eax) ; Initialize count

   loop
   ;; (call    nop-100)         ; Call NOP subroutine
   (call    noop-100) ; Call NOOP subroutine
   halt
   (halt) ; Halt

   ;; Stack
   (pos 8192)
   stack
   ))

(y86-prog (@ nop-test-code))  ; Check syntax

(! location 0)
(! symbol-table
   (hons-shrink-alist
    (y86-symbol-table (@ nop-test-code) (@ location) 'symbol-table)
    'shrunk-symbol-table))

; The function Y86-ASM assembles a program into a memory image.

(!! init-mem
    (hons-shrink-alist
     (y86-asm (@ nop-test-code) (@ location) (@ symbol-table) 'sum-1-to-n)
     'shrunk-sum-1-to-n))

; Initialize the Y86 state, note we need initial values for various
; registers.

(m86-clear-regs x86-32)       ; Clear registers
(m86-clear-mem  x86-32 8192)  ; Clear memory

(! init-pc (cdr (hons-get 'main (@ symbol-table))))
(! y86-status nil)   ; Initial value for the Y86 status register

(init-y86-state
 (@ y86-status)  ; Y86 status
 (@ init-pc)     ; Initial program counter
 nil             ; Initial registers, if NIL, then all zeros
 nil             ; Initial flags, if NIL, then all zeros
 (@ init-mem)    ; Initial memory
 x86-32
 )

; Single step
(y86-step x86-32) (m32-get-regs-and-flags x86-32)
; Step ISA 100 steps or to HALT.
(time$ (y86 x86-32 1000000000))



; With full byte decoding:
; With NOP,  100,000,000 operations in  5.09 seconds
; With NOOP, 100,000,000 operations in 24.64 seconds

; With full byte decoding without non-existent cases:
; With NOP,  100,000,000 operations in  3.94 seconds
; With NOOP, 100,000,000 operations in  7.93 seconds

; With nibble-by-nibble decoding:
; With NOP,  100,000,000 operations in  7.59 seconds
; With NOOP, 100,000,000 operations in  8.20 seconds


; Why slower than above?  We are Using, we thought, a more efficient
; memory model.  Is it the case that the measurements above made with
; an 8-bit memory model instead of the 32-bit one used below?  I can't
; remember.  Or, is it the case the DECLAREd code is bigger than the
; L1 cache?

; But, for the fibonacci code, the DECLAREd model takes about 75% of
; the time, so one might say that it is 1/3 faster.

; With full byte decoding without non-existent cases, and
; With Y86 with DECLARE forms in rm08 rm32 wm08 wm32:
; With NOP,  100,000,000 operations in  5.10 seconds
; With NOOP, 100,000,000 operations in  8.79 seconds

; With nibble-by-nibble decoding, and
; With Y86 with DECLARE forms in rm08 rm32 wm08 wm32:
; With NOP,  100,000,000 operations in  6.44 seconds
; With NOOP, 100,000,000 operations in  7.24 seconds
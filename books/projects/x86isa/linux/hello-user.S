; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail

; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Yahya Sohail        <ysohail@cs.utexas.edu>

; This Linux program simply prints a little message and then starts /bin/sh.
; It has no dependencies.
; Build with nasm -f elf64 hello-user.S && ld hello-user.o -o hello-user

  ; Begin the data section
  section .data
  ; This is the string that will be printed out when this program starts
str:
  ; 0x0a is an LF (in C: '\n') and 0 is for null termination
  db 'hello from userspace', 0x0a, 0
  ; Stores the length of the string (current address, $, minus address of str)
  ;in str_len
  str_len equ $-str

  ; String holding the path of the program to start
prog:
  db '/bin/sh', 0

  ; String holding the value we will pass as argv[0] to the program we start
argv0:
  db 'sh', 0

  ; argv and envp as passed to Linux programs are null terminated arrays of
  ; null terminated C strings. Here, we set argv = {argv0, NULL} We don't want
  ; to pass any environment variables, so we set envp = {NULL}, but instead of
  ; constructing a separate array for this values we use argv + 1
argv:
  dq argv0
envp:
  dq 0

section .text
global _start
_start:
  ; Linux's 64-bit x86 syscall ABI requires the syscall number to be in rax,
  ; and the first three arguments to be in RDI, RSI, and RDX in that order. The
  ; syscall is then triggered using the syscall instruction (unlike, say,
  ; 32-bit mode where we use int 0x80).

  mov rax, 1 ; write
  mov rdi, 1 ; stdout
  mov rsi, str
  mov rdx, str_len
  ;; write(stdout, str, str_len)
  syscall

  mov rax, 59 ; execve
  mov rdi, prog
  mov rsi, argv
  mov rdx, envp
  ;; execve(prog, argv, envp)
  syscall

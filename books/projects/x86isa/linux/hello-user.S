;; Build with nasm -f elf64 hello-user.S && ld hello-user.o -o hello-user

section .data
str:
  db 'hello from userspace', 0x0a, 0
  str_len equ $-str

prog:
  db '/bin/sh', 0

argv0:
  db 'sh', 0

argv:
  dq argv0
envp:
  dq 0

section .text
global _start
_start:
  mov rax, 1
  mov rdi, 1
  mov rsi, str
  mov rdx, str_len
  syscall
  mov rax, 59
  mov rdi, prog
  mov rsi, argv
  mov rdx, envp
  syscall

; x86isa assembly snippet testing framework
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

%include "utils.mac"

SECTION .text
global cmpxchg8b
cmpxchg8b:
	; input and output both are laid out as eax, edx, ebx, ecx, memory operand, flags
	mov r8d, DWORD[rdi]       ; this will become eax but for now we need ax for flags
	mov edx, DWORD[rdi+4]	  ;
	push rbx		  ; ebx needs to be backed up & restored I think
	mov ebx, DWORD[rdi+8]	  ;
	mov ecx, DWORD[rdi+12]	  ;
	; QWORD[rdi+16] gives the initial state of the memory operand -- move it to RSI via temp r10
	mov r10, QWORD[rdi+16]	  ;
	mov QWORD[rsi+16], r10	;
	mov ax, WORD[rdi+24]	; put flags in ax
	backup_and_set_eflags	; gets flags from ax, stores previous flags in r11w, uses r12 as scratch

	mov eax, r8d		; put the input operand in eax since we're done setting up the flags now
	
	cmpxchg8b [rsi+16]	;

	; save some outputs
	mov DWORD[rsi], eax	;
	mov DWORD[rsi+4], edx	;
	mov DWORD[rsi+8], ebx	;
	mov DWORD[rsi+12], ecx	;
	; the memory operand is all set already at rsi+16
	get_and_restore_eflags	; this leaves the resulting flags in ax and restores the previous ones from r11w
	and ax, ~0xB02		; mask out non-status flag bits
	mov WORD[rsi+24], ax
	pop rbx			;restore ebx
	ret
	
global cmpxchg16b
cmpxchg16b:
	; input and output both are laid out as rax, rdx, rbx, rcx, memory operand, flags
	mov r8, QWORD[rdi]       ; this will become eax but for now we need ax for flags
	mov rdx, QWORD[rdi+8]	  ;
	push rbx		  ; rbx needs to be backed up & restored I think
	mov rbx, QWORD[rdi+16]	  ;
	mov rcx, QWORD[rdi+24]	  ;
	; DQWORD[rdi+32] gives the initial state of the memory operand -- move it to RSI via temp r10
	mov r10, QWORD[rdi+32]	  ;
	mov QWORD[rsi+32], r10	  ;
	mov r10, QWORD[rdi+40]	  ;
	mov QWORD[rsi+40], r10	  ;
	mov ax, WORD[rdi+48]	; put flags in ax
	backup_and_set_eflags	; gets flags from ax, stores previous flags in r11w, uses r12 as scratch

	mov rax, r8		; put the input operand in eax since we're done setting up the flags now
	
	cmpxchg16b [rsi+32]	;

	; save some outputs
	mov QWORD[rsi], rax	;
	mov QWORD[rsi+8], rdx	;
	mov QWORD[rsi+16], rbx	;
	mov QWORD[rsi+24], rcx	;
	; the memory operand is all set already at rsi+32
	get_and_restore_eflags	; this leaves the resulting flags in ax and restores the previous ones from r11w
	and ax, ~0xB02		; mask out non-status flag bits
	mov WORD[rsi+48], ax
	pop rbx			;restore rbx
	ret
	
	
	

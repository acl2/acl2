# From: 
# http://software.intel.com/en-us/articles/intel-digital-random-number-generator-drng-software-implementation-guide/

.intel_syntax noprefix
	   .text
	   .global     get_cpuid_info_v1
get_cpuid_info_v1:
	   mov r8, rdi   #  array addr
	   mov r9, rsi   #  leaf
	   mov r10, rdx  #  subleaf
	   push        rax
	   push        rbx
	   push        rcx
	   push        rdx
	   mov         eax, r9d
	   mov         ecx, r10d
	   cpuid
	   mov         DWORD PTR [r8], eax
	   mov         DWORD PTR [r8+4], ebx
	   mov         DWORD PTR [r8+8], ecx
	   mov         DWORD PTR [r8+12], edx
	   pop         rdx
	   pop         rcx
	   pop         rbx
	   pop         rax
	   ret         0
#get_cpuid_info_v1 ENDP
#_TEXT     ENDS

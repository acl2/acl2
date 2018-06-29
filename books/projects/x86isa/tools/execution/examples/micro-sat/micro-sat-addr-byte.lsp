; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
; Shilpi Goel         <shigoel@cs.utexas.edu>


;; GCC Optimization level: -default-opt

(in-package "X86ISA")

(defconst *micro-sat*
  (list 
   
;; Section: <.interp>:


   (cons #x400238 #x2f) ;; (bad) 
   (cons #x400239 #x6c) ;; insb (%dx),%es:(%rdi) 
   (cons #x40023a #x69) ;; imul $0x646c2f34,0x36(%rdx),%esp 
   (cons #x40023b #x62) ;;  
   (cons #x40023c #x36) ;;  
   (cons #x40023d #x34) ;;  
   (cons #x40023e #x2f) ;;  
   (cons #x40023f #x6c) ;;  
   (cons #x400240 #x64) ;;  
   (cons #x400241 #x2d) ;; sub $0x756e696c,%eax 
   (cons #x400242 #x6c) ;;  
   (cons #x400243 #x69) ;;  
   (cons #x400244 #x6e) ;;  
   (cons #x400245 #x75) ;;  
   (cons #x400246 #x78) ;; js 400275 <_init-0x11b> 
   (cons #x400247 #x2d) ;;  
   (cons #x400248 #x78) ;; js 400282 <_init-0x10e> 
   (cons #x400249 #x38) ;;  
   (cons #x40024a #x36) ;; ss 
   (cons #x40024b #x2d) ;; sub $0x732e3436,%eax 
   (cons #x40024c #x36) ;;  
   (cons #x40024d #x34) ;;  
   (cons #x40024e #x2e) ;;  
   (cons #x40024f #x73) ;;  
   (cons #x400250 #x6f) ;; outsl %ds:(%rsi),(%dx) 
   (cons #x400251 #x2e) ;; xor %cs:(%rax),%al 
   (cons #x400252 #x32) ;;  
   (cons #x400253 #x00) ;;  
   
;; Section: <.note.ABI-tag>:


   (cons #x400254 #x04) ;; add $0x0,%al 
   (cons #x400255 #x00) ;;  
   (cons #x400256 #x00) ;; add %al,(%rax) 
   (cons #x400257 #x00) ;;  
   (cons #x400258 #x10) ;; adc %al,(%rax) 
   (cons #x400259 #x00) ;;  
   (cons #x40025a #x00) ;; add %al,(%rax) 
   (cons #x40025b #x00) ;;  
   (cons #x40025c #x01) ;; add %eax,(%rax) 
   (cons #x40025d #x00) ;;  
   (cons #x40025e #x00) ;; add %al,(%rax) 
   (cons #x40025f #x00) ;;  
   (cons #x400260 #x47) ;; rex.RXB 
   (cons #x400261 #x4e) ;; rex.WRX push %rbp 
   (cons #x400262 #x55) ;;  
   (cons #x400263 #x00) ;; add %al,(%rax) 
   (cons #x400264 #x00) ;;  
   (cons #x400265 #x00) ;; add %al,(%rax) 
   (cons #x400266 #x00) ;;  
   (cons #x400267 #x00) ;; add %al,(%rdx) 
   (cons #x400268 #x02) ;;  
   (cons #x400269 #x00) ;; add %al,(%rax) 
   (cons #x40026a #x00) ;;  
   (cons #x40026b #x00) ;; add %al,(%rsi) 
   (cons #x40026c #x06) ;;  
   (cons #x40026d #x00) ;; add %al,(%rax) 
   (cons #x40026e #x00) ;;  
   (cons #x40026f #x00) ;; add %bl,(%rax) 
   (cons #x400270 #x18) ;;  
   (cons #x400271 #x00) ;; add %al,(%rax) 
   (cons #x400272 #x00) ;;  
   
;; Section: <.note.gnu.build-id>:


   (cons #x400274 #x04) ;; add $0x0,%al 
   (cons #x400275 #x00) ;;  
   (cons #x400276 #x00) ;; add %al,(%rax) 
   (cons #x400277 #x00) ;;  
   (cons #x400278 #x14) ;; adc $0x0,%al 
   (cons #x400279 #x00) ;;  
   (cons #x40027a #x00) ;; add %al,(%rax) 
   (cons #x40027b #x00) ;;  
   (cons #x40027c #x03) ;; add (%rax),%eax 
   (cons #x40027d #x00) ;;  
   (cons #x40027e #x00) ;; add %al,(%rax) 
   (cons #x40027f #x00) ;;  
   (cons #x400280 #x47) ;; rex.RXB 
   (cons #x400281 #x4e) ;; rex.WRX push %rbp 
   (cons #x400282 #x55) ;;  
   (cons #x400283 #x00) ;; add %ch,%bl 
   (cons #x400284 #xeb) ;;  
   (cons #x400285 #x0b) ;; or 0x676763d0(%rcx),%ebp 
   (cons #x400286 #xa9) ;;  
   (cons #x400287 #xd0) ;;  
   (cons #x400288 #x63) ;;  
   (cons #x400289 #x67) ;;  
   (cons #x40028a #x67) ;;  
   (cons #x40028b #xae) ;; scas %es:(%rdi),%al 
   (cons #x40028c #xf1) ;; icebp 
   (cons #x40028d #xa6) ;; cmpsb %es:(%rdi),%ds:(%rsi) 
   (cons #x40028e #xe1) ;; loope 4002c2 <_init-0xce> 
   (cons #x40028f #x32) ;;  
   (cons #x400290 #xfa) ;; cli 
   (cons #x400291 #x87) ;; xchg %esi,-0x7b(%rdx) 
   (cons #x400292 #x72) ;;  
   (cons #x400293 #x85) ;;  
   (cons #x400294 #x87) ;; xchg %esp,%edi 
   (cons #x400295 #xe7) ;;  
   (cons #x400296 #x13) ;; .byte 0x13 
   (cons #x400297 #x48) ;; rex.W 
   
;; Section: <.gnu.hash>:


   (cons #x400298 #x01) ;; add %eax,(%rax) 
   (cons #x400299 #x00) ;;  
   (cons #x40029a #x00) ;; add %al,(%rax) 
   (cons #x40029b #x00) ;;  
   (cons #x40029c #x01) ;; add %eax,(%rax) 
   (cons #x40029d #x00) ;;  
   (cons #x40029e #x00) ;; add %al,(%rax) 
   (cons #x40029f #x00) ;;  
   (cons #x4002a0 #x01) ;; add %eax,(%rax) 
   (cons #x4002a1 #x00) ;;  
   
;; Section: <.dynsym>:


   
;; Section: <.dynstr>:


   (cons #x400300 #x00) ;; add %bl,0x5f(%rdi) 
   (cons #x400301 #x5f) ;;  
   (cons #x400302 #x5f) ;;  
   (cons #x400303 #x67) ;; insl (%dx),%es:(%edi) 
   (cons #x400304 #x6d) ;;  
   (cons #x400305 #x6f) ;; outsl %ds:(%rsi),(%dx) 
   (cons #x400306 #x6e) ;; outsb %ds:(%rsi),(%dx) 
   (cons #x400307 #x5f) ;; pop %rdi 
   (cons #x400308 #x73) ;; jae 40037e <_init-0x12> 
   (cons #x400309 #x74) ;;  
   (cons #x40030a #x61) ;; (bad) 
   (cons #x40030b #x72) ;; jb 400381 <_init-0xf> 
   (cons #x40030c #x74) ;;  
   (cons #x40030d #x5f) ;; pop %rdi 
   (cons #x40030e #x5f) ;; pop %rdi 
   (cons #x40030f #x00) ;; add %ch,0x62(%rcx,%rbp,2) 
   (cons #x400310 #x6c) ;;  
   (cons #x400311 #x69) ;;  
   (cons #x400312 #x62) ;;  
   (cons #x400313 #x63) ;; movslq (%rsi),%ebp 
   (cons #x400314 #x2e) ;;  
   (cons #x400315 #x73) ;; jae 400386 <_init-0xa> 
   (cons #x400316 #x6f) ;;  
   (cons #x400317 #x2e) ;; cs add %bl,%cs:%ss:0x5f(%rdi) 
   (cons #x400318 #x36) ;;  
   (cons #x400319 #x00) ;;  
   (cons #x40031a #x5f) ;;  
   (cons #x40031b #x5f) ;;  
   (cons #x40031c #x6c) ;; insb (%dx),%es:(%rdi) 
   (cons #x40031d #x69) ;; imul $0x6174735f,0x63(%rdx),%esp 
   (cons #x40031e #x62) ;;  
   (cons #x40031f #x63) ;;  
   (cons #x400320 #x5f) ;;  
   (cons #x400321 #x73) ;;  
   (cons #x400322 #x74) ;;  
   (cons #x400323 #x61) ;;  
   (cons #x400324 #x72) ;; jb 40039a <_init+0xa> 
   (cons #x400325 #x74) ;;  
   (cons #x400326 #x5f) ;; pop %rdi 
   (cons #x400327 #x6d) ;; insl (%dx),%es:(%rdi) 
   (cons #x400328 #x61) ;; (bad) 
   (cons #x400329 #x69) ;; imul $0x42494c47,0x0(%rsi),%ebp 
   (cons #x40032a #x6e) ;;  
   (cons #x40032b #x00) ;;  
   (cons #x40032c #x47) ;;  
   (cons #x40032d #x4c) ;;  
   (cons #x40032e #x49) ;;  
   (cons #x40032f #x42) ;;  
   (cons #x400330 #x43) ;; rex.XB pop %r15 
   (cons #x400331 #x5f) ;;  
   (cons #x400332 #x32) ;; xor (%rsi),%ch 
   (cons #x400333 #x2e) ;;  
   (cons #x400334 #x32) ;; xor (%rsi),%ch 
   (cons #x400335 #x2e) ;;  
   (cons #x400336 #x35) ;; .byte 0x35 
   
;; Section: <.gnu.version>:


   (cons #x400338 #x00) ;; add %al,(%rax) 
   (cons #x400339 #x00) ;;  
   (cons #x40033a #x02) ;; add (%rax),%al 
   (cons #x40033b #x00) ;;  
   
;; Section: <.gnu.version_r>:


   (cons #x400340 #x01) ;; add %eax,(%rax) 
   (cons #x400341 #x00) ;;  
   (cons #x400342 #x01) ;; add %eax,(%rax) 
   (cons #x400343 #x00) ;;  
   (cons #x400344 #x10) ;; adc %al,(%rax) 
   (cons #x400345 #x00) ;;  
   (cons #x400346 #x00) ;; add %al,(%rax) 
   (cons #x400347 #x00) ;;  
   (cons #x400348 #x10) ;; adc %al,(%rax) 
   (cons #x400349 #x00) ;;  
   (cons #x40034a #x00) ;; add %al,(%rax) 
   (cons #x40034b #x00) ;;  
   (cons #x40034c #x00) ;; add %al,(%rax) 
   (cons #x40034d #x00) ;;  
   (cons #x40034e #x00) ;; add %al,(%rax) 
   (cons #x40034f #x00) ;;  
   (cons #x400350 #x75) ;; jne 40036c <_init-0x24> 
   (cons #x400351 #x1a) ;;  
   (cons #x400352 #x69) ;; imul $0x20000,(%rcx),%ecx 
   (cons #x400353 #x09) ;;  
   (cons #x400354 #x00) ;;  
   (cons #x400355 #x00) ;;  
   (cons #x400356 #x02) ;;  
   (cons #x400357 #x00) ;;  
   (cons #x400358 #x2c) ;; sub $0x0,%al 
   (cons #x400359 #x00) ;;  
   (cons #x40035a #x00) ;; add %al,(%rax) 
   (cons #x40035b #x00) ;;  
   (cons #x40035c #x00) ;; add %al,(%rax) 
   (cons #x40035d #x00) ;;  
   
;; Section: <.rela.dyn>:


   (cons #x400360 #xe0) ;; loopne 400391 <_init+0x1> 
   (cons #x400361 #x2f) ;;  
   (cons #x400362 #x60) ;; (bad) 
   (cons #x400363 #x00) ;; add %al,(%rax) 
   (cons #x400364 #x00) ;;  
   (cons #x400365 #x00) ;; add %al,(%rax) 
   (cons #x400366 #x00) ;;  
   (cons #x400367 #x00) ;; add %al,(%rsi) 
   (cons #x400368 #x06) ;;  
   (cons #x400369 #x00) ;; add %al,(%rax) 
   (cons #x40036a #x00) ;;  
   (cons #x40036b #x00) ;; add %al,(%rdx) 
   (cons #x40036c #x02) ;;  
   
;; Section: <.rela.plt>:


   (cons #x400378 #x00) ;; add %dh,(%rax) 
   (cons #x400379 #x30) ;;  
   (cons #x40037a #x60) ;; (bad) 
   (cons #x40037b #x00) ;; add %al,(%rax) 
   (cons #x40037c #x00) ;;  
   (cons #x40037d #x00) ;; add %al,(%rax) 
   (cons #x40037e #x00) ;;  
   (cons #x40037f #x00) ;; add %al,(%rdi) 
   (cons #x400380 #x07) ;;  
   (cons #x400381 #x00) ;; add %al,(%rax) 
   (cons #x400382 #x00) ;;  
   (cons #x400383 #x00) ;; add %al,(%rcx) 
   (cons #x400384 #x01) ;;  
   
;; Section: <_init>:


   (cons #x400390 #x48) ;; sub $0x8,%rsp 
   (cons #x400391 #x83) ;;  
   (cons #x400392 #xec) ;;  
   (cons #x400393 #x08) ;;  
   (cons #x400394 #xe8) ;; callq 4003fc <call_gmon_start> 
   (cons #x400395 #x63) ;;  
   (cons #x400396 #x00) ;;  
   (cons #x400397 #x00) ;;  
   (cons #x400398 #x00) ;;  
   (cons #x400399 #xe8) ;; callq 400490 <frame_dummy> 
   (cons #x40039a #xf2) ;;  
   (cons #x40039b #x00) ;;  
   (cons #x40039c #x00) ;;  
   (cons #x40039d #x00) ;;  
   (cons #x40039e #xe8) ;; callq 402990 <__do_global_ctors_aux> 
   (cons #x40039f #xed) ;;  
   (cons #x4003a0 #x25) ;;  
   (cons #x4003a1 #x00) ;;  
   (cons #x4003a2 #x00) ;;  
   (cons #x4003a3 #x48) ;; add $0x8,%rsp 
   (cons #x4003a4 #x83) ;;  
   (cons #x4003a5 #xc4) ;;  
   (cons #x4003a6 #x08) ;;  
   (cons #x4003a7 #xc3) ;; retq 
   
;; Section: <__libc_start_main@plt-0x10>:


   (cons #x4003b0 #xff) ;; pushq 0x202c3a(%rip) # 602ff0 <_GLOBAL_OFFSET_TABLE_+0x8> 
   (cons #x4003b1 #x35) ;;  
   (cons #x4003b2 #x3a) ;;  
   (cons #x4003b3 #x2c) ;;  
   (cons #x4003b4 #x20) ;;  
   (cons #x4003b5 #x00) ;;  
   (cons #x4003b6 #xff) ;; jmpq *0x202c3c(%rip) # 602ff8 <_GLOBAL_OFFSET_TABLE_+0x10> 
   (cons #x4003b7 #x25) ;;  
   (cons #x4003b8 #x3c) ;;  
   (cons #x4003b9 #x2c) ;;  
   (cons #x4003ba #x20) ;;  
   (cons #x4003bb #x00) ;;  
   (cons #x4003bc #x0f) ;; nopl 0x0(%rax) 
   (cons #x4003bd #x1f) ;;  
   (cons #x4003be #x40) ;;  
   (cons #x4003bf #x00) ;;  
   
;; Section: <_start>:


   (cons #x4003d0 #x31) ;; xor %ebp,%ebp 
   (cons #x4003d1 #xed) ;;  
   (cons #x4003d2 #x49) ;; mov %rdx,%r9 
   (cons #x4003d3 #x89) ;;  
   (cons #x4003d4 #xd1) ;;  
   (cons #x4003d5 #x5e) ;; pop %rsi 
   (cons #x4003d6 #x48) ;; mov %rsp,%rdx 
   (cons #x4003d7 #x89) ;;  
   (cons #x4003d8 #xe2) ;;  
   (cons #x4003d9 #x48) ;; and $0xfffffffffffffff0,%rsp 
   (cons #x4003da #x83) ;;  
   (cons #x4003db #xe4) ;;  
   (cons #x4003dc #xf0) ;;  
   (cons #x4003dd #x50) ;; push %rax 
   (cons #x4003de #x54) ;; push %rsp 
   (cons #x4003df #x49) ;; mov $0x402980,%r8 
   (cons #x4003e0 #xc7) ;;  
   (cons #x4003e1 #xc0) ;;  
   (cons #x4003e2 #x80) ;;  
   (cons #x4003e3 #x29) ;;  
   (cons #x4003e4 #x40) ;;  
   (cons #x4003e5 #x00) ;;  
   (cons #x4003e6 #x48) ;; mov $0x4028f0,%rcx 
   (cons #x4003e7 #xc7) ;;  
   (cons #x4003e8 #xc1) ;;  
   (cons #x4003e9 #xf0) ;;  
   (cons #x4003ea #x28) ;;  
   (cons #x4003eb #x40) ;;  
   (cons #x4003ec #x00) ;;  
   (cons #x4003ed #x48) ;; mov $0x402874,%rdi 
   (cons #x4003ee #xc7) ;;  
   (cons #x4003ef #xc7) ;;  
   (cons #x4003f0 #x74) ;;  
   (cons #x4003f1 #x28) ;;  
   (cons #x4003f2 #x40) ;;  
   (cons #x4003f3 #x00) ;;  
   (cons #x4003f4 #xe8) ;; callq 4003c0 <__libc_start_main@plt> 
   (cons #x4003f5 #xc7) ;;  
   (cons #x4003f6 #xff) ;;  
   (cons #x4003f7 #xff) ;;  
   (cons #x4003f8 #xff) ;;  
   (cons #x4003f9 #xf4) ;; hlt 
   (cons #x4003fa #x90) ;; nop 
   (cons #x4003fb #x90) ;; nop 
   
;; Section: <call_gmon_start>:


   (cons #x4003fc #x48) ;; sub $0x8,%rsp 
   (cons #x4003fd #x83) ;;  
   (cons #x4003fe #xec) ;;  
   (cons #x4003ff #x08) ;;  
   (cons #x400400 #x48) ;; mov 0x202bd9(%rip),%rax # 602fe0 <_DYNAMIC+0x190> 
   (cons #x400401 #x8b) ;;  
   (cons #x400402 #x05) ;;  
   (cons #x400403 #xd9) ;;  
   (cons #x400404 #x2b) ;;  
   (cons #x400405 #x20) ;;  
   (cons #x400406 #x00) ;;  
   (cons #x400407 #x48) ;; test %rax,%rax 
   (cons #x400408 #x85) ;;  
   (cons #x400409 #xc0) ;;  
   (cons #x40040a #x74) ;; je 40040e <call_gmon_start+0x12> 
   (cons #x40040b #x02) ;;  
   (cons #x40040c #xff) ;; callq *%rax 
   (cons #x40040d #xd0) ;;  
   (cons #x40040e #x48) ;; add $0x8,%rsp 
   (cons #x40040f #x83) ;;  
   (cons #x400410 #xc4) ;;  
   (cons #x400411 #x08) ;;  
   (cons #x400412 #xc3) ;; retq 
   (cons #x400413 #x90) ;; nop 
   (cons #x400414 #x90) ;; nop 
   (cons #x400415 #x90) ;; nop 
   (cons #x400416 #x90) ;; nop 
   (cons #x400417 #x90) ;; nop 
   (cons #x400418 #x90) ;; nop 
   (cons #x400419 #x90) ;; nop 
   (cons #x40041a #x90) ;; nop 
   (cons #x40041b #x90) ;; nop 
   (cons #x40041c #x90) ;; nop 
   (cons #x40041d #x90) ;; nop 
   (cons #x40041e #x90) ;; nop 
   (cons #x40041f #x90) ;; nop 
   
;; Section: <__do_global_dtors_aux>:


   (cons #x400420 #x55) ;; push %rbp 
   (cons #x400421 #x48) ;; mov %rsp,%rbp 
   (cons #x400422 #x89) ;;  
   (cons #x400423 #xe5) ;;  
   (cons #x400424 #x53) ;; push %rbx 
   (cons #x400425 #x48) ;; sub $0x8,%rsp 
   (cons #x400426 #x83) ;;  
   (cons #x400427 #xec) ;;  
   (cons #x400428 #x08) ;;  
   (cons #x400429 #x80) ;; cmpb $0x0,0x202bf0(%rip) # 603020 <completed.6531> 
   (cons #x40042a #x3d) ;;  
   (cons #x40042b #xf0) ;;  
   (cons #x40042c #x2b) ;;  
   (cons #x40042d #x20) ;;  
   (cons #x40042e #x00) ;;  
   (cons #x40042f #x00) ;;  
   (cons #x400430 #x75) ;; jne 40047d <__do_global_dtors_aux+0x5d> 
   (cons #x400431 #x4b) ;;  
   (cons #x400432 #xbb) ;; mov $0x602e40,%ebx 
   (cons #x400433 #x40) ;;  
   (cons #x400434 #x2e) ;;  
   (cons #x400435 #x60) ;;  
   (cons #x400436 #x00) ;;  
   (cons #x400437 #x48) ;; mov 0x202bea(%rip),%rax # 603028 <dtor_idx.6533> 
   (cons #x400438 #x8b) ;;  
   (cons #x400439 #x05) ;;  
   (cons #x40043a #xea) ;;  
   (cons #x40043b #x2b) ;;  
   (cons #x40043c #x20) ;;  
   (cons #x40043d #x00) ;;  
   (cons #x40043e #x48) ;; sub $0x602e38,%rbx 
   (cons #x40043f #x81) ;;  
   (cons #x400440 #xeb) ;;  
   (cons #x400441 #x38) ;;  
   (cons #x400442 #x2e) ;;  
   (cons #x400443 #x60) ;;  
   (cons #x400444 #x00) ;;  
   (cons #x400445 #x48) ;; sar $0x3,%rbx 
   (cons #x400446 #xc1) ;;  
   (cons #x400447 #xfb) ;;  
   (cons #x400448 #x03) ;;  
   (cons #x400449 #x48) ;; sub $0x1,%rbx 
   (cons #x40044a #x83) ;;  
   (cons #x40044b #xeb) ;;  
   (cons #x40044c #x01) ;;  
   (cons #x40044d #x48) ;; cmp %rbx,%rax 
   (cons #x40044e #x39) ;;  
   (cons #x40044f #xd8) ;;  
   (cons #x400450 #x73) ;; jae 400476 <__do_global_dtors_aux+0x56> 
   (cons #x400451 #x24) ;;  
   (cons #x400452 #x66) ;; nopw 0x0(%rax,%rax,1) 
   (cons #x400453 #x0f) ;;  
   (cons #x400454 #x1f) ;;  
   (cons #x400455 #x44) ;;  
   (cons #x400456 #x00) ;;  
   (cons #x400457 #x00) ;;  
   (cons #x400458 #x48) ;; add $0x1,%rax 
   (cons #x400459 #x83) ;;  
   (cons #x40045a #xc0) ;;  
   (cons #x40045b #x01) ;;  
   (cons #x40045c #x48) ;; mov %rax,0x202bc5(%rip) # 603028 <dtor_idx.6533> 
   (cons #x40045d #x89) ;;  
   (cons #x40045e #x05) ;;  
   (cons #x40045f #xc5) ;;  
   (cons #x400460 #x2b) ;;  
   (cons #x400461 #x20) ;;  
   (cons #x400462 #x00) ;;  
   (cons #x400463 #xff) ;; callq *0x602e38(,%rax,8) 
   (cons #x400464 #x14) ;;  
   (cons #x400465 #xc5) ;;  
   (cons #x400466 #x38) ;;  
   (cons #x400467 #x2e) ;;  
   (cons #x400468 #x60) ;;  
   (cons #x400469 #x00) ;;  
   (cons #x40046a #x48) ;; mov 0x202bb7(%rip),%rax # 603028 <dtor_idx.6533> 
   (cons #x40046b #x8b) ;;  
   (cons #x40046c #x05) ;;  
   (cons #x40046d #xb7) ;;  
   (cons #x40046e #x2b) ;;  
   (cons #x40046f #x20) ;;  
   (cons #x400470 #x00) ;;  
   (cons #x400471 #x48) ;; cmp %rbx,%rax 
   (cons #x400472 #x39) ;;  
   (cons #x400473 #xd8) ;;  
   (cons #x400474 #x72) ;; jb 400458 <__do_global_dtors_aux+0x38> 
   (cons #x400475 #xe2) ;;  
   (cons #x400476 #xc6) ;; movb $0x1,0x202ba3(%rip) # 603020 <completed.6531> 
   (cons #x400477 #x05) ;;  
   (cons #x400478 #xa3) ;;  
   (cons #x400479 #x2b) ;;  
   (cons #x40047a #x20) ;;  
   (cons #x40047b #x00) ;;  
   (cons #x40047c #x01) ;;  
   (cons #x40047d #x48) ;; add $0x8,%rsp 
   (cons #x40047e #x83) ;;  
   (cons #x40047f #xc4) ;;  
   (cons #x400480 #x08) ;;  
   (cons #x400481 #x5b) ;; pop %rbx 
   (cons #x400482 #x5d) ;; pop %rbp 
   (cons #x400483 #xc3) ;; retq 
   (cons #x400484 #x66) ;; data32 data32 nopw %cs:0x0(%rax,%rax,1) 
   (cons #x400485 #x66) ;;  
   (cons #x400486 #x66) ;;  
   (cons #x400487 #x2e) ;;  
   (cons #x400488 #x0f) ;;  
   (cons #x400489 #x1f) ;;  
   (cons #x40048a #x84) ;;  
   (cons #x40048b #x00) ;;  
   (cons #x40048c #x00) ;;  
   (cons #x40048d #x00) ;;  
   (cons #x40048e #x00) ;;  
   (cons #x40048f #x00) ;;  
   
;; Section: <frame_dummy>:


   (cons #x400490 #x48) ;; cmpq $0x0,0x2029b0(%rip) # 602e48 <__JCR_END__> 
   (cons #x400491 #x83) ;;  
   (cons #x400492 #x3d) ;;  
   (cons #x400493 #xb0) ;;  
   (cons #x400494 #x29) ;;  
   (cons #x400495 #x20) ;;  
   (cons #x400496 #x00) ;;  
   (cons #x400497 #x00) ;;  
   (cons #x400498 #x55) ;; push %rbp 
   (cons #x400499 #x48) ;; mov %rsp,%rbp 
   (cons #x40049a #x89) ;;  
   (cons #x40049b #xe5) ;;  
   (cons #x40049c #x74) ;; je 4004b0 <frame_dummy+0x20> 
   (cons #x40049d #x12) ;;  
   (cons #x40049e #xb8) ;; mov $0x0,%eax 
   (cons #x40049f #x00) ;;  
   (cons #x4004a0 #x00) ;;  
   (cons #x4004a1 #x00) ;;  
   (cons #x4004a2 #x00) ;;  
   (cons #x4004a3 #x48) ;; test %rax,%rax 
   (cons #x4004a4 #x85) ;;  
   (cons #x4004a5 #xc0) ;;  
   (cons #x4004a6 #x74) ;; je 4004b0 <frame_dummy+0x20> 
   (cons #x4004a7 #x08) ;;  
   (cons #x4004a8 #x5d) ;; pop %rbp 
   (cons #x4004a9 #xbf) ;; mov $0x602e48,%edi 
   (cons #x4004aa #x48) ;;  
   (cons #x4004ab #x2e) ;;  
   (cons #x4004ac #x60) ;;  
   (cons #x4004ad #x00) ;;  
   (cons #x4004ae #xff) ;; jmpq *%rax 
   (cons #x4004af #xe0) ;;  
   (cons #x4004b0 #x5d) ;; pop %rbp 
   (cons #x4004b1 #xc3) ;; retq 
   (cons #x4004b2 #x90) ;; nop 
   (cons #x4004b3 #x90) ;; nop 
   
;; Section: <getMemory>:


   (cons #x4004b4 #x55) ;; push %rbp 
   (cons #x4004b5 #x48) ;; mov %rsp,%rbp 
   (cons #x4004b6 #x89) ;;  
   (cons #x4004b7 #xe5) ;;  
   (cons #x4004b8 #x48) ;; mov %rdi,-0x18(%rbp) 
   (cons #x4004b9 #x89) ;;  
   (cons #x4004ba #x7d) ;;  
   (cons #x4004bb #xe8) ;;  
   (cons #x4004bc #x89) ;; mov %esi,-0x1c(%rbp) 
   (cons #x4004bd #x75) ;;  
   (cons #x4004be #xe4) ;;  
   (cons #x4004bf #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4004c0 #x8b) ;;  
   (cons #x4004c1 #x45) ;;  
   (cons #x4004c2 #xe8) ;;  
   (cons #x4004c3 #x48) ;; mov (%rax),%rdx 
   (cons #x4004c4 #x8b) ;;  
   (cons #x4004c5 #x10) ;;  
   (cons #x4004c6 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4004c7 #x8b) ;;  
   (cons #x4004c8 #x45) ;;  
   (cons #x4004c9 #xe8) ;;  
   (cons #x4004ca #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x4004cb #x40) ;;  
   (cons #x4004cc #x10) ;;  
   (cons #x4004cd #x48) ;; cltq 
   (cons #x4004ce #x98) ;;  
   (cons #x4004cf #x48) ;; shl $0x2,%rax 
   (cons #x4004d0 #xc1) ;;  
   (cons #x4004d1 #xe0) ;;  
   (cons #x4004d2 #x02) ;;  
   (cons #x4004d3 #x48) ;; add %rdx,%rax 
   (cons #x4004d4 #x01) ;;  
   (cons #x4004d5 #xd0) ;;  
   (cons #x4004d6 #x48) ;; mov %rax,-0x8(%rbp) 
   (cons #x4004d7 #x89) ;;  
   (cons #x4004d8 #x45) ;;  
   (cons #x4004d9 #xf8) ;;  
   (cons #x4004da #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4004db #x8b) ;;  
   (cons #x4004dc #x45) ;;  
   (cons #x4004dd #xe8) ;;  
   (cons #x4004de #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x4004df #x40) ;;  
   (cons #x4004e0 #x10) ;;  
   (cons #x4004e1 #x89) ;; mov %eax,%edx 
   (cons #x4004e2 #xc2) ;;  
   (cons #x4004e3 #x03) ;; add -0x1c(%rbp),%edx 
   (cons #x4004e4 #x55) ;;  
   (cons #x4004e5 #xe4) ;;  
   (cons #x4004e6 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4004e7 #x8b) ;;  
   (cons #x4004e8 #x45) ;;  
   (cons #x4004e9 #xe8) ;;  
   (cons #x4004ea #x89) ;; mov %edx,0x10(%rax) 
   (cons #x4004eb #x50) ;;  
   (cons #x4004ec #x10) ;;  
   (cons #x4004ed #x48) ;; mov -0x8(%rbp),%rax 
   (cons #x4004ee #x8b) ;;  
   (cons #x4004ef #x45) ;;  
   (cons #x4004f0 #xf8) ;;  
   (cons #x4004f1 #x5d) ;; pop %rbp 
   (cons #x4004f2 #xc3) ;; retq 
   
;; Section: <addClause>:


   (cons #x4004f3 #x55) ;; push %rbp 
   (cons #x4004f4 #x48) ;; mov %rsp,%rbp 
   (cons #x4004f5 #x89) ;;  
   (cons #x4004f6 #xe5) ;;  
   (cons #x4004f7 #x48) ;; sub $0x28,%rsp 
   (cons #x4004f8 #x83) ;;  
   (cons #x4004f9 #xec) ;;  
   (cons #x4004fa #x28) ;;  
   (cons #x4004fb #x48) ;; mov %rdi,-0x18(%rbp) 
   (cons #x4004fc #x89) ;;  
   (cons #x4004fd #x7d) ;;  
   (cons #x4004fe #xe8) ;;  
   (cons #x4004ff #x48) ;; mov %rsi,-0x20(%rbp) 
   (cons #x400500 #x89) ;;  
   (cons #x400501 #x75) ;;  
   (cons #x400502 #xe0) ;;  
   (cons #x400503 #x89) ;; mov %edx,-0x24(%rbp) 
   (cons #x400504 #x55) ;;  
   (cons #x400505 #xdc) ;;  
   (cons #x400506 #x83) ;; cmpl $0x1,-0x24(%rbp) 
   (cons #x400507 #x7d) ;;  
   (cons #x400508 #xdc) ;;  
   (cons #x400509 #x01) ;;  
   (cons #x40050a #x0f) ;; jle 4005c5 <addClause+0xd2> 
   (cons #x40050b #x8e) ;;  
   (cons #x40050c #xb5) ;;  
   (cons #x40050d #x00) ;;  
   (cons #x40050e #x00) ;;  
   (cons #x40050f #x00) ;;  
   (cons #x400510 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400511 #x8b) ;;  
   (cons #x400512 #x45) ;;  
   (cons #x400513 #xe8) ;;  
   (cons #x400514 #x48) ;; mov (%rax),%rdx 
   (cons #x400515 #x8b) ;;  
   (cons #x400516 #x10) ;;  
   (cons #x400517 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400518 #x8b) ;;  
   (cons #x400519 #x45) ;;  
   (cons #x40051a #xe8) ;;  
   (cons #x40051b #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x40051c #x40) ;;  
   (cons #x40051d #x10) ;;  
   (cons #x40051e #x48) ;; cltq 
   (cons #x40051f #x98) ;;  
   (cons #x400520 #x48) ;; shl $0x2,%rax 
   (cons #x400521 #xc1) ;;  
   (cons #x400522 #xe0) ;;  
   (cons #x400523 #x02) ;;  
   (cons #x400524 #x48) ;; add %rax,%rdx 
   (cons #x400525 #x01) ;;  
   (cons #x400526 #xc2) ;;  
   (cons #x400527 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400528 #x8b) ;;  
   (cons #x400529 #x45) ;;  
   (cons #x40052a #xe8) ;;  
   (cons #x40052b #x48) ;; mov 0x48(%rax),%rcx 
   (cons #x40052c #x8b) ;;  
   (cons #x40052d #x48) ;;  
   (cons #x40052e #x48) ;;  
   (cons #x40052f #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x400530 #x8b) ;;  
   (cons #x400531 #x45) ;;  
   (cons #x400532 #xe0) ;;  
   (cons #x400533 #x8b) ;; mov (%rax),%eax 
   (cons #x400534 #x00) ;;  
   (cons #x400535 #x48) ;; cltq 
   (cons #x400536 #x98) ;;  
   (cons #x400537 #x48) ;; shl $0x2,%rax 
   (cons #x400538 #xc1) ;;  
   (cons #x400539 #xe0) ;;  
   (cons #x40053a #x02) ;;  
   (cons #x40053b #x48) ;; add %rcx,%rax 
   (cons #x40053c #x01) ;;  
   (cons #x40053d #xc8) ;;  
   (cons #x40053e #x8b) ;; mov (%rax),%eax 
   (cons #x40053f #x00) ;;  
   (cons #x400540 #x89) ;; mov %eax,(%rdx) 
   (cons #x400541 #x02) ;;  
   (cons #x400542 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400543 #x8b) ;;  
   (cons #x400544 #x45) ;;  
   (cons #x400545 #xe8) ;;  
   (cons #x400546 #x48) ;; mov 0x48(%rax),%rdx 
   (cons #x400547 #x8b) ;;  
   (cons #x400548 #x50) ;;  
   (cons #x400549 #x48) ;;  
   (cons #x40054a #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x40054b #x8b) ;;  
   (cons #x40054c #x45) ;;  
   (cons #x40054d #xe0) ;;  
   (cons #x40054e #x8b) ;; mov (%rax),%eax 
   (cons #x40054f #x00) ;;  
   (cons #x400550 #x48) ;; cltq 
   (cons #x400551 #x98) ;;  
   (cons #x400552 #x48) ;; shl $0x2,%rax 
   (cons #x400553 #xc1) ;;  
   (cons #x400554 #xe0) ;;  
   (cons #x400555 #x02) ;;  
   (cons #x400556 #x48) ;; add %rax,%rdx 
   (cons #x400557 #x01) ;;  
   (cons #x400558 #xc2) ;;  
   (cons #x400559 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40055a #x8b) ;;  
   (cons #x40055b #x45) ;;  
   (cons #x40055c #xe8) ;;  
   (cons #x40055d #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x40055e #x40) ;;  
   (cons #x40055f #x10) ;;  
   (cons #x400560 #x89) ;; mov %eax,(%rdx) 
   (cons #x400561 #x02) ;;  
   (cons #x400562 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400563 #x8b) ;;  
   (cons #x400564 #x45) ;;  
   (cons #x400565 #xe8) ;;  
   (cons #x400566 #x48) ;; mov (%rax),%rdx 
   (cons #x400567 #x8b) ;;  
   (cons #x400568 #x10) ;;  
   (cons #x400569 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40056a #x8b) ;;  
   (cons #x40056b #x45) ;;  
   (cons #x40056c #xe8) ;;  
   (cons #x40056d #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x40056e #x40) ;;  
   (cons #x40056f #x10) ;;  
   (cons #x400570 #x48) ;; cltq 
   (cons #x400571 #x98) ;;  
   (cons #x400572 #x48) ;; add $0x1,%rax 
   (cons #x400573 #x83) ;;  
   (cons #x400574 #xc0) ;;  
   (cons #x400575 #x01) ;;  
   (cons #x400576 #x48) ;; shl $0x2,%rax 
   (cons #x400577 #xc1) ;;  
   (cons #x400578 #xe0) ;;  
   (cons #x400579 #x02) ;;  
   (cons #x40057a #x48) ;; add %rax,%rdx 
   (cons #x40057b #x01) ;;  
   (cons #x40057c #xc2) ;;  
   (cons #x40057d #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40057e #x8b) ;;  
   (cons #x40057f #x45) ;;  
   (cons #x400580 #xe8) ;;  
   (cons #x400581 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x400582 #x8b) ;;  
   (cons #x400583 #x40) ;;  
   (cons #x400584 #x48) ;;  
   (cons #x400585 #x48) ;; mov -0x20(%rbp),%rcx 
   (cons #x400586 #x8b) ;;  
   (cons #x400587 #x4d) ;;  
   (cons #x400588 #xe0) ;;  
   (cons #x400589 #x48) ;; add $0x4,%rcx 
   (cons #x40058a #x83) ;;  
   (cons #x40058b #xc1) ;;  
   (cons #x40058c #x04) ;;  
   (cons #x40058d #x8b) ;; mov (%rcx),%ecx 
   (cons #x40058e #x09) ;;  
   (cons #x40058f #x48) ;; movslq %ecx,%rcx 
   (cons #x400590 #x63) ;;  
   (cons #x400591 #xc9) ;;  
   (cons #x400592 #x48) ;; shl $0x2,%rcx 
   (cons #x400593 #xc1) ;;  
   (cons #x400594 #xe1) ;;  
   (cons #x400595 #x02) ;;  
   (cons #x400596 #x48) ;; add %rcx,%rax 
   (cons #x400597 #x01) ;;  
   (cons #x400598 #xc8) ;;  
   (cons #x400599 #x8b) ;; mov (%rax),%eax 
   (cons #x40059a #x00) ;;  
   (cons #x40059b #x89) ;; mov %eax,(%rdx) 
   (cons #x40059c #x02) ;;  
   (cons #x40059d #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40059e #x8b) ;;  
   (cons #x40059f #x45) ;;  
   (cons #x4005a0 #xe8) ;;  
   (cons #x4005a1 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x4005a2 #x8b) ;;  
   (cons #x4005a3 #x40) ;;  
   (cons #x4005a4 #x48) ;;  
   (cons #x4005a5 #x48) ;; mov -0x20(%rbp),%rdx 
   (cons #x4005a6 #x8b) ;;  
   (cons #x4005a7 #x55) ;;  
   (cons #x4005a8 #xe0) ;;  
   (cons #x4005a9 #x48) ;; add $0x4,%rdx 
   (cons #x4005aa #x83) ;;  
   (cons #x4005ab #xc2) ;;  
   (cons #x4005ac #x04) ;;  
   (cons #x4005ad #x8b) ;; mov (%rdx),%edx 
   (cons #x4005ae #x12) ;;  
   (cons #x4005af #x48) ;; movslq %edx,%rdx 
   (cons #x4005b0 #x63) ;;  
   (cons #x4005b1 #xd2) ;;  
   (cons #x4005b2 #x48) ;; shl $0x2,%rdx 
   (cons #x4005b3 #xc1) ;;  
   (cons #x4005b4 #xe2) ;;  
   (cons #x4005b5 #x02) ;;  
   (cons #x4005b6 #x48) ;; add %rax,%rdx 
   (cons #x4005b7 #x01) ;;  
   (cons #x4005b8 #xc2) ;;  
   (cons #x4005b9 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4005ba #x8b) ;;  
   (cons #x4005bb #x45) ;;  
   (cons #x4005bc #xe8) ;;  
   (cons #x4005bd #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x4005be #x40) ;;  
   (cons #x4005bf #x10) ;;  
   (cons #x4005c0 #x83) ;; add $0x1,%eax 
   (cons #x4005c1 #xc0) ;;  
   (cons #x4005c2 #x01) ;;  
   (cons #x4005c3 #x89) ;; mov %eax,(%rdx) 
   (cons #x4005c4 #x02) ;;  
   (cons #x4005c5 #x8b) ;; mov -0x24(%rbp),%eax 
   (cons #x4005c6 #x45) ;;  
   (cons #x4005c7 #xdc) ;;  
   (cons #x4005c8 #x8d) ;; lea 0x3(%rax),%edx 
   (cons #x4005c9 #x50) ;;  
   (cons #x4005ca #x03) ;;  
   (cons #x4005cb #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4005cc #x8b) ;;  
   (cons #x4005cd #x45) ;;  
   (cons #x4005ce #xe8) ;;  
   (cons #x4005cf #x89) ;; mov %edx,%esi 
   (cons #x4005d0 #xd6) ;;  
   (cons #x4005d1 #x48) ;; mov %rax,%rdi 
   (cons #x4005d2 #x89) ;;  
   (cons #x4005d3 #xc7) ;;  
   (cons #x4005d4 #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x4005d5 #xdb) ;;  
   (cons #x4005d6 #xfe) ;;  
   (cons #x4005d7 #xff) ;;  
   (cons #x4005d8 #xff) ;;  
   (cons #x4005d9 #x48) ;; add $0x8,%rax 
   (cons #x4005da #x83) ;;  
   (cons #x4005db #xc0) ;;  
   (cons #x4005dc #x08) ;;  
   (cons #x4005dd #x48) ;; mov %rax,-0x10(%rbp) 
   (cons #x4005de #x89) ;;  
   (cons #x4005df #x45) ;;  
   (cons #x4005e0 #xf0) ;;  
   (cons #x4005e1 #xc7) ;; movl $0x0,-0x4(%rbp) 
   (cons #x4005e2 #x45) ;;  
   (cons #x4005e3 #xfc) ;;  
   (cons #x4005e4 #x00) ;;  
   (cons #x4005e5 #x00) ;;  
   (cons #x4005e6 #x00) ;;  
   (cons #x4005e7 #x00) ;;  
   (cons #x4005e8 #xeb) ;; jmp 40060d <addClause+0x11a> 
   (cons #x4005e9 #x23) ;;  
   (cons #x4005ea #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x4005eb #x45) ;;  
   (cons #x4005ec #xfc) ;;  
   (cons #x4005ed #x48) ;; cltq 
   (cons #x4005ee #x98) ;;  
   (cons #x4005ef #x48) ;; shl $0x2,%rax 
   (cons #x4005f0 #xc1) ;;  
   (cons #x4005f1 #xe0) ;;  
   (cons #x4005f2 #x02) ;;  
   (cons #x4005f3 #x48) ;; add -0x10(%rbp),%rax 
   (cons #x4005f4 #x03) ;;  
   (cons #x4005f5 #x45) ;;  
   (cons #x4005f6 #xf0) ;;  
   (cons #x4005f7 #x8b) ;; mov -0x4(%rbp),%edx 
   (cons #x4005f8 #x55) ;;  
   (cons #x4005f9 #xfc) ;;  
   (cons #x4005fa #x48) ;; movslq %edx,%rdx 
   (cons #x4005fb #x63) ;;  
   (cons #x4005fc #xd2) ;;  
   (cons #x4005fd #x48) ;; shl $0x2,%rdx 
   (cons #x4005fe #xc1) ;;  
   (cons #x4005ff #xe2) ;;  
   (cons #x400600 #x02) ;;  
   (cons #x400601 #x48) ;; add -0x20(%rbp),%rdx 
   (cons #x400602 #x03) ;;  
   (cons #x400603 #x55) ;;  
   (cons #x400604 #xe0) ;;  
   (cons #x400605 #x8b) ;; mov (%rdx),%edx 
   (cons #x400606 #x12) ;;  
   (cons #x400607 #x89) ;; mov %edx,(%rax) 
   (cons #x400608 #x10) ;;  
   (cons #x400609 #x83) ;; addl $0x1,-0x4(%rbp) 
   (cons #x40060a #x45) ;;  
   (cons #x40060b #xfc) ;;  
   (cons #x40060c #x01) ;;  
   (cons #x40060d #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x40060e #x45) ;;  
   (cons #x40060f #xfc) ;;  
   (cons #x400610 #x3b) ;; cmp -0x24(%rbp),%eax 
   (cons #x400611 #x45) ;;  
   (cons #x400612 #xdc) ;;  
   (cons #x400613 #x7c) ;; jl 4005ea <addClause+0xf7> 
   (cons #x400614 #xd5) ;;  
   (cons #x400615 #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x400616 #x45) ;;  
   (cons #x400617 #xfc) ;;  
   (cons #x400618 #x48) ;; cltq 
   (cons #x400619 #x98) ;;  
   (cons #x40061a #x48) ;; shl $0x2,%rax 
   (cons #x40061b #xc1) ;;  
   (cons #x40061c #xe0) ;;  
   (cons #x40061d #x02) ;;  
   (cons #x40061e #x48) ;; add -0x10(%rbp),%rax 
   (cons #x40061f #x03) ;;  
   (cons #x400620 #x45) ;;  
   (cons #x400621 #xf0) ;;  
   (cons #x400622 #xc7) ;; movl $0x0,(%rax) 
   (cons #x400623 #x00) ;;  
   (cons #x400624 #x00) ;;  
   (cons #x400625 #x00) ;;  
   (cons #x400626 #x00) ;;  
   (cons #x400627 #x00) ;;  
   (cons #x400628 #x48) ;; mov -0x10(%rbp),%rax 
   (cons #x400629 #x8b) ;;  
   (cons #x40062a #x45) ;;  
   (cons #x40062b #xf0) ;;  
   (cons #x40062c #xc9) ;; leaveq 
   (cons #x40062d #xc3) ;; retq 
   
;; Section: <reduceDB>:


   (cons #x40062e #x55) ;; push %rbp 
   (cons #x40062f #x48) ;; mov %rsp,%rbp 
   (cons #x400630 #x89) ;;  
   (cons #x400631 #xe5) ;;  
   (cons #x400632 #x48) ;; sub $0x38,%rsp 
   (cons #x400633 #x83) ;;  
   (cons #x400634 #xec) ;;  
   (cons #x400635 #x38) ;;  
   (cons #x400636 #x48) ;; mov %rdi,-0x38(%rbp) 
   (cons #x400637 #x89) ;;  
   (cons #x400638 #x7d) ;;  
   (cons #x400639 #xc8) ;;  
   (cons #x40063a #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40063b #x8b) ;;  
   (cons #x40063c #x45) ;;  
   (cons #x40063d #xc8) ;;  
   (cons #x40063e #x48) ;; mov (%rax),%rdx 
   (cons #x40063f #x8b) ;;  
   (cons #x400640 #x10) ;;  
   (cons #x400641 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400642 #x8b) ;;  
   (cons #x400643 #x45) ;;  
   (cons #x400644 #xc8) ;;  
   (cons #x400645 #x8b) ;; mov 0x14(%rax),%eax 
   (cons #x400646 #x40) ;;  
   (cons #x400647 #x14) ;;  
   (cons #x400648 #x48) ;; cltq 
   (cons #x400649 #x98) ;;  
   (cons #x40064a #x48) ;; shl $0x2,%rax 
   (cons #x40064b #xc1) ;;  
   (cons #x40064c #xe0) ;;  
   (cons #x40064d #x02) ;;  
   (cons #x40064e #x48) ;; add %rdx,%rax 
   (cons #x40064f #x01) ;;  
   (cons #x400650 #xd0) ;;  
   (cons #x400651 #x48) ;; mov %rax,-0x30(%rbp) 
   (cons #x400652 #x89) ;;  
   (cons #x400653 #x45) ;;  
   (cons #x400654 #xd0) ;;  
   (cons #x400655 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400656 #x8b) ;;  
   (cons #x400657 #x45) ;;  
   (cons #x400658 #xc8) ;;  
   (cons #x400659 #x48) ;; mov (%rax),%rdx 
   (cons #x40065a #x8b) ;;  
   (cons #x40065b #x10) ;;  
   (cons #x40065c #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40065d #x8b) ;;  
   (cons #x40065e #x45) ;;  
   (cons #x40065f #xc8) ;;  
   (cons #x400660 #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x400661 #x40) ;;  
   (cons #x400662 #x10) ;;  
   (cons #x400663 #x48) ;; cltq 
   (cons #x400664 #x98) ;;  
   (cons #x400665 #x48) ;; shl $0x2,%rax 
   (cons #x400666 #xc1) ;;  
   (cons #x400667 #xe0) ;;  
   (cons #x400668 #x02) ;;  
   (cons #x400669 #x48) ;; add %rdx,%rax 
   (cons #x40066a #x01) ;;  
   (cons #x40066b #xd0) ;;  
   (cons #x40066c #x48) ;; mov %rax,-0x18(%rbp) 
   (cons #x40066d #x89) ;;  
   (cons #x40066e #x45) ;;  
   (cons #x40066f #xe8) ;;  
   (cons #x400670 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400671 #x8b) ;;  
   (cons #x400672 #x45) ;;  
   (cons #x400673 #xc8) ;;  
   (cons #x400674 #x8b) ;; mov 0x18(%rax),%edx 
   (cons #x400675 #x50) ;;  
   (cons #x400676 #x18) ;;  
   (cons #x400677 #x89) ;; mov %edx,%eax 
   (cons #x400678 #xd0) ;;  
   (cons #x400679 #xc1) ;; shl $0x3,%eax 
   (cons #x40067a #xe0) ;;  
   (cons #x40067b #x03) ;;  
   (cons #x40067c #x01) ;; add %edx,%eax 
   (cons #x40067d #xd0) ;;  
   (cons #x40067e #x89) ;; mov %eax,%edx 
   (cons #x40067f #xc2) ;;  
   (cons #x400680 #xc1) ;; sar $0x3,%edx 
   (cons #x400681 #xfa) ;;  
   (cons #x400682 #x03) ;;  
   (cons #x400683 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400684 #x8b) ;;  
   (cons #x400685 #x45) ;;  
   (cons #x400686 #xc8) ;;  
   (cons #x400687 #x89) ;; mov %edx,0x18(%rax) 
   (cons #x400688 #x50) ;;  
   (cons #x400689 #x18) ;;  
   (cons #x40068a #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40068b #x8b) ;;  
   (cons #x40068c #x45) ;;  
   (cons #x40068d #xc8) ;;  
   (cons #x40068e #x8b) ;; mov 0x14(%rax),%edx 
   (cons #x40068f #x50) ;;  
   (cons #x400690 #x14) ;;  
   (cons #x400691 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400692 #x8b) ;;  
   (cons #x400693 #x45) ;;  
   (cons #x400694 #xc8) ;;  
   (cons #x400695 #x89) ;; mov %edx,0x10(%rax) 
   (cons #x400696 #x50) ;;  
   (cons #x400697 #x10) ;;  
   (cons #x400698 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400699 #x8b) ;;  
   (cons #x40069a #x45) ;;  
   (cons #x40069b #xc8) ;;  
   (cons #x40069c #xc7) ;; movl $0x0,0x1c(%rax) 
   (cons #x40069d #x40) ;;  
   (cons #x40069e #x1c) ;;  
   (cons #x40069f #x00) ;;  
   (cons #x4006a0 #x00) ;;  
   (cons #x4006a1 #x00) ;;  
   (cons #x4006a2 #x00) ;;  
   (cons #x4006a3 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4006a4 #x8b) ;;  
   (cons #x4006a5 #x45) ;;  
   (cons #x4006a6 #xc8) ;;  
   (cons #x4006a7 #x8b) ;; mov 0x8(%rax),%eax 
   (cons #x4006a8 #x40) ;;  
   (cons #x4006a9 #x08) ;;  
   (cons #x4006aa #xf7) ;; neg %eax 
   (cons #x4006ab #xd8) ;;  
   (cons #x4006ac #x89) ;; mov %eax,-0xc(%rbp) 
   (cons #x4006ad #x45) ;;  
   (cons #x4006ae #xf4) ;;  
   (cons #x4006af #xeb) ;; jmp 40072f <reduceDB+0x101> 
   (cons #x4006b0 #x7e) ;;  
   (cons #x4006b1 #x83) ;; cmpl $0x0,-0xc(%rbp) 
   (cons #x4006b2 #x7d) ;;  
   (cons #x4006b3 #xf4) ;;  
   (cons #x4006b4 #x00) ;;  
   (cons #x4006b5 #x74) ;; je 40072a <reduceDB+0xfc> 
   (cons #x4006b6 #x73) ;;  
   (cons #x4006b7 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4006b8 #x8b) ;;  
   (cons #x4006b9 #x45) ;;  
   (cons #x4006ba #xc8) ;;  
   (cons #x4006bb #x48) ;; mov 0x48(%rax),%rax 
   (cons #x4006bc #x8b) ;;  
   (cons #x4006bd #x40) ;;  
   (cons #x4006be #x48) ;;  
   (cons #x4006bf #x8b) ;; mov -0xc(%rbp),%edx 
   (cons #x4006c0 #x55) ;;  
   (cons #x4006c1 #xf4) ;;  
   (cons #x4006c2 #x48) ;; movslq %edx,%rdx 
   (cons #x4006c3 #x63) ;;  
   (cons #x4006c4 #xd2) ;;  
   (cons #x4006c5 #x48) ;; shl $0x2,%rdx 
   (cons #x4006c6 #xc1) ;;  
   (cons #x4006c7 #xe2) ;;  
   (cons #x4006c8 #x02) ;;  
   (cons #x4006c9 #x48) ;; add %rdx,%rax 
   (cons #x4006ca #x01) ;;  
   (cons #x4006cb #xd0) ;;  
   (cons #x4006cc #x48) ;; mov %rax,-0x28(%rbp) 
   (cons #x4006cd #x89) ;;  
   (cons #x4006ce #x45) ;;  
   (cons #x4006cf #xd8) ;;  
   (cons #x4006d0 #xeb) ;; jmp 40071d <reduceDB+0xef> 
   (cons #x4006d1 #x4b) ;;  
   (cons #x4006d2 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4006d3 #x8b) ;;  
   (cons #x4006d4 #x45) ;;  
   (cons #x4006d5 #xd8) ;;  
   (cons #x4006d6 #x8b) ;; mov (%rax),%edx 
   (cons #x4006d7 #x10) ;;  
   (cons #x4006d8 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4006d9 #x8b) ;;  
   (cons #x4006da #x45) ;;  
   (cons #x4006db #xc8) ;;  
   (cons #x4006dc #x8b) ;; mov 0x14(%rax),%eax 
   (cons #x4006dd #x40) ;;  
   (cons #x4006de #x14) ;;  
   (cons #x4006df #x39) ;; cmp %eax,%edx 
   (cons #x4006e0 #xc2) ;;  
   (cons #x4006e1 #x7d) ;; jge 4006ff <reduceDB+0xd1> 
   (cons #x4006e2 #x1c) ;;  
   (cons #x4006e3 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4006e4 #x8b) ;;  
   (cons #x4006e5 #x45) ;;  
   (cons #x4006e6 #xc8) ;;  
   (cons #x4006e7 #x48) ;; mov (%rax),%rdx 
   (cons #x4006e8 #x8b) ;;  
   (cons #x4006e9 #x10) ;;  
   (cons #x4006ea #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4006eb #x8b) ;;  
   (cons #x4006ec #x45) ;;  
   (cons #x4006ed #xd8) ;;  
   (cons #x4006ee #x8b) ;; mov (%rax),%eax 
   (cons #x4006ef #x00) ;;  
   (cons #x4006f0 #x48) ;; cltq 
   (cons #x4006f1 #x98) ;;  
   (cons #x4006f2 #x48) ;; shl $0x2,%rax 
   (cons #x4006f3 #xc1) ;;  
   (cons #x4006f4 #xe0) ;;  
   (cons #x4006f5 #x02) ;;  
   (cons #x4006f6 #x48) ;; add %rdx,%rax 
   (cons #x4006f7 #x01) ;;  
   (cons #x4006f8 #xd0) ;;  
   (cons #x4006f9 #x48) ;; mov %rax,-0x28(%rbp) 
   (cons #x4006fa #x89) ;;  
   (cons #x4006fb #x45) ;;  
   (cons #x4006fc #xd8) ;;  
   (cons #x4006fd #xeb) ;; jmp 40071d <reduceDB+0xef> 
   (cons #x4006fe #x1e) ;;  
   (cons #x4006ff #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400700 #x8b) ;;  
   (cons #x400701 #x45) ;;  
   (cons #x400702 #xc8) ;;  
   (cons #x400703 #x48) ;; mov (%rax),%rdx 
   (cons #x400704 #x8b) ;;  
   (cons #x400705 #x10) ;;  
   (cons #x400706 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x400707 #x8b) ;;  
   (cons #x400708 #x45) ;;  
   (cons #x400709 #xd8) ;;  
   (cons #x40070a #x8b) ;; mov (%rax),%eax 
   (cons #x40070b #x00) ;;  
   (cons #x40070c #x48) ;; cltq 
   (cons #x40070d #x98) ;;  
   (cons #x40070e #x48) ;; shl $0x2,%rax 
   (cons #x40070f #xc1) ;;  
   (cons #x400710 #xe0) ;;  
   (cons #x400711 #x02) ;;  
   (cons #x400712 #x48) ;; add %rdx,%rax 
   (cons #x400713 #x01) ;;  
   (cons #x400714 #xd0) ;;  
   (cons #x400715 #x8b) ;; mov (%rax),%edx 
   (cons #x400716 #x10) ;;  
   (cons #x400717 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x400718 #x8b) ;;  
   (cons #x400719 #x45) ;;  
   (cons #x40071a #xd8) ;;  
   (cons #x40071b #x89) ;; mov %edx,(%rax) 
   (cons #x40071c #x10) ;;  
   (cons #x40071d #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40071e #x8b) ;;  
   (cons #x40071f #x45) ;;  
   (cons #x400720 #xd8) ;;  
   (cons #x400721 #x8b) ;; mov (%rax),%eax 
   (cons #x400722 #x00) ;;  
   (cons #x400723 #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x400724 #xf8) ;;  
   (cons #x400725 #xf7) ;;  
   (cons #x400726 #x75) ;; jne 4006d2 <reduceDB+0xa4> 
   (cons #x400727 #xaa) ;;  
   (cons #x400728 #xeb) ;; jmp 40072b <reduceDB+0xfd> 
   (cons #x400729 #x01) ;;  
   (cons #x40072a #x90) ;; nop 
   (cons #x40072b #x83) ;; addl $0x1,-0xc(%rbp) 
   (cons #x40072c #x45) ;;  
   (cons #x40072d #xf4) ;;  
   (cons #x40072e #x01) ;;  
   (cons #x40072f #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400730 #x8b) ;;  
   (cons #x400731 #x45) ;;  
   (cons #x400732 #xc8) ;;  
   (cons #x400733 #x8b) ;; mov 0x8(%rax),%eax 
   (cons #x400734 #x40) ;;  
   (cons #x400735 #x08) ;;  
   (cons #x400736 #x3b) ;; cmp -0xc(%rbp),%eax 
   (cons #x400737 #x45) ;;  
   (cons #x400738 #xf4) ;;  
   (cons #x400739 #x0f) ;; jge 4006b1 <reduceDB+0x83> 
   (cons #x40073a #x8d) ;;  
   (cons #x40073b #x72) ;;  
   (cons #x40073c #xff) ;;  
   (cons #x40073d #xff) ;;  
   (cons #x40073e #xff) ;;  
   (cons #x40073f #xe9) ;; jmpq 4007ed <reduceDB+0x1bf> 
   (cons #x400740 #xa9) ;;  
   (cons #x400741 #x00) ;;  
   (cons #x400742 #x00) ;;  
   (cons #x400743 #x00) ;;  
   (cons #x400744 #xc7) ;; movl $0x0,-0x8(%rbp) 
   (cons #x400745 #x45) ;;  
   (cons #x400746 #xf8) ;;  
   (cons #x400747 #x00) ;;  
   (cons #x400748 #x00) ;;  
   (cons #x400749 #x00) ;;  
   (cons #x40074a #x00) ;;  
   (cons #x40074b #xc7) ;; movl $0x0,-0x4(%rbp) 
   (cons #x40074c #x45) ;;  
   (cons #x40074d #xfc) ;;  
   (cons #x40074e #x00) ;;  
   (cons #x40074f #x00) ;;  
   (cons #x400750 #x00) ;;  
   (cons #x400751 #x00) ;;  
   (cons #x400752 #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x400753 #x8b) ;;  
   (cons #x400754 #x45) ;;  
   (cons #x400755 #xd0) ;;  
   (cons #x400756 #x48) ;; add $0x8,%rax 
   (cons #x400757 #x83) ;;  
   (cons #x400758 #xc0) ;;  
   (cons #x400759 #x08) ;;  
   (cons #x40075a #x48) ;; mov %rax,-0x20(%rbp) 
   (cons #x40075b #x89) ;;  
   (cons #x40075c #x45) ;;  
   (cons #x40075d #xe0) ;;  
   (cons #x40075e #xeb) ;; jmp 4007a6 <reduceDB+0x178> 
   (cons #x40075f #x46) ;;  
   (cons #x400760 #x83) ;; addl $0x1,-0x8(%rbp) 
   (cons #x400761 #x45) ;;  
   (cons #x400762 #xf8) ;;  
   (cons #x400763 #x01) ;;  
   (cons #x400764 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x400765 #x8b) ;;  
   (cons #x400766 #x45) ;;  
   (cons #x400767 #xe0) ;;  
   (cons #x400768 #x8b) ;; mov (%rax),%eax 
   (cons #x400769 #x00) ;;  
   (cons #x40076a #x85) ;; test %eax,%eax 
   (cons #x40076b #xc0) ;;  
   (cons #x40076c #x0f) ;; setg %al 
   (cons #x40076d #x9f) ;;  
   (cons #x40076e #xc0) ;;  
   (cons #x40076f #x0f) ;; movzbl %al,%ecx 
   (cons #x400770 #xb6) ;;  
   (cons #x400771 #xc8) ;;  
   (cons #x400772 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x400773 #x8b) ;;  
   (cons #x400774 #x45) ;;  
   (cons #x400775 #xc8) ;;  
   (cons #x400776 #x48) ;; mov 0x28(%rax),%rsi 
   (cons #x400777 #x8b) ;;  
   (cons #x400778 #x70) ;;  
   (cons #x400779 #x28) ;;  
   (cons #x40077a #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x40077b #x8b) ;;  
   (cons #x40077c #x45) ;;  
   (cons #x40077d #xe0) ;;  
   (cons #x40077e #x8b) ;; mov (%rax),%eax 
   (cons #x40077f #x00) ;;  
   (cons #x400780 #x89) ;; mov %eax,%edx 
   (cons #x400781 #xc2) ;;  
   (cons #x400782 #xc1) ;; sar $0x1f,%edx 
   (cons #x400783 #xfa) ;;  
   (cons #x400784 #x1f) ;;  
   (cons #x400785 #x31) ;; xor %edx,%eax 
   (cons #x400786 #xd0) ;;  
   (cons #x400787 #x29) ;; sub %edx,%eax 
   (cons #x400788 #xd0) ;;  
   (cons #x400789 #x48) ;; cltq 
   (cons #x40078a #x98) ;;  
   (cons #x40078b #x48) ;; shl $0x2,%rax 
   (cons #x40078c #xc1) ;;  
   (cons #x40078d #xe0) ;;  
   (cons #x40078e #x02) ;;  
   (cons #x40078f #x48) ;; add %rsi,%rax 
   (cons #x400790 #x01) ;;  
   (cons #x400791 #xf0) ;;  
   (cons #x400792 #x8b) ;; mov (%rax),%eax 
   (cons #x400793 #x00) ;;  
   (cons #x400794 #x39) ;; cmp %eax,%ecx 
   (cons #x400795 #xc1) ;;  
   (cons #x400796 #x0f) ;; sete %al 
   (cons #x400797 #x94) ;;  
   (cons #x400798 #xc0) ;;  
   (cons #x400799 #x48) ;; addq $0x4,-0x20(%rbp) 
   (cons #x40079a #x83) ;;  
   (cons #x40079b #x45) ;;  
   (cons #x40079c #xe0) ;;  
   (cons #x40079d #x04) ;;  
   (cons #x40079e #x84) ;; test %al,%al 
   (cons #x40079f #xc0) ;;  
   (cons #x4007a0 #x74) ;; je 4007a6 <reduceDB+0x178> 
   (cons #x4007a1 #x04) ;;  
   (cons #x4007a2 #x83) ;; addl $0x1,-0x4(%rbp) 
   (cons #x4007a3 #x45) ;;  
   (cons #x4007a4 #xfc) ;;  
   (cons #x4007a5 #x01) ;;  
   (cons #x4007a6 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x4007a7 #x8b) ;;  
   (cons #x4007a8 #x45) ;;  
   (cons #x4007a9 #xe0) ;;  
   (cons #x4007aa #x8b) ;; mov (%rax),%eax 
   (cons #x4007ab #x00) ;;  
   (cons #x4007ac #x85) ;; test %eax,%eax 
   (cons #x4007ad #xc0) ;;  
   (cons #x4007ae #x75) ;; jne 400760 <reduceDB+0x132> 
   (cons #x4007af #xb0) ;;  
   (cons #x4007b0 #x83) ;; cmpl $0x3,-0x4(%rbp) 
   (cons #x4007b1 #x7d) ;;  
   (cons #x4007b2 #xfc) ;;  
   (cons #x4007b3 #x03) ;;  
   (cons #x4007b4 #x7f) ;; jg 4007e1 <reduceDB+0x1b3> 
   (cons #x4007b5 #x2b) ;;  
   (cons #x4007b6 #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x4007b7 #x8b) ;;  
   (cons #x4007b8 #x45) ;;  
   (cons #x4007b9 #xd0) ;;  
   (cons #x4007ba #x48) ;; lea 0x8(%rax),%rcx 
   (cons #x4007bb #x8d) ;;  
   (cons #x4007bc #x48) ;;  
   (cons #x4007bd #x08) ;;  
   (cons #x4007be #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x4007bf #x55) ;;  
   (cons #x4007c0 #xf8) ;;  
   (cons #x4007c1 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4007c2 #x8b) ;;  
   (cons #x4007c3 #x45) ;;  
   (cons #x4007c4 #xc8) ;;  
   (cons #x4007c5 #x48) ;; mov %rcx,%rsi 
   (cons #x4007c6 #x89) ;;  
   (cons #x4007c7 #xce) ;;  
   (cons #x4007c8 #x48) ;; mov %rax,%rdi 
   (cons #x4007c9 #x89) ;;  
   (cons #x4007ca #xc7) ;;  
   (cons #x4007cb #xe8) ;; callq 4004f3 <addClause> 
   (cons #x4007cc #x23) ;;  
   (cons #x4007cd #xfd) ;;  
   (cons #x4007ce #xff) ;;  
   (cons #x4007cf #xff) ;;  
   (cons #x4007d0 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4007d1 #x8b) ;;  
   (cons #x4007d2 #x45) ;;  
   (cons #x4007d3 #xc8) ;;  
   (cons #x4007d4 #x8b) ;; mov 0x1c(%rax),%eax 
   (cons #x4007d5 #x40) ;;  
   (cons #x4007d6 #x1c) ;;  
   (cons #x4007d7 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x4007d8 #x50) ;;  
   (cons #x4007d9 #x01) ;;  
   (cons #x4007da #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4007db #x8b) ;;  
   (cons #x4007dc #x45) ;;  
   (cons #x4007dd #xc8) ;;  
   (cons #x4007de #x89) ;; mov %edx,0x1c(%rax) 
   (cons #x4007df #x50) ;;  
   (cons #x4007e0 #x1c) ;;  
   (cons #x4007e1 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x4007e2 #x8b) ;;  
   (cons #x4007e3 #x45) ;;  
   (cons #x4007e4 #xe0) ;;  
   (cons #x4007e5 #x48) ;; add $0x4,%rax 
   (cons #x4007e6 #x83) ;;  
   (cons #x4007e7 #xc0) ;;  
   (cons #x4007e8 #x04) ;;  
   (cons #x4007e9 #x48) ;; mov %rax,-0x30(%rbp) 
   (cons #x4007ea #x89) ;;  
   (cons #x4007eb #x45) ;;  
   (cons #x4007ec #xd0) ;;  
   (cons #x4007ed #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x4007ee #x8b) ;;  
   (cons #x4007ef #x45) ;;  
   (cons #x4007f0 #xd0) ;;  
   (cons #x4007f1 #x48) ;; cmp -0x18(%rbp),%rax 
   (cons #x4007f2 #x3b) ;;  
   (cons #x4007f3 #x45) ;;  
   (cons #x4007f4 #xe8) ;;  
   (cons #x4007f5 #x0f) ;; jb 400744 <reduceDB+0x116> 
   (cons #x4007f6 #x82) ;;  
   (cons #x4007f7 #x49) ;;  
   (cons #x4007f8 #xff) ;;  
   (cons #x4007f9 #xff) ;;  
   (cons #x4007fa #xff) ;;  
   (cons #x4007fb #xc9) ;; leaveq 
   (cons #x4007fc #xc3) ;; retq 
   
;; Section: <heapRemoveTop>:


   (cons #x4007fd #x55) ;; push %rbp 
   (cons #x4007fe #x48) ;; mov %rsp,%rbp 
   (cons #x4007ff #x89) ;;  
   (cons #x400800 #xe5) ;;  
   (cons #x400801 #x48) ;; mov %rdi,-0x18(%rbp) 
   (cons #x400802 #x89) ;;  
   (cons #x400803 #x7d) ;;  
   (cons #x400804 #xe8) ;;  
   (cons #x400805 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400806 #x8b) ;;  
   (cons #x400807 #x45) ;;  
   (cons #x400808 #xe8) ;;  
   (cons #x400809 #x48) ;; mov 0x60(%rax),%rdx 
   (cons #x40080a #x8b) ;;  
   (cons #x40080b #x50) ;;  
   (cons #x40080c #x60) ;;  
   (cons #x40080d #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40080e #x8b) ;;  
   (cons #x40080f #x45) ;;  
   (cons #x400810 #xe8) ;;  
   (cons #x400811 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400812 #x8b) ;;  
   (cons #x400813 #x40) ;;  
   (cons #x400814 #x50) ;;  
   (cons #x400815 #x8b) ;; mov (%rax),%eax 
   (cons #x400816 #x00) ;;  
   (cons #x400817 #x48) ;; cltq 
   (cons #x400818 #x98) ;;  
   (cons #x400819 #x48) ;; shl $0x2,%rax 
   (cons #x40081a #xc1) ;;  
   (cons #x40081b #xe0) ;;  
   (cons #x40081c #x02) ;;  
   (cons #x40081d #x48) ;; add %rdx,%rax 
   (cons #x40081e #x01) ;;  
   (cons #x40081f #xd0) ;;  
   (cons #x400820 #xc7) ;; movl $0xfffffff7,(%rax) 
   (cons #x400821 #x00) ;;  
   (cons #x400822 #xf7) ;;  
   (cons #x400823 #xff) ;;  
   (cons #x400824 #xff) ;;  
   (cons #x400825 #xff) ;;  
   (cons #x400826 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400827 #x8b) ;;  
   (cons #x400828 #x45) ;;  
   (cons #x400829 #xe8) ;;  
   (cons #x40082a #x48) ;; mov 0x50(%rax),%rdx 
   (cons #x40082b #x8b) ;;  
   (cons #x40082c #x50) ;;  
   (cons #x40082d #x50) ;;  
   (cons #x40082e #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40082f #x8b) ;;  
   (cons #x400830 #x45) ;;  
   (cons #x400831 #xe8) ;;  
   (cons #x400832 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x400833 #x40) ;;  
   (cons #x400834 #x58) ;;  
   (cons #x400835 #x48) ;; movslq %eax,%rcx 
   (cons #x400836 #x63) ;;  
   (cons #x400837 #xc8) ;;  
   (cons #x400838 #x48) ;; shl $0x2,%rcx 
   (cons #x400839 #xc1) ;;  
   (cons #x40083a #xe1) ;;  
   (cons #x40083b #x02) ;;  
   (cons #x40083c #x48) ;; add %rcx,%rdx 
   (cons #x40083d #x01) ;;  
   (cons #x40083e #xca) ;;  
   (cons #x40083f #x8b) ;; mov (%rdx),%edx 
   (cons #x400840 #x12) ;;  
   (cons #x400841 #x89) ;; mov %edx,-0x8(%rbp) 
   (cons #x400842 #x55) ;;  
   (cons #x400843 #xf8) ;;  
   (cons #x400844 #x8d) ;; lea -0x1(%rax),%edx 
   (cons #x400845 #x50) ;;  
   (cons #x400846 #xff) ;;  
   (cons #x400847 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400848 #x8b) ;;  
   (cons #x400849 #x45) ;;  
   (cons #x40084a #xe8) ;;  
   (cons #x40084b #x89) ;; mov %edx,0x58(%rax) 
   (cons #x40084c #x50) ;;  
   (cons #x40084d #x58) ;;  
   (cons #x40084e #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40084f #x8b) ;;  
   (cons #x400850 #x45) ;;  
   (cons #x400851 #xe8) ;;  
   (cons #x400852 #x48) ;; mov 0x68(%rax),%rax 
   (cons #x400853 #x8b) ;;  
   (cons #x400854 #x40) ;;  
   (cons #x400855 #x68) ;;  
   (cons #x400856 #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x400857 #x55) ;;  
   (cons #x400858 #xf8) ;;  
   (cons #x400859 #x48) ;; movslq %edx,%rdx 
   (cons #x40085a #x63) ;;  
   (cons #x40085b #xd2) ;;  
   (cons #x40085c #x48) ;; shl $0x2,%rdx 
   (cons #x40085d #xc1) ;;  
   (cons #x40085e #xe2) ;;  
   (cons #x40085f #x02) ;;  
   (cons #x400860 #x48) ;; add %rdx,%rax 
   (cons #x400861 #x01) ;;  
   (cons #x400862 #xd0) ;;  
   (cons #x400863 #x8b) ;; mov (%rax),%eax 
   (cons #x400864 #x00) ;;  
   (cons #x400865 #x89) ;; mov %eax,-0x4(%rbp) 
   (cons #x400866 #x45) ;;  
   (cons #x400867 #xfc) ;;  
   (cons #x400868 #xc7) ;; movl $0x0,-0x10(%rbp) 
   (cons #x400869 #x45) ;;  
   (cons #x40086a #xf0) ;;  
   (cons #x40086b #x00) ;;  
   (cons #x40086c #x00) ;;  
   (cons #x40086d #x00) ;;  
   (cons #x40086e #x00) ;;  
   (cons #x40086f #xc7) ;; movl $0x1,-0xc(%rbp) 
   (cons #x400870 #x45) ;;  
   (cons #x400871 #xf4) ;;  
   (cons #x400872 #x01) ;;  
   (cons #x400873 #x00) ;;  
   (cons #x400874 #x00) ;;  
   (cons #x400875 #x00) ;;  
   (cons #x400876 #xe9) ;; jmpq 400982 <heapRemoveTop+0x185> 
   (cons #x400877 #x07) ;;  
   (cons #x400878 #x01) ;;  
   (cons #x400879 #x00) ;;  
   (cons #x40087a #x00) ;;  
   (cons #x40087b #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40087c #x8b) ;;  
   (cons #x40087d #x45) ;;  
   (cons #x40087e #xe8) ;;  
   (cons #x40087f #x48) ;; mov 0x68(%rax),%rdx 
   (cons #x400880 #x8b) ;;  
   (cons #x400881 #x50) ;;  
   (cons #x400882 #x68) ;;  
   (cons #x400883 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400884 #x8b) ;;  
   (cons #x400885 #x45) ;;  
   (cons #x400886 #xe8) ;;  
   (cons #x400887 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400888 #x8b) ;;  
   (cons #x400889 #x40) ;;  
   (cons #x40088a #x50) ;;  
   (cons #x40088b #x8b) ;; mov -0xc(%rbp),%ecx 
   (cons #x40088c #x4d) ;;  
   (cons #x40088d #xf4) ;;  
   (cons #x40088e #x48) ;; movslq %ecx,%rcx 
   (cons #x40088f #x63) ;;  
   (cons #x400890 #xc9) ;;  
   (cons #x400891 #x48) ;; shl $0x2,%rcx 
   (cons #x400892 #xc1) ;;  
   (cons #x400893 #xe1) ;;  
   (cons #x400894 #x02) ;;  
   (cons #x400895 #x48) ;; add %rcx,%rax 
   (cons #x400896 #x01) ;;  
   (cons #x400897 #xc8) ;;  
   (cons #x400898 #x8b) ;; mov (%rax),%eax 
   (cons #x400899 #x00) ;;  
   (cons #x40089a #x48) ;; cltq 
   (cons #x40089b #x98) ;;  
   (cons #x40089c #x48) ;; shl $0x2,%rax 
   (cons #x40089d #xc1) ;;  
   (cons #x40089e #xe0) ;;  
   (cons #x40089f #x02) ;;  
   (cons #x4008a0 #x48) ;; add %rdx,%rax 
   (cons #x4008a1 #x01) ;;  
   (cons #x4008a2 #xd0) ;;  
   (cons #x4008a3 #x8b) ;; mov (%rax),%edx 
   (cons #x4008a4 #x10) ;;  
   (cons #x4008a5 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4008a6 #x8b) ;;  
   (cons #x4008a7 #x45) ;;  
   (cons #x4008a8 #xe8) ;;  
   (cons #x4008a9 #x48) ;; mov 0x68(%rax),%rcx 
   (cons #x4008aa #x8b) ;;  
   (cons #x4008ab #x48) ;;  
   (cons #x4008ac #x68) ;;  
   (cons #x4008ad #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4008ae #x8b) ;;  
   (cons #x4008af #x45) ;;  
   (cons #x4008b0 #xe8) ;;  
   (cons #x4008b1 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x4008b2 #x8b) ;;  
   (cons #x4008b3 #x40) ;;  
   (cons #x4008b4 #x50) ;;  
   (cons #x4008b5 #x8b) ;; mov -0xc(%rbp),%esi 
   (cons #x4008b6 #x75) ;;  
   (cons #x4008b7 #xf4) ;;  
   (cons #x4008b8 #x48) ;; movslq %esi,%rsi 
   (cons #x4008b9 #x63) ;;  
   (cons #x4008ba #xf6) ;;  
   (cons #x4008bb #x48) ;; add $0x1,%rsi 
   (cons #x4008bc #x83) ;;  
   (cons #x4008bd #xc6) ;;  
   (cons #x4008be #x01) ;;  
   (cons #x4008bf #x48) ;; shl $0x2,%rsi 
   (cons #x4008c0 #xc1) ;;  
   (cons #x4008c1 #xe6) ;;  
   (cons #x4008c2 #x02) ;;  
   (cons #x4008c3 #x48) ;; add %rsi,%rax 
   (cons #x4008c4 #x01) ;;  
   (cons #x4008c5 #xf0) ;;  
   (cons #x4008c6 #x8b) ;; mov (%rax),%eax 
   (cons #x4008c7 #x00) ;;  
   (cons #x4008c8 #x48) ;; cltq 
   (cons #x4008c9 #x98) ;;  
   (cons #x4008ca #x48) ;; shl $0x2,%rax 
   (cons #x4008cb #xc1) ;;  
   (cons #x4008cc #xe0) ;;  
   (cons #x4008cd #x02) ;;  
   (cons #x4008ce #x48) ;; add %rcx,%rax 
   (cons #x4008cf #x01) ;;  
   (cons #x4008d0 #xc8) ;;  
   (cons #x4008d1 #x8b) ;; mov (%rax),%eax 
   (cons #x4008d2 #x00) ;;  
   (cons #x4008d3 #x39) ;; cmp %eax,%edx 
   (cons #x4008d4 #xc2) ;;  
   (cons #x4008d5 #x7d) ;; jge 4008e7 <heapRemoveTop+0xea> 
   (cons #x4008d6 #x10) ;;  
   (cons #x4008d7 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4008d8 #x8b) ;;  
   (cons #x4008d9 #x45) ;;  
   (cons #x4008da #xe8) ;;  
   (cons #x4008db #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x4008dc #x40) ;;  
   (cons #x4008dd #x58) ;;  
   (cons #x4008de #x3b) ;; cmp -0xc(%rbp),%eax 
   (cons #x4008df #x45) ;;  
   (cons #x4008e0 #xf4) ;;  
   (cons #x4008e1 #x7e) ;; jle 4008e7 <heapRemoveTop+0xea> 
   (cons #x4008e2 #x04) ;;  
   (cons #x4008e3 #x83) ;; addl $0x1,-0xc(%rbp) 
   (cons #x4008e4 #x45) ;;  
   (cons #x4008e5 #xf4) ;;  
   (cons #x4008e6 #x01) ;;  
   (cons #x4008e7 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4008e8 #x8b) ;;  
   (cons #x4008e9 #x45) ;;  
   (cons #x4008ea #xe8) ;;  
   (cons #x4008eb #x48) ;; mov 0x68(%rax),%rdx 
   (cons #x4008ec #x8b) ;;  
   (cons #x4008ed #x50) ;;  
   (cons #x4008ee #x68) ;;  
   (cons #x4008ef #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4008f0 #x8b) ;;  
   (cons #x4008f1 #x45) ;;  
   (cons #x4008f2 #xe8) ;;  
   (cons #x4008f3 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x4008f4 #x8b) ;;  
   (cons #x4008f5 #x40) ;;  
   (cons #x4008f6 #x50) ;;  
   (cons #x4008f7 #x8b) ;; mov -0xc(%rbp),%ecx 
   (cons #x4008f8 #x4d) ;;  
   (cons #x4008f9 #xf4) ;;  
   (cons #x4008fa #x48) ;; movslq %ecx,%rcx 
   (cons #x4008fb #x63) ;;  
   (cons #x4008fc #xc9) ;;  
   (cons #x4008fd #x48) ;; shl $0x2,%rcx 
   (cons #x4008fe #xc1) ;;  
   (cons #x4008ff #xe1) ;;  
   (cons #x400900 #x02) ;;  
   (cons #x400901 #x48) ;; add %rcx,%rax 
   (cons #x400902 #x01) ;;  
   (cons #x400903 #xc8) ;;  
   (cons #x400904 #x8b) ;; mov (%rax),%eax 
   (cons #x400905 #x00) ;;  
   (cons #x400906 #x48) ;; cltq 
   (cons #x400907 #x98) ;;  
   (cons #x400908 #x48) ;; shl $0x2,%rax 
   (cons #x400909 #xc1) ;;  
   (cons #x40090a #xe0) ;;  
   (cons #x40090b #x02) ;;  
   (cons #x40090c #x48) ;; add %rdx,%rax 
   (cons #x40090d #x01) ;;  
   (cons #x40090e #xd0) ;;  
   (cons #x40090f #x8b) ;; mov (%rax),%eax 
   (cons #x400910 #x00) ;;  
   (cons #x400911 #x3b) ;; cmp -0x4(%rbp),%eax 
   (cons #x400912 #x45) ;;  
   (cons #x400913 #xfc) ;;  
   (cons #x400914 #x7c) ;; jl 400994 <heapRemoveTop+0x197> 
   (cons #x400915 #x7e) ;;  
   (cons #x400916 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400917 #x8b) ;;  
   (cons #x400918 #x45) ;;  
   (cons #x400919 #xe8) ;;  
   (cons #x40091a #x48) ;; mov 0x50(%rax),%rax 
   (cons #x40091b #x8b) ;;  
   (cons #x40091c #x40) ;;  
   (cons #x40091d #x50) ;;  
   (cons #x40091e #x8b) ;; mov -0x10(%rbp),%edx 
   (cons #x40091f #x55) ;;  
   (cons #x400920 #xf0) ;;  
   (cons #x400921 #x48) ;; movslq %edx,%rdx 
   (cons #x400922 #x63) ;;  
   (cons #x400923 #xd2) ;;  
   (cons #x400924 #x48) ;; shl $0x2,%rdx 
   (cons #x400925 #xc1) ;;  
   (cons #x400926 #xe2) ;;  
   (cons #x400927 #x02) ;;  
   (cons #x400928 #x48) ;; add %rax,%rdx 
   (cons #x400929 #x01) ;;  
   (cons #x40092a #xc2) ;;  
   (cons #x40092b #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40092c #x8b) ;;  
   (cons #x40092d #x45) ;;  
   (cons #x40092e #xe8) ;;  
   (cons #x40092f #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400930 #x8b) ;;  
   (cons #x400931 #x40) ;;  
   (cons #x400932 #x50) ;;  
   (cons #x400933 #x8b) ;; mov -0xc(%rbp),%ecx 
   (cons #x400934 #x4d) ;;  
   (cons #x400935 #xf4) ;;  
   (cons #x400936 #x48) ;; movslq %ecx,%rcx 
   (cons #x400937 #x63) ;;  
   (cons #x400938 #xc9) ;;  
   (cons #x400939 #x48) ;; shl $0x2,%rcx 
   (cons #x40093a #xc1) ;;  
   (cons #x40093b #xe1) ;;  
   (cons #x40093c #x02) ;;  
   (cons #x40093d #x48) ;; add %rcx,%rax 
   (cons #x40093e #x01) ;;  
   (cons #x40093f #xc8) ;;  
   (cons #x400940 #x8b) ;; mov (%rax),%eax 
   (cons #x400941 #x00) ;;  
   (cons #x400942 #x89) ;; mov %eax,(%rdx) 
   (cons #x400943 #x02) ;;  
   (cons #x400944 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400945 #x8b) ;;  
   (cons #x400946 #x45) ;;  
   (cons #x400947 #xe8) ;;  
   (cons #x400948 #x48) ;; mov 0x60(%rax),%rdx 
   (cons #x400949 #x8b) ;;  
   (cons #x40094a #x50) ;;  
   (cons #x40094b #x60) ;;  
   (cons #x40094c #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x40094d #x8b) ;;  
   (cons #x40094e #x45) ;;  
   (cons #x40094f #xe8) ;;  
   (cons #x400950 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400951 #x8b) ;;  
   (cons #x400952 #x40) ;;  
   (cons #x400953 #x50) ;;  
   (cons #x400954 #x8b) ;; mov -0xc(%rbp),%ecx 
   (cons #x400955 #x4d) ;;  
   (cons #x400956 #xf4) ;;  
   (cons #x400957 #x48) ;; movslq %ecx,%rcx 
   (cons #x400958 #x63) ;;  
   (cons #x400959 #xc9) ;;  
   (cons #x40095a #x48) ;; shl $0x2,%rcx 
   (cons #x40095b #xc1) ;;  
   (cons #x40095c #xe1) ;;  
   (cons #x40095d #x02) ;;  
   (cons #x40095e #x48) ;; add %rcx,%rax 
   (cons #x40095f #x01) ;;  
   (cons #x400960 #xc8) ;;  
   (cons #x400961 #x8b) ;; mov (%rax),%eax 
   (cons #x400962 #x00) ;;  
   (cons #x400963 #x48) ;; cltq 
   (cons #x400964 #x98) ;;  
   (cons #x400965 #x48) ;; shl $0x2,%rax 
   (cons #x400966 #xc1) ;;  
   (cons #x400967 #xe0) ;;  
   (cons #x400968 #x02) ;;  
   (cons #x400969 #x48) ;; add %rax,%rdx 
   (cons #x40096a #x01) ;;  
   (cons #x40096b #xc2) ;;  
   (cons #x40096c #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x40096d #x45) ;;  
   (cons #x40096e #xf0) ;;  
   (cons #x40096f #x89) ;; mov %eax,(%rdx) 
   (cons #x400970 #x02) ;;  
   (cons #x400971 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x400972 #x45) ;;  
   (cons #x400973 #xf4) ;;  
   (cons #x400974 #x89) ;; mov %eax,-0x10(%rbp) 
   (cons #x400975 #x45) ;;  
   (cons #x400976 #xf0) ;;  
   (cons #x400977 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x400978 #x45) ;;  
   (cons #x400979 #xf4) ;;  
   (cons #x40097a #x01) ;; add %eax,%eax 
   (cons #x40097b #xc0) ;;  
   (cons #x40097c #x83) ;; add $0x1,%eax 
   (cons #x40097d #xc0) ;;  
   (cons #x40097e #x01) ;;  
   (cons #x40097f #x89) ;; mov %eax,-0xc(%rbp) 
   (cons #x400980 #x45) ;;  
   (cons #x400981 #xf4) ;;  
   (cons #x400982 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400983 #x8b) ;;  
   (cons #x400984 #x45) ;;  
   (cons #x400985 #xe8) ;;  
   (cons #x400986 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x400987 #x40) ;;  
   (cons #x400988 #x58) ;;  
   (cons #x400989 #x3b) ;; cmp -0xc(%rbp),%eax 
   (cons #x40098a #x45) ;;  
   (cons #x40098b #xf4) ;;  
   (cons #x40098c #x0f) ;; jge 40087b <heapRemoveTop+0x7e> 
   (cons #x40098d #x8d) ;;  
   (cons #x40098e #xe9) ;;  
   (cons #x40098f #xfe) ;;  
   (cons #x400990 #xff) ;;  
   (cons #x400991 #xff) ;;  
   (cons #x400992 #xeb) ;; jmp 400995 <heapRemoveTop+0x198> 
   (cons #x400993 #x01) ;;  
   (cons #x400994 #x90) ;; nop 
   (cons #x400995 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400996 #x8b) ;;  
   (cons #x400997 #x45) ;;  
   (cons #x400998 #xe8) ;;  
   (cons #x400999 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x40099a #x8b) ;;  
   (cons #x40099b #x40) ;;  
   (cons #x40099c #x50) ;;  
   (cons #x40099d #x8b) ;; mov -0x10(%rbp),%edx 
   (cons #x40099e #x55) ;;  
   (cons #x40099f #xf0) ;;  
   (cons #x4009a0 #x48) ;; movslq %edx,%rdx 
   (cons #x4009a1 #x63) ;;  
   (cons #x4009a2 #xd2) ;;  
   (cons #x4009a3 #x48) ;; shl $0x2,%rdx 
   (cons #x4009a4 #xc1) ;;  
   (cons #x4009a5 #xe2) ;;  
   (cons #x4009a6 #x02) ;;  
   (cons #x4009a7 #x48) ;; add %rax,%rdx 
   (cons #x4009a8 #x01) ;;  
   (cons #x4009a9 #xc2) ;;  
   (cons #x4009aa #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x4009ab #x45) ;;  
   (cons #x4009ac #xf8) ;;  
   (cons #x4009ad #x89) ;; mov %eax,(%rdx) 
   (cons #x4009ae #x02) ;;  
   (cons #x4009af #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4009b0 #x8b) ;;  
   (cons #x4009b1 #x45) ;;  
   (cons #x4009b2 #xe8) ;;  
   (cons #x4009b3 #x48) ;; mov 0x60(%rax),%rax 
   (cons #x4009b4 #x8b) ;;  
   (cons #x4009b5 #x40) ;;  
   (cons #x4009b6 #x60) ;;  
   (cons #x4009b7 #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x4009b8 #x55) ;;  
   (cons #x4009b9 #xf8) ;;  
   (cons #x4009ba #x48) ;; movslq %edx,%rdx 
   (cons #x4009bb #x63) ;;  
   (cons #x4009bc #xd2) ;;  
   (cons #x4009bd #x48) ;; shl $0x2,%rdx 
   (cons #x4009be #xc1) ;;  
   (cons #x4009bf #xe2) ;;  
   (cons #x4009c0 #x02) ;;  
   (cons #x4009c1 #x48) ;; add %rax,%rdx 
   (cons #x4009c2 #x01) ;;  
   (cons #x4009c3 #xc2) ;;  
   (cons #x4009c4 #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x4009c5 #x45) ;;  
   (cons #x4009c6 #xf0) ;;  
   (cons #x4009c7 #x89) ;; mov %eax,(%rdx) 
   (cons #x4009c8 #x02) ;;  
   (cons #x4009c9 #x5d) ;; pop %rbp 
   (cons #x4009ca #xc3) ;; retq 
   
;; Section: <heapUp>:


   (cons #x4009cb #x55) ;; push %rbp 
   (cons #x4009cc #x48) ;; mov %rsp,%rbp 
   (cons #x4009cd #x89) ;;  
   (cons #x4009ce #xe5) ;;  
   (cons #x4009cf #x48) ;; mov %rdi,-0x18(%rbp) 
   (cons #x4009d0 #x89) ;;  
   (cons #x4009d1 #x7d) ;;  
   (cons #x4009d2 #xe8) ;;  
   (cons #x4009d3 #x89) ;; mov %esi,-0x1c(%rbp) 
   (cons #x4009d4 #x75) ;;  
   (cons #x4009d5 #xe4) ;;  
   (cons #x4009d6 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4009d7 #x8b) ;;  
   (cons #x4009d8 #x45) ;;  
   (cons #x4009d9 #xe8) ;;  
   (cons #x4009da #x48) ;; mov 0x68(%rax),%rax 
   (cons #x4009db #x8b) ;;  
   (cons #x4009dc #x40) ;;  
   (cons #x4009dd #x68) ;;  
   (cons #x4009de #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x4009df #x55) ;;  
   (cons #x4009e0 #xe4) ;;  
   (cons #x4009e1 #x48) ;; movslq %edx,%rdx 
   (cons #x4009e2 #x63) ;;  
   (cons #x4009e3 #xd2) ;;  
   (cons #x4009e4 #x48) ;; shl $0x2,%rdx 
   (cons #x4009e5 #xc1) ;;  
   (cons #x4009e6 #xe2) ;;  
   (cons #x4009e7 #x02) ;;  
   (cons #x4009e8 #x48) ;; add %rdx,%rax 
   (cons #x4009e9 #x01) ;;  
   (cons #x4009ea #xd0) ;;  
   (cons #x4009eb #x8b) ;; mov (%rax),%eax 
   (cons #x4009ec #x00) ;;  
   (cons #x4009ed #x89) ;; mov %eax,-0x4(%rbp) 
   (cons #x4009ee #x45) ;;  
   (cons #x4009ef #xfc) ;;  
   (cons #x4009f0 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x4009f1 #x8b) ;;  
   (cons #x4009f2 #x45) ;;  
   (cons #x4009f3 #xe8) ;;  
   (cons #x4009f4 #x48) ;; mov 0x60(%rax),%rax 
   (cons #x4009f5 #x8b) ;;  
   (cons #x4009f6 #x40) ;;  
   (cons #x4009f7 #x60) ;;  
   (cons #x4009f8 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x4009f9 #x55) ;;  
   (cons #x4009fa #xe4) ;;  
   (cons #x4009fb #x48) ;; movslq %edx,%rdx 
   (cons #x4009fc #x63) ;;  
   (cons #x4009fd #xd2) ;;  
   (cons #x4009fe #x48) ;; shl $0x2,%rdx 
   (cons #x4009ff #xc1) ;;  
   (cons #x400a00 #xe2) ;;  
   (cons #x400a01 #x02) ;;  
   (cons #x400a02 #x48) ;; add %rdx,%rax 
   (cons #x400a03 #x01) ;;  
   (cons #x400a04 #xd0) ;;  
   (cons #x400a05 #x8b) ;; mov (%rax),%eax 
   (cons #x400a06 #x00) ;;  
   (cons #x400a07 #x89) ;; mov %eax,-0x8(%rbp) 
   (cons #x400a08 #x45) ;;  
   (cons #x400a09 #xf8) ;;  
   (cons #x400a0a #xeb) ;; jmp 400a77 <heapUp+0xac> 
   (cons #x400a0b #x6b) ;;  
   (cons #x400a0c #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a0d #x8b) ;;  
   (cons #x400a0e #x45) ;;  
   (cons #x400a0f #xe8) ;;  
   (cons #x400a10 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400a11 #x8b) ;;  
   (cons #x400a12 #x40) ;;  
   (cons #x400a13 #x50) ;;  
   (cons #x400a14 #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x400a15 #x55) ;;  
   (cons #x400a16 #xf8) ;;  
   (cons #x400a17 #x48) ;; movslq %edx,%rdx 
   (cons #x400a18 #x63) ;;  
   (cons #x400a19 #xd2) ;;  
   (cons #x400a1a #x48) ;; shl $0x2,%rdx 
   (cons #x400a1b #xc1) ;;  
   (cons #x400a1c #xe2) ;;  
   (cons #x400a1d #x02) ;;  
   (cons #x400a1e #x48) ;; add %rax,%rdx 
   (cons #x400a1f #x01) ;;  
   (cons #x400a20 #xc2) ;;  
   (cons #x400a21 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a22 #x8b) ;;  
   (cons #x400a23 #x45) ;;  
   (cons #x400a24 #xe8) ;;  
   (cons #x400a25 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400a26 #x8b) ;;  
   (cons #x400a27 #x40) ;;  
   (cons #x400a28 #x50) ;;  
   (cons #x400a29 #x8b) ;; mov -0x8(%rbp),%ecx 
   (cons #x400a2a #x4d) ;;  
   (cons #x400a2b #xf8) ;;  
   (cons #x400a2c #x83) ;; sub $0x1,%ecx 
   (cons #x400a2d #xe9) ;;  
   (cons #x400a2e #x01) ;;  
   (cons #x400a2f #xd1) ;; sar %ecx 
   (cons #x400a30 #xf9) ;;  
   (cons #x400a31 #x48) ;; movslq %ecx,%rcx 
   (cons #x400a32 #x63) ;;  
   (cons #x400a33 #xc9) ;;  
   (cons #x400a34 #x48) ;; shl $0x2,%rcx 
   (cons #x400a35 #xc1) ;;  
   (cons #x400a36 #xe1) ;;  
   (cons #x400a37 #x02) ;;  
   (cons #x400a38 #x48) ;; add %rcx,%rax 
   (cons #x400a39 #x01) ;;  
   (cons #x400a3a #xc8) ;;  
   (cons #x400a3b #x8b) ;; mov (%rax),%eax 
   (cons #x400a3c #x00) ;;  
   (cons #x400a3d #x89) ;; mov %eax,(%rdx) 
   (cons #x400a3e #x02) ;;  
   (cons #x400a3f #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a40 #x8b) ;;  
   (cons #x400a41 #x45) ;;  
   (cons #x400a42 #xe8) ;;  
   (cons #x400a43 #x48) ;; mov 0x60(%rax),%rdx 
   (cons #x400a44 #x8b) ;;  
   (cons #x400a45 #x50) ;;  
   (cons #x400a46 #x60) ;;  
   (cons #x400a47 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a48 #x8b) ;;  
   (cons #x400a49 #x45) ;;  
   (cons #x400a4a #xe8) ;;  
   (cons #x400a4b #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400a4c #x8b) ;;  
   (cons #x400a4d #x40) ;;  
   (cons #x400a4e #x50) ;;  
   (cons #x400a4f #x8b) ;; mov -0x8(%rbp),%ecx 
   (cons #x400a50 #x4d) ;;  
   (cons #x400a51 #xf8) ;;  
   (cons #x400a52 #x48) ;; movslq %ecx,%rcx 
   (cons #x400a53 #x63) ;;  
   (cons #x400a54 #xc9) ;;  
   (cons #x400a55 #x48) ;; shl $0x2,%rcx 
   (cons #x400a56 #xc1) ;;  
   (cons #x400a57 #xe1) ;;  
   (cons #x400a58 #x02) ;;  
   (cons #x400a59 #x48) ;; add %rcx,%rax 
   (cons #x400a5a #x01) ;;  
   (cons #x400a5b #xc8) ;;  
   (cons #x400a5c #x8b) ;; mov (%rax),%eax 
   (cons #x400a5d #x00) ;;  
   (cons #x400a5e #x48) ;; cltq 
   (cons #x400a5f #x98) ;;  
   (cons #x400a60 #x48) ;; shl $0x2,%rax 
   (cons #x400a61 #xc1) ;;  
   (cons #x400a62 #xe0) ;;  
   (cons #x400a63 #x02) ;;  
   (cons #x400a64 #x48) ;; add %rax,%rdx 
   (cons #x400a65 #x01) ;;  
   (cons #x400a66 #xc2) ;;  
   (cons #x400a67 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x400a68 #x45) ;;  
   (cons #x400a69 #xf8) ;;  
   (cons #x400a6a #x89) ;; mov %eax,(%rdx) 
   (cons #x400a6b #x02) ;;  
   (cons #x400a6c #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x400a6d #x45) ;;  
   (cons #x400a6e #xf8) ;;  
   (cons #x400a6f #x83) ;; sub $0x1,%eax 
   (cons #x400a70 #xe8) ;;  
   (cons #x400a71 #x01) ;;  
   (cons #x400a72 #xd1) ;; sar %eax 
   (cons #x400a73 #xf8) ;;  
   (cons #x400a74 #x89) ;; mov %eax,-0x8(%rbp) 
   (cons #x400a75 #x45) ;;  
   (cons #x400a76 #xf8) ;;  
   (cons #x400a77 #x83) ;; cmpl $0x0,-0x8(%rbp) 
   (cons #x400a78 #x7d) ;;  
   (cons #x400a79 #xf8) ;;  
   (cons #x400a7a #x00) ;;  
   (cons #x400a7b #x74) ;; je 400ab5 <heapUp+0xea> 
   (cons #x400a7c #x38) ;;  
   (cons #x400a7d #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a7e #x8b) ;;  
   (cons #x400a7f #x45) ;;  
   (cons #x400a80 #xe8) ;;  
   (cons #x400a81 #x48) ;; mov 0x68(%rax),%rdx 
   (cons #x400a82 #x8b) ;;  
   (cons #x400a83 #x50) ;;  
   (cons #x400a84 #x68) ;;  
   (cons #x400a85 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400a86 #x8b) ;;  
   (cons #x400a87 #x45) ;;  
   (cons #x400a88 #xe8) ;;  
   (cons #x400a89 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400a8a #x8b) ;;  
   (cons #x400a8b #x40) ;;  
   (cons #x400a8c #x50) ;;  
   (cons #x400a8d #x8b) ;; mov -0x8(%rbp),%ecx 
   (cons #x400a8e #x4d) ;;  
   (cons #x400a8f #xf8) ;;  
   (cons #x400a90 #x83) ;; sub $0x1,%ecx 
   (cons #x400a91 #xe9) ;;  
   (cons #x400a92 #x01) ;;  
   (cons #x400a93 #xd1) ;; sar %ecx 
   (cons #x400a94 #xf9) ;;  
   (cons #x400a95 #x48) ;; movslq %ecx,%rcx 
   (cons #x400a96 #x63) ;;  
   (cons #x400a97 #xc9) ;;  
   (cons #x400a98 #x48) ;; shl $0x2,%rcx 
   (cons #x400a99 #xc1) ;;  
   (cons #x400a9a #xe1) ;;  
   (cons #x400a9b #x02) ;;  
   (cons #x400a9c #x48) ;; add %rcx,%rax 
   (cons #x400a9d #x01) ;;  
   (cons #x400a9e #xc8) ;;  
   (cons #x400a9f #x8b) ;; mov (%rax),%eax 
   (cons #x400aa0 #x00) ;;  
   (cons #x400aa1 #x48) ;; cltq 
   (cons #x400aa2 #x98) ;;  
   (cons #x400aa3 #x48) ;; shl $0x2,%rax 
   (cons #x400aa4 #xc1) ;;  
   (cons #x400aa5 #xe0) ;;  
   (cons #x400aa6 #x02) ;;  
   (cons #x400aa7 #x48) ;; add %rdx,%rax 
   (cons #x400aa8 #x01) ;;  
   (cons #x400aa9 #xd0) ;;  
   (cons #x400aaa #x8b) ;; mov (%rax),%eax 
   (cons #x400aab #x00) ;;  
   (cons #x400aac #x3b) ;; cmp -0x4(%rbp),%eax 
   (cons #x400aad #x45) ;;  
   (cons #x400aae #xfc) ;;  
   (cons #x400aaf #x0f) ;; jl 400a0c <heapUp+0x41> 
   (cons #x400ab0 #x8c) ;;  
   (cons #x400ab1 #x57) ;;  
   (cons #x400ab2 #xff) ;;  
   (cons #x400ab3 #xff) ;;  
   (cons #x400ab4 #xff) ;;  
   (cons #x400ab5 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400ab6 #x8b) ;;  
   (cons #x400ab7 #x45) ;;  
   (cons #x400ab8 #xe8) ;;  
   (cons #x400ab9 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x400aba #x8b) ;;  
   (cons #x400abb #x40) ;;  
   (cons #x400abc #x50) ;;  
   (cons #x400abd #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x400abe #x55) ;;  
   (cons #x400abf #xf8) ;;  
   (cons #x400ac0 #x48) ;; movslq %edx,%rdx 
   (cons #x400ac1 #x63) ;;  
   (cons #x400ac2 #xd2) ;;  
   (cons #x400ac3 #x48) ;; shl $0x2,%rdx 
   (cons #x400ac4 #xc1) ;;  
   (cons #x400ac5 #xe2) ;;  
   (cons #x400ac6 #x02) ;;  
   (cons #x400ac7 #x48) ;; add %rax,%rdx 
   (cons #x400ac8 #x01) ;;  
   (cons #x400ac9 #xc2) ;;  
   (cons #x400aca #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x400acb #x45) ;;  
   (cons #x400acc #xe4) ;;  
   (cons #x400acd #x89) ;; mov %eax,(%rdx) 
   (cons #x400ace #x02) ;;  
   (cons #x400acf #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400ad0 #x8b) ;;  
   (cons #x400ad1 #x45) ;;  
   (cons #x400ad2 #xe8) ;;  
   (cons #x400ad3 #x48) ;; mov 0x60(%rax),%rax 
   (cons #x400ad4 #x8b) ;;  
   (cons #x400ad5 #x40) ;;  
   (cons #x400ad6 #x60) ;;  
   (cons #x400ad7 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x400ad8 #x55) ;;  
   (cons #x400ad9 #xe4) ;;  
   (cons #x400ada #x48) ;; movslq %edx,%rdx 
   (cons #x400adb #x63) ;;  
   (cons #x400adc #xd2) ;;  
   (cons #x400add #x48) ;; shl $0x2,%rdx 
   (cons #x400ade #xc1) ;;  
   (cons #x400adf #xe2) ;;  
   (cons #x400ae0 #x02) ;;  
   (cons #x400ae1 #x48) ;; add %rax,%rdx 
   (cons #x400ae2 #x01) ;;  
   (cons #x400ae3 #xc2) ;;  
   (cons #x400ae4 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x400ae5 #x45) ;;  
   (cons #x400ae6 #xf8) ;;  
   (cons #x400ae7 #x89) ;; mov %eax,(%rdx) 
   (cons #x400ae8 #x02) ;;  
   (cons #x400ae9 #x5d) ;; pop %rbp 
   (cons #x400aea #xc3) ;; retq 
   
;; Section: <implied>:


   (cons #x400aeb #x55) ;; push %rbp 
   (cons #x400aec #x48) ;; mov %rsp,%rbp 
   (cons #x400aed #x89) ;;  
   (cons #x400aee #xe5) ;;  
   (cons #x400aef #x48) ;; sub $0x20,%rsp 
   (cons #x400af0 #x83) ;;  
   (cons #x400af1 #xec) ;;  
   (cons #x400af2 #x20) ;;  
   (cons #x400af3 #x48) ;; mov %rdi,-0x18(%rbp) 
   (cons #x400af4 #x89) ;;  
   (cons #x400af5 #x7d) ;;  
   (cons #x400af6 #xe8) ;;  
   (cons #x400af7 #x89) ;; mov %esi,-0x1c(%rbp) 
   (cons #x400af8 #x75) ;;  
   (cons #x400af9 #xe4) ;;  
   (cons #x400afa #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400afb #x8b) ;;  
   (cons #x400afc #x45) ;;  
   (cons #x400afd #xe8) ;;  
   (cons #x400afe #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400aff #x8b) ;;  
   (cons #x400b00 #x40) ;;  
   (cons #x400b01 #x40) ;;  
   (cons #x400b02 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x400b03 #x55) ;;  
   (cons #x400b04 #xe4) ;;  
   (cons #x400b05 #x48) ;; movslq %edx,%rdx 
   (cons #x400b06 #x63) ;;  
   (cons #x400b07 #xd2) ;;  
   (cons #x400b08 #x48) ;; shl $0x2,%rdx 
   (cons #x400b09 #xc1) ;;  
   (cons #x400b0a #xe2) ;;  
   (cons #x400b0b #x02) ;;  
   (cons #x400b0c #x48) ;; add %rdx,%rax 
   (cons #x400b0d #x01) ;;  
   (cons #x400b0e #xd0) ;;  
   (cons #x400b0f #x8b) ;; mov (%rax),%eax 
   (cons #x400b10 #x00) ;;  
   (cons #x400b11 #x83) ;; cmp $0x2,%eax 
   (cons #x400b12 #xf8) ;;  
   (cons #x400b13 #x02) ;;  
   (cons #x400b14 #x7e) ;; jle 400b35 <implied+0x4a> 
   (cons #x400b15 #x1f) ;;  
   (cons #x400b16 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400b17 #x8b) ;;  
   (cons #x400b18 #x45) ;;  
   (cons #x400b19 #xe8) ;;  
   (cons #x400b1a #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400b1b #x8b) ;;  
   (cons #x400b1c #x40) ;;  
   (cons #x400b1d #x40) ;;  
   (cons #x400b1e #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x400b1f #x55) ;;  
   (cons #x400b20 #xe4) ;;  
   (cons #x400b21 #x48) ;; movslq %edx,%rdx 
   (cons #x400b22 #x63) ;;  
   (cons #x400b23 #xd2) ;;  
   (cons #x400b24 #x48) ;; shl $0x2,%rdx 
   (cons #x400b25 #xc1) ;;  
   (cons #x400b26 #xe2) ;;  
   (cons #x400b27 #x02) ;;  
   (cons #x400b28 #x48) ;; add %rdx,%rax 
   (cons #x400b29 #x01) ;;  
   (cons #x400b2a #xd0) ;;  
   (cons #x400b2b #x8b) ;; mov (%rax),%eax 
   (cons #x400b2c #x00) ;;  
   (cons #x400b2d #x83) ;; and $0x2,%eax 
   (cons #x400b2e #xe0) ;;  
   (cons #x400b2f #x02) ;;  
   (cons #x400b30 #xe9) ;; jmpq 400c28 <implied+0x13d> 
   (cons #x400b31 #xf3) ;;  
   (cons #x400b32 #x00) ;;  
   (cons #x400b33 #x00) ;;  
   (cons #x400b34 #x00) ;;  
   (cons #x400b35 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400b36 #x8b) ;;  
   (cons #x400b37 #x45) ;;  
   (cons #x400b38 #xe8) ;;  
   (cons #x400b39 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x400b3a #x8b) ;;  
   (cons #x400b3b #x48) ;;  
   (cons #x400b3c #x30) ;;  
   (cons #x400b3d #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x400b3e #x45) ;;  
   (cons #x400b3f #xe4) ;;  
   (cons #x400b40 #x89) ;; mov %eax,%edx 
   (cons #x400b41 #xc2) ;;  
   (cons #x400b42 #xc1) ;; sar $0x1f,%edx 
   (cons #x400b43 #xfa) ;;  
   (cons #x400b44 #x1f) ;;  
   (cons #x400b45 #x89) ;; mov %edx,%eax 
   (cons #x400b46 #xd0) ;;  
   (cons #x400b47 #x33) ;; xor -0x1c(%rbp),%eax 
   (cons #x400b48 #x45) ;;  
   (cons #x400b49 #xe4) ;;  
   (cons #x400b4a #x29) ;; sub %edx,%eax 
   (cons #x400b4b #xd0) ;;  
   (cons #x400b4c #x48) ;; cltq 
   (cons #x400b4d #x98) ;;  
   (cons #x400b4e #x48) ;; shl $0x2,%rax 
   (cons #x400b4f #xc1) ;;  
   (cons #x400b50 #xe0) ;;  
   (cons #x400b51 #x02) ;;  
   (cons #x400b52 #x48) ;; add %rcx,%rax 
   (cons #x400b53 #x01) ;;  
   (cons #x400b54 #xc8) ;;  
   (cons #x400b55 #x8b) ;; mov (%rax),%eax 
   (cons #x400b56 #x00) ;;  
   (cons #x400b57 #x85) ;; test %eax,%eax 
   (cons #x400b58 #xc0) ;;  
   (cons #x400b59 #x75) ;; jne 400b65 <implied+0x7a> 
   (cons #x400b5a #x0a) ;;  
   (cons #x400b5b #xb8) ;; mov $0x0,%eax 
   (cons #x400b5c #x00) ;;  
   (cons #x400b5d #x00) ;;  
   (cons #x400b5e #x00) ;;  
   (cons #x400b5f #x00) ;;  
   (cons #x400b60 #xe9) ;; jmpq 400c28 <implied+0x13d> 
   (cons #x400b61 #xc3) ;;  
   (cons #x400b62 #x00) ;;  
   (cons #x400b63 #x00) ;;  
   (cons #x400b64 #x00) ;;  
   (cons #x400b65 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400b66 #x8b) ;;  
   (cons #x400b67 #x45) ;;  
   (cons #x400b68 #xe8) ;;  
   (cons #x400b69 #x48) ;; mov (%rax),%rcx 
   (cons #x400b6a #x8b) ;;  
   (cons #x400b6b #x08) ;;  
   (cons #x400b6c #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400b6d #x8b) ;;  
   (cons #x400b6e #x45) ;;  
   (cons #x400b6f #xe8) ;;  
   (cons #x400b70 #x48) ;; mov 0x30(%rax),%rsi 
   (cons #x400b71 #x8b) ;;  
   (cons #x400b72 #x70) ;;  
   (cons #x400b73 #x30) ;;  
   (cons #x400b74 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x400b75 #x45) ;;  
   (cons #x400b76 #xe4) ;;  
   (cons #x400b77 #x89) ;; mov %eax,%edx 
   (cons #x400b78 #xc2) ;;  
   (cons #x400b79 #xc1) ;; sar $0x1f,%edx 
   (cons #x400b7a #xfa) ;;  
   (cons #x400b7b #x1f) ;;  
   (cons #x400b7c #x89) ;; mov %edx,%eax 
   (cons #x400b7d #xd0) ;;  
   (cons #x400b7e #x33) ;; xor -0x1c(%rbp),%eax 
   (cons #x400b7f #x45) ;;  
   (cons #x400b80 #xe4) ;;  
   (cons #x400b81 #x29) ;; sub %edx,%eax 
   (cons #x400b82 #xd0) ;;  
   (cons #x400b83 #x48) ;; cltq 
   (cons #x400b84 #x98) ;;  
   (cons #x400b85 #x48) ;; shl $0x2,%rax 
   (cons #x400b86 #xc1) ;;  
   (cons #x400b87 #xe0) ;;  
   (cons #x400b88 #x02) ;;  
   (cons #x400b89 #x48) ;; add %rsi,%rax 
   (cons #x400b8a #x01) ;;  
   (cons #x400b8b #xf0) ;;  
   (cons #x400b8c #x8b) ;; mov (%rax),%eax 
   (cons #x400b8d #x00) ;;  
   (cons #x400b8e #x48) ;; cltq 
   (cons #x400b8f #x98) ;;  
   (cons #x400b90 #x48) ;; sub $0x1,%rax 
   (cons #x400b91 #x83) ;;  
   (cons #x400b92 #xe8) ;;  
   (cons #x400b93 #x01) ;;  
   (cons #x400b94 #x48) ;; shl $0x2,%rax 
   (cons #x400b95 #xc1) ;;  
   (cons #x400b96 #xe0) ;;  
   (cons #x400b97 #x02) ;;  
   (cons #x400b98 #x48) ;; add %rcx,%rax 
   (cons #x400b99 #x01) ;;  
   (cons #x400b9a #xc8) ;;  
   (cons #x400b9b #x48) ;; mov %rax,-0x8(%rbp) 
   (cons #x400b9c #x89) ;;  
   (cons #x400b9d #x45) ;;  
   (cons #x400b9e #xf8) ;;  
   (cons #x400b9f #xeb) ;; jmp 400bf9 <implied+0x10e> 
   (cons #x400ba0 #x58) ;;  
   (cons #x400ba1 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400ba2 #x8b) ;;  
   (cons #x400ba3 #x45) ;;  
   (cons #x400ba4 #xe8) ;;  
   (cons #x400ba5 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x400ba6 #x8b) ;;  
   (cons #x400ba7 #x50) ;;  
   (cons #x400ba8 #x40) ;;  
   (cons #x400ba9 #x48) ;; mov -0x8(%rbp),%rax 
   (cons #x400baa #x8b) ;;  
   (cons #x400bab #x45) ;;  
   (cons #x400bac #xf8) ;;  
   (cons #x400bad #x8b) ;; mov (%rax),%eax 
   (cons #x400bae #x00) ;;  
   (cons #x400baf #x48) ;; cltq 
   (cons #x400bb0 #x98) ;;  
   (cons #x400bb1 #x48) ;; shl $0x2,%rax 
   (cons #x400bb2 #xc1) ;;  
   (cons #x400bb3 #xe0) ;;  
   (cons #x400bb4 #x02) ;;  
   (cons #x400bb5 #x48) ;; add %rdx,%rax 
   (cons #x400bb6 #x01) ;;  
   (cons #x400bb7 #xd0) ;;  
   (cons #x400bb8 #x8b) ;; mov (%rax),%eax 
   (cons #x400bb9 #x00) ;;  
   (cons #x400bba #x83) ;; cmp $0x2,%eax 
   (cons #x400bbb #xf8) ;;  
   (cons #x400bbc #x02) ;;  
   (cons #x400bbd #x74) ;; je 400bf9 <implied+0x10e> 
   (cons #x400bbe #x3a) ;;  
   (cons #x400bbf #x48) ;; mov -0x8(%rbp),%rax 
   (cons #x400bc0 #x8b) ;;  
   (cons #x400bc1 #x45) ;;  
   (cons #x400bc2 #xf8) ;;  
   (cons #x400bc3 #x8b) ;; mov (%rax),%edx 
   (cons #x400bc4 #x10) ;;  
   (cons #x400bc5 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400bc6 #x8b) ;;  
   (cons #x400bc7 #x45) ;;  
   (cons #x400bc8 #xe8) ;;  
   (cons #x400bc9 #x89) ;; mov %edx,%esi 
   (cons #x400bca #xd6) ;;  
   (cons #x400bcb #x48) ;; mov %rax,%rdi 
   (cons #x400bcc #x89) ;;  
   (cons #x400bcd #xc7) ;;  
   (cons #x400bce #xe8) ;; callq 400aeb <implied> 
   (cons #x400bcf #x18) ;;  
   (cons #x400bd0 #xff) ;;  
   (cons #x400bd1 #xff) ;;  
   (cons #x400bd2 #xff) ;;  
   (cons #x400bd3 #x85) ;; test %eax,%eax 
   (cons #x400bd4 #xc0) ;;  
   (cons #x400bd5 #x75) ;; jne 400bf9 <implied+0x10e> 
   (cons #x400bd6 #x22) ;;  
   (cons #x400bd7 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400bd8 #x8b) ;;  
   (cons #x400bd9 #x45) ;;  
   (cons #x400bda #xe8) ;;  
   (cons #x400bdb #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400bdc #x8b) ;;  
   (cons #x400bdd #x40) ;;  
   (cons #x400bde #x40) ;;  
   (cons #x400bdf #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x400be0 #x55) ;;  
   (cons #x400be1 #xe4) ;;  
   (cons #x400be2 #x48) ;; movslq %edx,%rdx 
   (cons #x400be3 #x63) ;;  
   (cons #x400be4 #xd2) ;;  
   (cons #x400be5 #x48) ;; shl $0x2,%rdx 
   (cons #x400be6 #xc1) ;;  
   (cons #x400be7 #xe2) ;;  
   (cons #x400be8 #x02) ;;  
   (cons #x400be9 #x48) ;; add %rdx,%rax 
   (cons #x400bea #x01) ;;  
   (cons #x400beb #xd0) ;;  
   (cons #x400bec #xc7) ;; movl $0x5,(%rax) 
   (cons #x400bed #x00) ;;  
   (cons #x400bee #x05) ;;  
   (cons #x400bef #x00) ;;  
   (cons #x400bf0 #x00) ;;  
   (cons #x400bf1 #x00) ;;  
   (cons #x400bf2 #xb8) ;; mov $0x0,%eax 
   (cons #x400bf3 #x00) ;;  
   (cons #x400bf4 #x00) ;;  
   (cons #x400bf5 #x00) ;;  
   (cons #x400bf6 #x00) ;;  
   (cons #x400bf7 #xeb) ;; jmp 400c28 <implied+0x13d> 
   (cons #x400bf8 #x2f) ;;  
   (cons #x400bf9 #x48) ;; addq $0x4,-0x8(%rbp) 
   (cons #x400bfa #x83) ;;  
   (cons #x400bfb #x45) ;;  
   (cons #x400bfc #xf8) ;;  
   (cons #x400bfd #x04) ;;  
   (cons #x400bfe #x48) ;; mov -0x8(%rbp),%rax 
   (cons #x400bff #x8b) ;;  
   (cons #x400c00 #x45) ;;  
   (cons #x400c01 #xf8) ;;  
   (cons #x400c02 #x8b) ;; mov (%rax),%eax 
   (cons #x400c03 #x00) ;;  
   (cons #x400c04 #x85) ;; test %eax,%eax 
   (cons #x400c05 #xc0) ;;  
   (cons #x400c06 #x75) ;; jne 400ba1 <implied+0xb6> 
   (cons #x400c07 #x99) ;;  
   (cons #x400c08 #x48) ;; mov -0x18(%rbp),%rax 
   (cons #x400c09 #x8b) ;;  
   (cons #x400c0a #x45) ;;  
   (cons #x400c0b #xe8) ;;  
   (cons #x400c0c #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400c0d #x8b) ;;  
   (cons #x400c0e #x40) ;;  
   (cons #x400c0f #x40) ;;  
   (cons #x400c10 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x400c11 #x55) ;;  
   (cons #x400c12 #xe4) ;;  
   (cons #x400c13 #x48) ;; movslq %edx,%rdx 
   (cons #x400c14 #x63) ;;  
   (cons #x400c15 #xd2) ;;  
   (cons #x400c16 #x48) ;; shl $0x2,%rdx 
   (cons #x400c17 #xc1) ;;  
   (cons #x400c18 #xe2) ;;  
   (cons #x400c19 #x02) ;;  
   (cons #x400c1a #x48) ;; add %rdx,%rax 
   (cons #x400c1b #x01) ;;  
   (cons #x400c1c #xd0) ;;  
   (cons #x400c1d #xc7) ;; movl $0x6,(%rax) 
   (cons #x400c1e #x00) ;;  
   (cons #x400c1f #x06) ;;  
   (cons #x400c20 #x00) ;;  
   (cons #x400c21 #x00) ;;  
   (cons #x400c22 #x00) ;;  
   (cons #x400c23 #xb8) ;; mov $0x1,%eax 
   (cons #x400c24 #x01) ;;  
   (cons #x400c25 #x00) ;;  
   (cons #x400c26 #x00) ;;  
   (cons #x400c27 #x00) ;;  
   (cons #x400c28 #xc9) ;; leaveq 
   (cons #x400c29 #xc3) ;; retq 
   
;; Section: <analyze>:


   (cons #x400c2a #x55) ;; push %rbp 
   (cons #x400c2b #x48) ;; mov %rsp,%rbp 
   (cons #x400c2c #x89) ;;  
   (cons #x400c2d #xe5) ;;  
   (cons #x400c2e #x48) ;; sub $0x50,%rsp 
   (cons #x400c2f #x83) ;;  
   (cons #x400c30 #xec) ;;  
   (cons #x400c31 #x50) ;;  
   (cons #x400c32 #x48) ;; mov %rdi,-0x48(%rbp) 
   (cons #x400c33 #x89) ;;  
   (cons #x400c34 #x7d) ;;  
   (cons #x400c35 #xb8) ;;  
   (cons #x400c36 #x48) ;; mov %rsi,-0x50(%rbp) 
   (cons #x400c37 #x89) ;;  
   (cons #x400c38 #x75) ;;  
   (cons #x400c39 #xb0) ;;  
   (cons #x400c3a #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c3b #x8b) ;;  
   (cons #x400c3c #x45) ;;  
   (cons #x400c3d #xb8) ;;  
   (cons #x400c3e #x8b) ;; mov 0x1c(%rax),%eax 
   (cons #x400c3f #x40) ;;  
   (cons #x400c40 #x1c) ;;  
   (cons #x400c41 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x400c42 #x50) ;;  
   (cons #x400c43 #x01) ;;  
   (cons #x400c44 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c45 #x8b) ;;  
   (cons #x400c46 #x45) ;;  
   (cons #x400c47 #xb8) ;;  
   (cons #x400c48 #x89) ;; mov %edx,0x1c(%rax) 
   (cons #x400c49 #x50) ;;  
   (cons #x400c4a #x1c) ;;  
   (cons #x400c4b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c4c #x8b) ;;  
   (cons #x400c4d #x45) ;;  
   (cons #x400c4e #xb8) ;;  
   (cons #x400c4f #x8b) ;; mov 0x20(%rax),%eax 
   (cons #x400c50 #x40) ;;  
   (cons #x400c51 #x20) ;;  
   (cons #x400c52 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x400c53 #x50) ;;  
   (cons #x400c54 #x01) ;;  
   (cons #x400c55 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c56 #x8b) ;;  
   (cons #x400c57 #x45) ;;  
   (cons #x400c58 #xb8) ;;  
   (cons #x400c59 #x89) ;; mov %edx,0x20(%rax) 
   (cons #x400c5a #x50) ;;  
   (cons #x400c5b #x20) ;;  
   (cons #x400c5c #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c5d #x8b) ;;  
   (cons #x400c5e #x45) ;;  
   (cons #x400c5f #xb8) ;;  
   (cons #x400c60 #x8b) ;; mov 0x24(%rax),%eax 
   (cons #x400c61 #x40) ;;  
   (cons #x400c62 #x24) ;;  
   (cons #x400c63 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x400c64 #x50) ;;  
   (cons #x400c65 #x01) ;;  
   (cons #x400c66 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c67 #x8b) ;;  
   (cons #x400c68 #x45) ;;  
   (cons #x400c69 #xb8) ;;  
   (cons #x400c6a #x89) ;; mov %edx,0x24(%rax) 
   (cons #x400c6b #x50) ;;  
   (cons #x400c6c #x24) ;;  
   (cons #x400c6d #xe9) ;; jmpq 400d58 <analyze+0x12e> 
   (cons #x400c6e #xe6) ;;  
   (cons #x400c6f #x00) ;;  
   (cons #x400c70 #x00) ;;  
   (cons #x400c71 #x00) ;;  
   (cons #x400c72 #x48) ;; mov -0x50(%rbp),%rax 
   (cons #x400c73 #x8b) ;;  
   (cons #x400c74 #x45) ;;  
   (cons #x400c75 #xb0) ;;  
   (cons #x400c76 #x8b) ;; mov (%rax),%eax 
   (cons #x400c77 #x00) ;;  
   (cons #x400c78 #x89) ;; mov %eax,-0x14(%rbp) 
   (cons #x400c79 #x45) ;;  
   (cons #x400c7a #xec) ;;  
   (cons #x400c7b #x48) ;; addq $0x4,-0x50(%rbp) 
   (cons #x400c7c #x83) ;;  
   (cons #x400c7d #x45) ;;  
   (cons #x400c7e #xb0) ;;  
   (cons #x400c7f #x04) ;;  
   (cons #x400c80 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400c81 #x8b) ;;  
   (cons #x400c82 #x45) ;;  
   (cons #x400c83 #xb8) ;;  
   (cons #x400c84 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400c85 #x8b) ;;  
   (cons #x400c86 #x40) ;;  
   (cons #x400c87 #x40) ;;  
   (cons #x400c88 #x8b) ;; mov -0x14(%rbp),%edx 
   (cons #x400c89 #x55) ;;  
   (cons #x400c8a #xec) ;;  
   (cons #x400c8b #x48) ;; movslq %edx,%rdx 
   (cons #x400c8c #x63) ;;  
   (cons #x400c8d #xd2) ;;  
   (cons #x400c8e #x48) ;; shl $0x2,%rdx 
   (cons #x400c8f #xc1) ;;  
   (cons #x400c90 #xe2) ;;  
   (cons #x400c91 #x02) ;;  
   (cons #x400c92 #x48) ;; add %rdx,%rax 
   (cons #x400c93 #x01) ;;  
   (cons #x400c94 #xd0) ;;  
   (cons #x400c95 #x8b) ;; mov (%rax),%eax 
   (cons #x400c96 #x00) ;;  
   (cons #x400c97 #x83) ;; cmp $0x2,%eax 
   (cons #x400c98 #xf8) ;;  
   (cons #x400c99 #x02) ;;  
   (cons #x400c9a #x0f) ;; je 400d3d <analyze+0x113> 
   (cons #x400c9b #x84) ;;  
   (cons #x400c9c #x9d) ;;  
   (cons #x400c9d #x00) ;;  
   (cons #x400c9e #x00) ;;  
   (cons #x400c9f #x00) ;;  
   (cons #x400ca0 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400ca1 #x8b) ;;  
   (cons #x400ca2 #x45) ;;  
   (cons #x400ca3 #xb8) ;;  
   (cons #x400ca4 #x48) ;; mov 0x68(%rax),%rcx 
   (cons #x400ca5 #x8b) ;;  
   (cons #x400ca6 #x48) ;;  
   (cons #x400ca7 #x68) ;;  
   (cons #x400ca8 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x400ca9 #x45) ;;  
   (cons #x400caa #xec) ;;  
   (cons #x400cab #x89) ;; mov %eax,%edx 
   (cons #x400cac #xc2) ;;  
   (cons #x400cad #xc1) ;; sar $0x1f,%edx 
   (cons #x400cae #xfa) ;;  
   (cons #x400caf #x1f) ;;  
   (cons #x400cb0 #x89) ;; mov %edx,%eax 
   (cons #x400cb1 #xd0) ;;  
   (cons #x400cb2 #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x400cb3 #x45) ;;  
   (cons #x400cb4 #xec) ;;  
   (cons #x400cb5 #x29) ;; sub %edx,%eax 
   (cons #x400cb6 #xd0) ;;  
   (cons #x400cb7 #x48) ;; cltq 
   (cons #x400cb8 #x98) ;;  
   (cons #x400cb9 #x48) ;; shl $0x2,%rax 
   (cons #x400cba #xc1) ;;  
   (cons #x400cbb #xe0) ;;  
   (cons #x400cbc #x02) ;;  
   (cons #x400cbd #x48) ;; add %rax,%rcx 
   (cons #x400cbe #x01) ;;  
   (cons #x400cbf #xc1) ;;  
   (cons #x400cc0 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400cc1 #x8b) ;;  
   (cons #x400cc2 #x45) ;;  
   (cons #x400cc3 #xb8) ;;  
   (cons #x400cc4 #x48) ;; mov 0x68(%rax),%rsi 
   (cons #x400cc5 #x8b) ;;  
   (cons #x400cc6 #x70) ;;  
   (cons #x400cc7 #x68) ;;  
   (cons #x400cc8 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x400cc9 #x45) ;;  
   (cons #x400cca #xec) ;;  
   (cons #x400ccb #x89) ;; mov %eax,%edx 
   (cons #x400ccc #xc2) ;;  
   (cons #x400ccd #xc1) ;; sar $0x1f,%edx 
   (cons #x400cce #xfa) ;;  
   (cons #x400ccf #x1f) ;;  
   (cons #x400cd0 #x89) ;; mov %edx,%eax 
   (cons #x400cd1 #xd0) ;;  
   (cons #x400cd2 #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x400cd3 #x45) ;;  
   (cons #x400cd4 #xec) ;;  
   (cons #x400cd5 #x29) ;; sub %edx,%eax 
   (cons #x400cd6 #xd0) ;;  
   (cons #x400cd7 #x48) ;; cltq 
   (cons #x400cd8 #x98) ;;  
   (cons #x400cd9 #x48) ;; shl $0x2,%rax 
   (cons #x400cda #xc1) ;;  
   (cons #x400cdb #xe0) ;;  
   (cons #x400cdc #x02) ;;  
   (cons #x400cdd #x48) ;; add %rsi,%rax 
   (cons #x400cde #x01) ;;  
   (cons #x400cdf #xf0) ;;  
   (cons #x400ce0 #x8b) ;; mov (%rax),%edx 
   (cons #x400ce1 #x10) ;;  
   (cons #x400ce2 #x89) ;; mov %edx,%eax 
   (cons #x400ce3 #xd0) ;;  
   (cons #x400ce4 #x01) ;; add %eax,%eax 
   (cons #x400ce5 #xc0) ;;  
   (cons #x400ce6 #x01) ;; add %eax,%edx 
   (cons #x400ce7 #xc2) ;;  
   (cons #x400ce8 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400ce9 #x8b) ;;  
   (cons #x400cea #x45) ;;  
   (cons #x400ceb #xb8) ;;  
   (cons #x400cec #x8b) ;; mov 0x24(%rax),%eax 
   (cons #x400ced #x40) ;;  
   (cons #x400cee #x24) ;;  
   (cons #x400cef #xc1) ;; shl $0x5,%eax 
   (cons #x400cf0 #xe0) ;;  
   (cons #x400cf1 #x05) ;;  
   (cons #x400cf2 #x01) ;; add %edx,%eax 
   (cons #x400cf3 #xd0) ;;  
   (cons #x400cf4 #xc1) ;; sar $0x2,%eax 
   (cons #x400cf5 #xf8) ;;  
   (cons #x400cf6 #x02) ;;  
   (cons #x400cf7 #x89) ;; mov %eax,(%rcx) 
   (cons #x400cf8 #x01) ;;  
   (cons #x400cf9 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400cfa #x8b) ;;  
   (cons #x400cfb #x45) ;;  
   (cons #x400cfc #xb8) ;;  
   (cons #x400cfd #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x400cfe #x8b) ;;  
   (cons #x400cff #x48) ;;  
   (cons #x400d00 #x60) ;;  
   (cons #x400d01 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x400d02 #x45) ;;  
   (cons #x400d03 #xec) ;;  
   (cons #x400d04 #x89) ;; mov %eax,%edx 
   (cons #x400d05 #xc2) ;;  
   (cons #x400d06 #xc1) ;; sar $0x1f,%edx 
   (cons #x400d07 #xfa) ;;  
   (cons #x400d08 #x1f) ;;  
   (cons #x400d09 #x89) ;; mov %edx,%eax 
   (cons #x400d0a #xd0) ;;  
   (cons #x400d0b #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x400d0c #x45) ;;  
   (cons #x400d0d #xec) ;;  
   (cons #x400d0e #x29) ;; sub %edx,%eax 
   (cons #x400d0f #xd0) ;;  
   (cons #x400d10 #x48) ;; cltq 
   (cons #x400d11 #x98) ;;  
   (cons #x400d12 #x48) ;; shl $0x2,%rax 
   (cons #x400d13 #xc1) ;;  
   (cons #x400d14 #xe0) ;;  
   (cons #x400d15 #x02) ;;  
   (cons #x400d16 #x48) ;; add %rcx,%rax 
   (cons #x400d17 #x01) ;;  
   (cons #x400d18 #xc8) ;;  
   (cons #x400d19 #x8b) ;; mov (%rax),%eax 
   (cons #x400d1a #x00) ;;  
   (cons #x400d1b #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x400d1c #xf8) ;;  
   (cons #x400d1d #xf7) ;;  
   (cons #x400d1e #x74) ;; je 400d3d <analyze+0x113> 
   (cons #x400d1f #x1d) ;;  
   (cons #x400d20 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x400d21 #x45) ;;  
   (cons #x400d22 #xec) ;;  
   (cons #x400d23 #x89) ;; mov %eax,%edx 
   (cons #x400d24 #xc2) ;;  
   (cons #x400d25 #xc1) ;; sar $0x1f,%edx 
   (cons #x400d26 #xfa) ;;  
   (cons #x400d27 #x1f) ;;  
   (cons #x400d28 #x89) ;; mov %edx,%eax 
   (cons #x400d29 #xd0) ;;  
   (cons #x400d2a #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x400d2b #x45) ;;  
   (cons #x400d2c #xec) ;;  
   (cons #x400d2d #x29) ;; sub %edx,%eax 
   (cons #x400d2e #xd0) ;;  
   (cons #x400d2f #x48) ;; mov -0x48(%rbp),%rdx 
   (cons #x400d30 #x8b) ;;  
   (cons #x400d31 #x55) ;;  
   (cons #x400d32 #xb8) ;;  
   (cons #x400d33 #x89) ;; mov %eax,%esi 
   (cons #x400d34 #xc6) ;;  
   (cons #x400d35 #x48) ;; mov %rdx,%rdi 
   (cons #x400d36 #x89) ;;  
   (cons #x400d37 #xd7) ;;  
   (cons #x400d38 #xe8) ;; callq 4009cb <heapUp> 
   (cons #x400d39 #x8e) ;;  
   (cons #x400d3a #xfc) ;;  
   (cons #x400d3b #xff) ;;  
   (cons #x400d3c #xff) ;;  
   (cons #x400d3d #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400d3e #x8b) ;;  
   (cons #x400d3f #x45) ;;  
   (cons #x400d40 #xb8) ;;  
   (cons #x400d41 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400d42 #x8b) ;;  
   (cons #x400d43 #x40) ;;  
   (cons #x400d44 #x40) ;;  
   (cons #x400d45 #x8b) ;; mov -0x14(%rbp),%edx 
   (cons #x400d46 #x55) ;;  
   (cons #x400d47 #xec) ;;  
   (cons #x400d48 #x48) ;; movslq %edx,%rdx 
   (cons #x400d49 #x63) ;;  
   (cons #x400d4a #xd2) ;;  
   (cons #x400d4b #x48) ;; shl $0x2,%rdx 
   (cons #x400d4c #xc1) ;;  
   (cons #x400d4d #xe2) ;;  
   (cons #x400d4e #x02) ;;  
   (cons #x400d4f #x48) ;; add %rdx,%rax 
   (cons #x400d50 #x01) ;;  
   (cons #x400d51 #xd0) ;;  
   (cons #x400d52 #xc7) ;; movl $0x2,(%rax) 
   (cons #x400d53 #x00) ;;  
   (cons #x400d54 #x02) ;;  
   (cons #x400d55 #x00) ;;  
   (cons #x400d56 #x00) ;;  
   (cons #x400d57 #x00) ;;  
   (cons #x400d58 #x48) ;; mov -0x50(%rbp),%rax 
   (cons #x400d59 #x8b) ;;  
   (cons #x400d5a #x45) ;;  
   (cons #x400d5b #xb0) ;;  
   (cons #x400d5c #x8b) ;; mov (%rax),%eax 
   (cons #x400d5d #x00) ;;  
   (cons #x400d5e #x85) ;; test %eax,%eax 
   (cons #x400d5f #xc0) ;;  
   (cons #x400d60 #x0f) ;; jne 400c72 <analyze+0x48> 
   (cons #x400d61 #x85) ;;  
   (cons #x400d62 #x0c) ;;  
   (cons #x400d63 #xff) ;;  
   (cons #x400d64 #xff) ;;  
   (cons #x400d65 #xff) ;;  
   (cons #x400d66 #xe9) ;; jmpq 400fd2 <analyze+0x3a8> 
   (cons #x400d67 #x67) ;;  
   (cons #x400d68 #x02) ;;  
   (cons #x400d69 #x00) ;;  
   (cons #x400d6a #x00) ;;  
   (cons #x400d6b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400d6c #x8b) ;;  
   (cons #x400d6d #x45) ;;  
   (cons #x400d6e #xb8) ;;  
   (cons #x400d6f #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x400d70 #x8b) ;;  
   (cons #x400d71 #x50) ;;  
   (cons #x400d72 #x40) ;;  
   (cons #x400d73 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400d74 #x8b) ;;  
   (cons #x400d75 #x45) ;;  
   (cons #x400d76 #xb8) ;;  
   (cons #x400d77 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400d78 #x8b) ;;  
   (cons #x400d79 #x80) ;;  
   (cons #x400d7a #x80) ;;  
   (cons #x400d7b #x00) ;;  
   (cons #x400d7c #x00) ;;  
   (cons #x400d7d #x00) ;;  
   (cons #x400d7e #x8b) ;; mov (%rax),%eax 
   (cons #x400d7f #x00) ;;  
   (cons #x400d80 #x48) ;; cltq 
   (cons #x400d81 #x98) ;;  
   (cons #x400d82 #x48) ;; shl $0x2,%rax 
   (cons #x400d83 #xc1) ;;  
   (cons #x400d84 #xe0) ;;  
   (cons #x400d85 #x02) ;;  
   (cons #x400d86 #x48) ;; add %rdx,%rax 
   (cons #x400d87 #x01) ;;  
   (cons #x400d88 #xd0) ;;  
   (cons #x400d89 #x8b) ;; mov (%rax),%eax 
   (cons #x400d8a #x00) ;;  
   (cons #x400d8b #x83) ;; cmp $0x2,%eax 
   (cons #x400d8c #xf8) ;;  
   (cons #x400d8d #x02) ;;  
   (cons #x400d8e #x0f) ;; jne 400f28 <analyze+0x2fe> 
   (cons #x400d8f #x85) ;;  
   (cons #x400d90 #x94) ;;  
   (cons #x400d91 #x01) ;;  
   (cons #x400d92 #x00) ;;  
   (cons #x400d93 #x00) ;;  
   (cons #x400d94 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400d95 #x8b) ;;  
   (cons #x400d96 #x45) ;;  
   (cons #x400d97 #xb8) ;;  
   (cons #x400d98 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400d99 #x8b) ;;  
   (cons #x400d9a #x80) ;;  
   (cons #x400d9b #x80) ;;  
   (cons #x400d9c #x00) ;;  
   (cons #x400d9d #x00) ;;  
   (cons #x400d9e #x00) ;;  
   (cons #x400d9f #x48) ;; mov %rax,-0x28(%rbp) 
   (cons #x400da0 #x89) ;;  
   (cons #x400da1 #x45) ;;  
   (cons #x400da2 #xd8) ;;  
   (cons #x400da3 #xeb) ;; jmp 400dcf <analyze+0x1a5> 
   (cons #x400da4 #x2a) ;;  
   (cons #x400da5 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400da6 #x8b) ;;  
   (cons #x400da7 #x45) ;;  
   (cons #x400da8 #xb8) ;;  
   (cons #x400da9 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x400daa #x8b) ;;  
   (cons #x400dab #x48) ;;  
   (cons #x400dac #x30) ;;  
   (cons #x400dad #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x400dae #x8b) ;;  
   (cons #x400daf #x45) ;;  
   (cons #x400db0 #xd8) ;;  
   (cons #x400db1 #x8b) ;; mov (%rax),%eax 
   (cons #x400db2 #x00) ;;  
   (cons #x400db3 #x89) ;; mov %eax,%edx 
   (cons #x400db4 #xc2) ;;  
   (cons #x400db5 #xc1) ;; sar $0x1f,%edx 
   (cons #x400db6 #xfa) ;;  
   (cons #x400db7 #x1f) ;;  
   (cons #x400db8 #x31) ;; xor %edx,%eax 
   (cons #x400db9 #xd0) ;;  
   (cons #x400dba #x29) ;; sub %edx,%eax 
   (cons #x400dbb #xd0) ;;  
   (cons #x400dbc #x48) ;; cltq 
   (cons #x400dbd #x98) ;;  
   (cons #x400dbe #x48) ;; shl $0x2,%rax 
   (cons #x400dbf #xc1) ;;  
   (cons #x400dc0 #xe0) ;;  
   (cons #x400dc1 #x02) ;;  
   (cons #x400dc2 #x48) ;; add %rcx,%rax 
   (cons #x400dc3 #x01) ;;  
   (cons #x400dc4 #xc8) ;;  
   (cons #x400dc5 #x8b) ;; mov (%rax),%eax 
   (cons #x400dc6 #x00) ;;  
   (cons #x400dc7 #x85) ;; test %eax,%eax 
   (cons #x400dc8 #xc0) ;;  
   (cons #x400dc9 #x0f) ;; je 40101f <analyze+0x3f5> 
   (cons #x400dca #x84) ;;  
   (cons #x400dcb #x50) ;;  
   (cons #x400dcc #x02) ;;  
   (cons #x400dcd #x00) ;;  
   (cons #x400dce #x00) ;;  
   (cons #x400dcf #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400dd0 #x8b) ;;  
   (cons #x400dd1 #x45) ;;  
   (cons #x400dd2 #xb8) ;;  
   (cons #x400dd3 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x400dd4 #x8b) ;;  
   (cons #x400dd5 #x50) ;;  
   (cons #x400dd6 #x40) ;;  
   (cons #x400dd7 #x48) ;; subq $0x4,-0x28(%rbp) 
   (cons #x400dd8 #x83) ;;  
   (cons #x400dd9 #x6d) ;;  
   (cons #x400dda #xd8) ;;  
   (cons #x400ddb #x04) ;;  
   (cons #x400ddc #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x400ddd #x8b) ;;  
   (cons #x400dde #x45) ;;  
   (cons #x400ddf #xd8) ;;  
   (cons #x400de0 #x8b) ;; mov (%rax),%eax 
   (cons #x400de1 #x00) ;;  
   (cons #x400de2 #x48) ;; cltq 
   (cons #x400de3 #x98) ;;  
   (cons #x400de4 #x48) ;; shl $0x2,%rax 
   (cons #x400de5 #xc1) ;;  
   (cons #x400de6 #xe0) ;;  
   (cons #x400de7 #x02) ;;  
   (cons #x400de8 #x48) ;; add %rdx,%rax 
   (cons #x400de9 #x01) ;;  
   (cons #x400dea #xd0) ;;  
   (cons #x400deb #x8b) ;; mov (%rax),%eax 
   (cons #x400dec #x00) ;;  
   (cons #x400ded #x83) ;; cmp $0x2,%eax 
   (cons #x400dee #xf8) ;;  
   (cons #x400def #x02) ;;  
   (cons #x400df0 #x75) ;; jne 400da5 <analyze+0x17b> 
   (cons #x400df1 #xb3) ;;  
   (cons #x400df2 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400df3 #x8b) ;;  
   (cons #x400df4 #x45) ;;  
   (cons #x400df5 #xb8) ;;  
   (cons #x400df6 #x48) ;; mov (%rax),%rcx 
   (cons #x400df7 #x8b) ;;  
   (cons #x400df8 #x08) ;;  
   (cons #x400df9 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400dfa #x8b) ;;  
   (cons #x400dfb #x45) ;;  
   (cons #x400dfc #xb8) ;;  
   (cons #x400dfd #x48) ;; mov 0x30(%rax),%rsi 
   (cons #x400dfe #x8b) ;;  
   (cons #x400dff #x70) ;;  
   (cons #x400e00 #x30) ;;  
   (cons #x400e01 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400e02 #x8b) ;;  
   (cons #x400e03 #x45) ;;  
   (cons #x400e04 #xb8) ;;  
   (cons #x400e05 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400e06 #x8b) ;;  
   (cons #x400e07 #x80) ;;  
   (cons #x400e08 #x80) ;;  
   (cons #x400e09 #x00) ;;  
   (cons #x400e0a #x00) ;;  
   (cons #x400e0b #x00) ;;  
   (cons #x400e0c #x8b) ;; mov (%rax),%eax 
   (cons #x400e0d #x00) ;;  
   (cons #x400e0e #x89) ;; mov %eax,%edx 
   (cons #x400e0f #xc2) ;;  
   (cons #x400e10 #xc1) ;; sar $0x1f,%edx 
   (cons #x400e11 #xfa) ;;  
   (cons #x400e12 #x1f) ;;  
   (cons #x400e13 #x31) ;; xor %edx,%eax 
   (cons #x400e14 #xd0) ;;  
   (cons #x400e15 #x29) ;; sub %edx,%eax 
   (cons #x400e16 #xd0) ;;  
   (cons #x400e17 #x48) ;; cltq 
   (cons #x400e18 #x98) ;;  
   (cons #x400e19 #x48) ;; shl $0x2,%rax 
   (cons #x400e1a #xc1) ;;  
   (cons #x400e1b #xe0) ;;  
   (cons #x400e1c #x02) ;;  
   (cons #x400e1d #x48) ;; add %rsi,%rax 
   (cons #x400e1e #x01) ;;  
   (cons #x400e1f #xf0) ;;  
   (cons #x400e20 #x8b) ;; mov (%rax),%eax 
   (cons #x400e21 #x00) ;;  
   (cons #x400e22 #x48) ;; cltq 
   (cons #x400e23 #x98) ;;  
   (cons #x400e24 #x48) ;; shl $0x2,%rax 
   (cons #x400e25 #xc1) ;;  
   (cons #x400e26 #xe0) ;;  
   (cons #x400e27 #x02) ;;  
   (cons #x400e28 #x48) ;; add %rcx,%rax 
   (cons #x400e29 #x01) ;;  
   (cons #x400e2a #xc8) ;;  
   (cons #x400e2b #x48) ;; mov %rax,-0x50(%rbp) 
   (cons #x400e2c #x89) ;;  
   (cons #x400e2d #x45) ;;  
   (cons #x400e2e #xb0) ;;  
   (cons #x400e2f #xe9) ;; jmpq 400f1a <analyze+0x2f0> 
   (cons #x400e30 #xe6) ;;  
   (cons #x400e31 #x00) ;;  
   (cons #x400e32 #x00) ;;  
   (cons #x400e33 #x00) ;;  
   (cons #x400e34 #x48) ;; mov -0x50(%rbp),%rax 
   (cons #x400e35 #x8b) ;;  
   (cons #x400e36 #x45) ;;  
   (cons #x400e37 #xb0) ;;  
   (cons #x400e38 #x8b) ;; mov (%rax),%eax 
   (cons #x400e39 #x00) ;;  
   (cons #x400e3a #x89) ;; mov %eax,-0x10(%rbp) 
   (cons #x400e3b #x45) ;;  
   (cons #x400e3c #xf0) ;;  
   (cons #x400e3d #x48) ;; addq $0x4,-0x50(%rbp) 
   (cons #x400e3e #x83) ;;  
   (cons #x400e3f #x45) ;;  
   (cons #x400e40 #xb0) ;;  
   (cons #x400e41 #x04) ;;  
   (cons #x400e42 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400e43 #x8b) ;;  
   (cons #x400e44 #x45) ;;  
   (cons #x400e45 #xb8) ;;  
   (cons #x400e46 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400e47 #x8b) ;;  
   (cons #x400e48 #x40) ;;  
   (cons #x400e49 #x40) ;;  
   (cons #x400e4a #x8b) ;; mov -0x10(%rbp),%edx 
   (cons #x400e4b #x55) ;;  
   (cons #x400e4c #xf0) ;;  
   (cons #x400e4d #x48) ;; movslq %edx,%rdx 
   (cons #x400e4e #x63) ;;  
   (cons #x400e4f #xd2) ;;  
   (cons #x400e50 #x48) ;; shl $0x2,%rdx 
   (cons #x400e51 #xc1) ;;  
   (cons #x400e52 #xe2) ;;  
   (cons #x400e53 #x02) ;;  
   (cons #x400e54 #x48) ;; add %rdx,%rax 
   (cons #x400e55 #x01) ;;  
   (cons #x400e56 #xd0) ;;  
   (cons #x400e57 #x8b) ;; mov (%rax),%eax 
   (cons #x400e58 #x00) ;;  
   (cons #x400e59 #x83) ;; cmp $0x2,%eax 
   (cons #x400e5a #xf8) ;;  
   (cons #x400e5b #x02) ;;  
   (cons #x400e5c #x0f) ;; je 400eff <analyze+0x2d5> 
   (cons #x400e5d #x84) ;;  
   (cons #x400e5e #x9d) ;;  
   (cons #x400e5f #x00) ;;  
   (cons #x400e60 #x00) ;;  
   (cons #x400e61 #x00) ;;  
   (cons #x400e62 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400e63 #x8b) ;;  
   (cons #x400e64 #x45) ;;  
   (cons #x400e65 #xb8) ;;  
   (cons #x400e66 #x48) ;; mov 0x68(%rax),%rcx 
   (cons #x400e67 #x8b) ;;  
   (cons #x400e68 #x48) ;;  
   (cons #x400e69 #x68) ;;  
   (cons #x400e6a #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x400e6b #x45) ;;  
   (cons #x400e6c #xf0) ;;  
   (cons #x400e6d #x89) ;; mov %eax,%edx 
   (cons #x400e6e #xc2) ;;  
   (cons #x400e6f #xc1) ;; sar $0x1f,%edx 
   (cons #x400e70 #xfa) ;;  
   (cons #x400e71 #x1f) ;;  
   (cons #x400e72 #x89) ;; mov %edx,%eax 
   (cons #x400e73 #xd0) ;;  
   (cons #x400e74 #x33) ;; xor -0x10(%rbp),%eax 
   (cons #x400e75 #x45) ;;  
   (cons #x400e76 #xf0) ;;  
   (cons #x400e77 #x29) ;; sub %edx,%eax 
   (cons #x400e78 #xd0) ;;  
   (cons #x400e79 #x48) ;; cltq 
   (cons #x400e7a #x98) ;;  
   (cons #x400e7b #x48) ;; shl $0x2,%rax 
   (cons #x400e7c #xc1) ;;  
   (cons #x400e7d #xe0) ;;  
   (cons #x400e7e #x02) ;;  
   (cons #x400e7f #x48) ;; add %rax,%rcx 
   (cons #x400e80 #x01) ;;  
   (cons #x400e81 #xc1) ;;  
   (cons #x400e82 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400e83 #x8b) ;;  
   (cons #x400e84 #x45) ;;  
   (cons #x400e85 #xb8) ;;  
   (cons #x400e86 #x48) ;; mov 0x68(%rax),%rsi 
   (cons #x400e87 #x8b) ;;  
   (cons #x400e88 #x70) ;;  
   (cons #x400e89 #x68) ;;  
   (cons #x400e8a #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x400e8b #x45) ;;  
   (cons #x400e8c #xf0) ;;  
   (cons #x400e8d #x89) ;; mov %eax,%edx 
   (cons #x400e8e #xc2) ;;  
   (cons #x400e8f #xc1) ;; sar $0x1f,%edx 
   (cons #x400e90 #xfa) ;;  
   (cons #x400e91 #x1f) ;;  
   (cons #x400e92 #x89) ;; mov %edx,%eax 
   (cons #x400e93 #xd0) ;;  
   (cons #x400e94 #x33) ;; xor -0x10(%rbp),%eax 
   (cons #x400e95 #x45) ;;  
   (cons #x400e96 #xf0) ;;  
   (cons #x400e97 #x29) ;; sub %edx,%eax 
   (cons #x400e98 #xd0) ;;  
   (cons #x400e99 #x48) ;; cltq 
   (cons #x400e9a #x98) ;;  
   (cons #x400e9b #x48) ;; shl $0x2,%rax 
   (cons #x400e9c #xc1) ;;  
   (cons #x400e9d #xe0) ;;  
   (cons #x400e9e #x02) ;;  
   (cons #x400e9f #x48) ;; add %rsi,%rax 
   (cons #x400ea0 #x01) ;;  
   (cons #x400ea1 #xf0) ;;  
   (cons #x400ea2 #x8b) ;; mov (%rax),%edx 
   (cons #x400ea3 #x10) ;;  
   (cons #x400ea4 #x89) ;; mov %edx,%eax 
   (cons #x400ea5 #xd0) ;;  
   (cons #x400ea6 #x01) ;; add %eax,%eax 
   (cons #x400ea7 #xc0) ;;  
   (cons #x400ea8 #x01) ;; add %eax,%edx 
   (cons #x400ea9 #xc2) ;;  
   (cons #x400eaa #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400eab #x8b) ;;  
   (cons #x400eac #x45) ;;  
   (cons #x400ead #xb8) ;;  
   (cons #x400eae #x8b) ;; mov 0x24(%rax),%eax 
   (cons #x400eaf #x40) ;;  
   (cons #x400eb0 #x24) ;;  
   (cons #x400eb1 #xc1) ;; shl $0x5,%eax 
   (cons #x400eb2 #xe0) ;;  
   (cons #x400eb3 #x05) ;;  
   (cons #x400eb4 #x01) ;; add %edx,%eax 
   (cons #x400eb5 #xd0) ;;  
   (cons #x400eb6 #xc1) ;; sar $0x2,%eax 
   (cons #x400eb7 #xf8) ;;  
   (cons #x400eb8 #x02) ;;  
   (cons #x400eb9 #x89) ;; mov %eax,(%rcx) 
   (cons #x400eba #x01) ;;  
   (cons #x400ebb #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400ebc #x8b) ;;  
   (cons #x400ebd #x45) ;;  
   (cons #x400ebe #xb8) ;;  
   (cons #x400ebf #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x400ec0 #x8b) ;;  
   (cons #x400ec1 #x48) ;;  
   (cons #x400ec2 #x60) ;;  
   (cons #x400ec3 #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x400ec4 #x45) ;;  
   (cons #x400ec5 #xf0) ;;  
   (cons #x400ec6 #x89) ;; mov %eax,%edx 
   (cons #x400ec7 #xc2) ;;  
   (cons #x400ec8 #xc1) ;; sar $0x1f,%edx 
   (cons #x400ec9 #xfa) ;;  
   (cons #x400eca #x1f) ;;  
   (cons #x400ecb #x89) ;; mov %edx,%eax 
   (cons #x400ecc #xd0) ;;  
   (cons #x400ecd #x33) ;; xor -0x10(%rbp),%eax 
   (cons #x400ece #x45) ;;  
   (cons #x400ecf #xf0) ;;  
   (cons #x400ed0 #x29) ;; sub %edx,%eax 
   (cons #x400ed1 #xd0) ;;  
   (cons #x400ed2 #x48) ;; cltq 
   (cons #x400ed3 #x98) ;;  
   (cons #x400ed4 #x48) ;; shl $0x2,%rax 
   (cons #x400ed5 #xc1) ;;  
   (cons #x400ed6 #xe0) ;;  
   (cons #x400ed7 #x02) ;;  
   (cons #x400ed8 #x48) ;; add %rcx,%rax 
   (cons #x400ed9 #x01) ;;  
   (cons #x400eda #xc8) ;;  
   (cons #x400edb #x8b) ;; mov (%rax),%eax 
   (cons #x400edc #x00) ;;  
   (cons #x400edd #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x400ede #xf8) ;;  
   (cons #x400edf #xf7) ;;  
   (cons #x400ee0 #x74) ;; je 400eff <analyze+0x2d5> 
   (cons #x400ee1 #x1d) ;;  
   (cons #x400ee2 #x8b) ;; mov -0x10(%rbp),%eax 
   (cons #x400ee3 #x45) ;;  
   (cons #x400ee4 #xf0) ;;  
   (cons #x400ee5 #x89) ;; mov %eax,%edx 
   (cons #x400ee6 #xc2) ;;  
   (cons #x400ee7 #xc1) ;; sar $0x1f,%edx 
   (cons #x400ee8 #xfa) ;;  
   (cons #x400ee9 #x1f) ;;  
   (cons #x400eea #x89) ;; mov %edx,%eax 
   (cons #x400eeb #xd0) ;;  
   (cons #x400eec #x33) ;; xor -0x10(%rbp),%eax 
   (cons #x400eed #x45) ;;  
   (cons #x400eee #xf0) ;;  
   (cons #x400eef #x29) ;; sub %edx,%eax 
   (cons #x400ef0 #xd0) ;;  
   (cons #x400ef1 #x48) ;; mov -0x48(%rbp),%rdx 
   (cons #x400ef2 #x8b) ;;  
   (cons #x400ef3 #x55) ;;  
   (cons #x400ef4 #xb8) ;;  
   (cons #x400ef5 #x89) ;; mov %eax,%esi 
   (cons #x400ef6 #xc6) ;;  
   (cons #x400ef7 #x48) ;; mov %rdx,%rdi 
   (cons #x400ef8 #x89) ;;  
   (cons #x400ef9 #xd7) ;;  
   (cons #x400efa #xe8) ;; callq 4009cb <heapUp> 
   (cons #x400efb #xcc) ;;  
   (cons #x400efc #xfa) ;;  
   (cons #x400efd #xff) ;;  
   (cons #x400efe #xff) ;;  
   (cons #x400eff #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f00 #x8b) ;;  
   (cons #x400f01 #x45) ;;  
   (cons #x400f02 #xb8) ;;  
   (cons #x400f03 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400f04 #x8b) ;;  
   (cons #x400f05 #x40) ;;  
   (cons #x400f06 #x40) ;;  
   (cons #x400f07 #x8b) ;; mov -0x10(%rbp),%edx 
   (cons #x400f08 #x55) ;;  
   (cons #x400f09 #xf0) ;;  
   (cons #x400f0a #x48) ;; movslq %edx,%rdx 
   (cons #x400f0b #x63) ;;  
   (cons #x400f0c #xd2) ;;  
   (cons #x400f0d #x48) ;; shl $0x2,%rdx 
   (cons #x400f0e #xc1) ;;  
   (cons #x400f0f #xe2) ;;  
   (cons #x400f10 #x02) ;;  
   (cons #x400f11 #x48) ;; add %rdx,%rax 
   (cons #x400f12 #x01) ;;  
   (cons #x400f13 #xd0) ;;  
   (cons #x400f14 #xc7) ;; movl $0x2,(%rax) 
   (cons #x400f15 #x00) ;;  
   (cons #x400f16 #x02) ;;  
   (cons #x400f17 #x00) ;;  
   (cons #x400f18 #x00) ;;  
   (cons #x400f19 #x00) ;;  
   (cons #x400f1a #x48) ;; mov -0x50(%rbp),%rax 
   (cons #x400f1b #x8b) ;;  
   (cons #x400f1c #x45) ;;  
   (cons #x400f1d #xb0) ;;  
   (cons #x400f1e #x8b) ;; mov (%rax),%eax 
   (cons #x400f1f #x00) ;;  
   (cons #x400f20 #x85) ;; test %eax,%eax 
   (cons #x400f21 #xc0) ;;  
   (cons #x400f22 #x0f) ;; jne 400e34 <analyze+0x20a> 
   (cons #x400f23 #x85) ;;  
   (cons #x400f24 #x0c) ;;  
   (cons #x400f25 #xff) ;;  
   (cons #x400f26 #xff) ;;  
   (cons #x400f27 #xff) ;;  
   (cons #x400f28 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f29 #x8b) ;;  
   (cons #x400f2a #x45) ;;  
   (cons #x400f2b #xb8) ;;  
   (cons #x400f2c #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400f2d #x8b) ;;  
   (cons #x400f2e #x80) ;;  
   (cons #x400f2f #x80) ;;  
   (cons #x400f30 #x00) ;;  
   (cons #x400f31 #x00) ;;  
   (cons #x400f32 #x00) ;;  
   (cons #x400f33 #x8b) ;; mov (%rax),%eax 
   (cons #x400f34 #x00) ;;  
   (cons #x400f35 #x89) ;; mov %eax,-0xc(%rbp) 
   (cons #x400f36 #x45) ;;  
   (cons #x400f37 #xf4) ;;  
   (cons #x400f38 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f39 #x8b) ;;  
   (cons #x400f3a #x45) ;;  
   (cons #x400f3b #xb8) ;;  
   (cons #x400f3c #x48) ;; mov 0x40(%rax),%rax 
   (cons #x400f3d #x8b) ;;  
   (cons #x400f3e #x40) ;;  
   (cons #x400f3f #x40) ;;  
   (cons #x400f40 #x8b) ;; mov -0xc(%rbp),%edx 
   (cons #x400f41 #x55) ;;  
   (cons #x400f42 #xf4) ;;  
   (cons #x400f43 #x48) ;; movslq %edx,%rdx 
   (cons #x400f44 #x63) ;;  
   (cons #x400f45 #xd2) ;;  
   (cons #x400f46 #x48) ;; shl $0x2,%rdx 
   (cons #x400f47 #xc1) ;;  
   (cons #x400f48 #xe2) ;;  
   (cons #x400f49 #x02) ;;  
   (cons #x400f4a #x48) ;; add %rdx,%rax 
   (cons #x400f4b #x01) ;;  
   (cons #x400f4c #xd0) ;;  
   (cons #x400f4d #xc7) ;; movl $0x0,(%rax) 
   (cons #x400f4e #x00) ;;  
   (cons #x400f4f #x00) ;;  
   (cons #x400f50 #x00) ;;  
   (cons #x400f51 #x00) ;;  
   (cons #x400f52 #x00) ;;  
   (cons #x400f53 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f54 #x8b) ;;  
   (cons #x400f55 #x45) ;;  
   (cons #x400f56 #xb8) ;;  
   (cons #x400f57 #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x400f58 #x8b) ;;  
   (cons #x400f59 #x48) ;;  
   (cons #x400f5a #x60) ;;  
   (cons #x400f5b #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x400f5c #x45) ;;  
   (cons #x400f5d #xf4) ;;  
   (cons #x400f5e #x89) ;; mov %eax,%edx 
   (cons #x400f5f #xc2) ;;  
   (cons #x400f60 #xc1) ;; sar $0x1f,%edx 
   (cons #x400f61 #xfa) ;;  
   (cons #x400f62 #x1f) ;;  
   (cons #x400f63 #x89) ;; mov %edx,%eax 
   (cons #x400f64 #xd0) ;;  
   (cons #x400f65 #x33) ;; xor -0xc(%rbp),%eax 
   (cons #x400f66 #x45) ;;  
   (cons #x400f67 #xf4) ;;  
   (cons #x400f68 #x29) ;; sub %edx,%eax 
   (cons #x400f69 #xd0) ;;  
   (cons #x400f6a #x48) ;; cltq 
   (cons #x400f6b #x98) ;;  
   (cons #x400f6c #x48) ;; shl $0x2,%rax 
   (cons #x400f6d #xc1) ;;  
   (cons #x400f6e #xe0) ;;  
   (cons #x400f6f #x02) ;;  
   (cons #x400f70 #x48) ;; add %rcx,%rax 
   (cons #x400f71 #x01) ;;  
   (cons #x400f72 #xc8) ;;  
   (cons #x400f73 #x8b) ;; mov (%rax),%eax 
   (cons #x400f74 #x00) ;;  
   (cons #x400f75 #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x400f76 #xf8) ;;  
   (cons #x400f77 #xf7) ;;  
   (cons #x400f78 #x75) ;; jne 400fd2 <analyze+0x3a8> 
   (cons #x400f79 #x58) ;;  
   (cons #x400f7a #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f7b #x8b) ;;  
   (cons #x400f7c #x45) ;;  
   (cons #x400f7d #xb8) ;;  
   (cons #x400f7e #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x400f7f #x8b) ;;  
   (cons #x400f80 #x48) ;;  
   (cons #x400f81 #x60) ;;  
   (cons #x400f82 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x400f83 #x45) ;;  
   (cons #x400f84 #xf4) ;;  
   (cons #x400f85 #x89) ;; mov %eax,%edx 
   (cons #x400f86 #xc2) ;;  
   (cons #x400f87 #xc1) ;; sar $0x1f,%edx 
   (cons #x400f88 #xfa) ;;  
   (cons #x400f89 #x1f) ;;  
   (cons #x400f8a #x89) ;; mov %edx,%eax 
   (cons #x400f8b #xd0) ;;  
   (cons #x400f8c #x33) ;; xor -0xc(%rbp),%eax 
   (cons #x400f8d #x45) ;;  
   (cons #x400f8e #xf4) ;;  
   (cons #x400f8f #x29) ;; sub %edx,%eax 
   (cons #x400f90 #xd0) ;;  
   (cons #x400f91 #x48) ;; cltq 
   (cons #x400f92 #x98) ;;  
   (cons #x400f93 #x48) ;; shl $0x2,%rax 
   (cons #x400f94 #xc1) ;;  
   (cons #x400f95 #xe0) ;;  
   (cons #x400f96 #x02) ;;  
   (cons #x400f97 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x400f98 #x8d) ;;  
   (cons #x400f99 #x14) ;;  
   (cons #x400f9a #x01) ;;  
   (cons #x400f9b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400f9c #x8b) ;;  
   (cons #x400f9d #x45) ;;  
   (cons #x400f9e #xb8) ;;  
   (cons #x400f9f #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x400fa0 #x40) ;;  
   (cons #x400fa1 #x58) ;;  
   (cons #x400fa2 #x8d) ;; lea 0x1(%rax),%ecx 
   (cons #x400fa3 #x48) ;;  
   (cons #x400fa4 #x01) ;;  
   (cons #x400fa5 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400fa6 #x8b) ;;  
   (cons #x400fa7 #x45) ;;  
   (cons #x400fa8 #xb8) ;;  
   (cons #x400fa9 #x89) ;; mov %ecx,0x58(%rax) 
   (cons #x400faa #x48) ;;  
   (cons #x400fab #x58) ;;  
   (cons #x400fac #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400fad #x8b) ;;  
   (cons #x400fae #x45) ;;  
   (cons #x400faf #xb8) ;;  
   (cons #x400fb0 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x400fb1 #x40) ;;  
   (cons #x400fb2 #x58) ;;  
   (cons #x400fb3 #x89) ;; mov %eax,(%rdx) 
   (cons #x400fb4 #x02) ;;  
   (cons #x400fb5 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x400fb6 #x45) ;;  
   (cons #x400fb7 #xf4) ;;  
   (cons #x400fb8 #x89) ;; mov %eax,%edx 
   (cons #x400fb9 #xc2) ;;  
   (cons #x400fba #xc1) ;; sar $0x1f,%edx 
   (cons #x400fbb #xfa) ;;  
   (cons #x400fbc #x1f) ;;  
   (cons #x400fbd #x89) ;; mov %edx,%eax 
   (cons #x400fbe #xd0) ;;  
   (cons #x400fbf #x33) ;; xor -0xc(%rbp),%eax 
   (cons #x400fc0 #x45) ;;  
   (cons #x400fc1 #xf4) ;;  
   (cons #x400fc2 #x29) ;; sub %edx,%eax 
   (cons #x400fc3 #xd0) ;;  
   (cons #x400fc4 #x48) ;; mov -0x48(%rbp),%rdx 
   (cons #x400fc5 #x8b) ;;  
   (cons #x400fc6 #x55) ;;  
   (cons #x400fc7 #xb8) ;;  
   (cons #x400fc8 #x89) ;; mov %eax,%esi 
   (cons #x400fc9 #xc6) ;;  
   (cons #x400fca #x48) ;; mov %rdx,%rdi 
   (cons #x400fcb #x89) ;;  
   (cons #x400fcc #xd7) ;;  
   (cons #x400fcd #xe8) ;; callq 4009cb <heapUp> 
   (cons #x400fce #xf9) ;;  
   (cons #x400fcf #xf9) ;;  
   (cons #x400fd0 #xff) ;;  
   (cons #x400fd1 #xff) ;;  
   (cons #x400fd2 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400fd3 #x8b) ;;  
   (cons #x400fd4 #x45) ;;  
   (cons #x400fd5 #xb8) ;;  
   (cons #x400fd6 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x400fd7 #x8b) ;;  
   (cons #x400fd8 #x48) ;;  
   (cons #x400fd9 #x30) ;;  
   (cons #x400fda #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400fdb #x8b) ;;  
   (cons #x400fdc #x45) ;;  
   (cons #x400fdd #xb8) ;;  
   (cons #x400fde #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400fdf #x8b) ;;  
   (cons #x400fe0 #x80) ;;  
   (cons #x400fe1 #x80) ;;  
   (cons #x400fe2 #x00) ;;  
   (cons #x400fe3 #x00) ;;  
   (cons #x400fe4 #x00) ;;  
   (cons #x400fe5 #x48) ;; lea -0x4(%rax),%rdx 
   (cons #x400fe6 #x8d) ;;  
   (cons #x400fe7 #x50) ;;  
   (cons #x400fe8 #xfc) ;;  
   (cons #x400fe9 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400fea #x8b) ;;  
   (cons #x400feb #x45) ;;  
   (cons #x400fec #xb8) ;;  
   (cons #x400fed #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x400fee #x89) ;;  
   (cons #x400fef #x90) ;;  
   (cons #x400ff0 #x80) ;;  
   (cons #x400ff1 #x00) ;;  
   (cons #x400ff2 #x00) ;;  
   (cons #x400ff3 #x00) ;;  
   (cons #x400ff4 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x400ff5 #x8b) ;;  
   (cons #x400ff6 #x45) ;;  
   (cons #x400ff7 #xb8) ;;  
   (cons #x400ff8 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x400ff9 #x8b) ;;  
   (cons #x400ffa #x80) ;;  
   (cons #x400ffb #x80) ;;  
   (cons #x400ffc #x00) ;;  
   (cons #x400ffd #x00) ;;  
   (cons #x400ffe #x00) ;;  
   (cons #x400fff #x8b) ;; mov (%rax),%eax 
   (cons #x401000 #x00) ;;  
   (cons #x401001 #x89) ;; mov %eax,%edx 
   (cons #x401002 #xc2) ;;  
   (cons #x401003 #xc1) ;; sar $0x1f,%edx 
   (cons #x401004 #xfa) ;;  
   (cons #x401005 #x1f) ;;  
   (cons #x401006 #x31) ;; xor %edx,%eax 
   (cons #x401007 #xd0) ;;  
   (cons #x401008 #x29) ;; sub %edx,%eax 
   (cons #x401009 #xd0) ;;  
   (cons #x40100a #x48) ;; cltq 
   (cons #x40100b #x98) ;;  
   (cons #x40100c #x48) ;; shl $0x2,%rax 
   (cons #x40100d #xc1) ;;  
   (cons #x40100e #xe0) ;;  
   (cons #x40100f #x02) ;;  
   (cons #x401010 #x48) ;; add %rcx,%rax 
   (cons #x401011 #x01) ;;  
   (cons #x401012 #xc8) ;;  
   (cons #x401013 #x8b) ;; mov (%rax),%eax 
   (cons #x401014 #x00) ;;  
   (cons #x401015 #x85) ;; test %eax,%eax 
   (cons #x401016 #xc0) ;;  
   (cons #x401017 #x0f) ;; jne 400d6b <analyze+0x141> 
   (cons #x401018 #x85) ;;  
   (cons #x401019 #x4e) ;;  
   (cons #x40101a #xfd) ;;  
   (cons #x40101b #xff) ;;  
   (cons #x40101c #xff) ;;  
   (cons #x40101d #xeb) ;; jmp 401020 <analyze+0x3f6> 
   (cons #x40101e #x01) ;;  
   (cons #x40101f #x90) ;; nop 
   (cons #x401020 #xc7) ;; movl $0x0,-0x18(%rbp) 
   (cons #x401021 #x45) ;;  
   (cons #x401022 #xe8) ;;  
   (cons #x401023 #x00) ;;  
   (cons #x401024 #x00) ;;  
   (cons #x401025 #x00) ;;  
   (cons #x401026 #x00) ;;  
   (cons #x401027 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401028 #x8b) ;;  
   (cons #x401029 #x45) ;;  
   (cons #x40102a #xb8) ;;  
   (cons #x40102b #x48) ;; mov 0x80(%rax),%rax 
   (cons #x40102c #x8b) ;;  
   (cons #x40102d #x80) ;;  
   (cons #x40102e #x80) ;;  
   (cons #x40102f #x00) ;;  
   (cons #x401030 #x00) ;;  
   (cons #x401031 #x00) ;;  
   (cons #x401032 #x48) ;; mov %rax,-0x20(%rbp) 
   (cons #x401033 #x89) ;;  
   (cons #x401034 #x45) ;;  
   (cons #x401035 #xe0) ;;  
   (cons #x401036 #xe9) ;; jmpq 4010de <analyze+0x4b4> 
   (cons #x401037 #xa3) ;;  
   (cons #x401038 #x00) ;;  
   (cons #x401039 #x00) ;;  
   (cons #x40103a #x00) ;;  
   (cons #x40103b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40103c #x8b) ;;  
   (cons #x40103d #x45) ;;  
   (cons #x40103e #xb8) ;;  
   (cons #x40103f #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x401040 #x8b) ;;  
   (cons #x401041 #x50) ;;  
   (cons #x401042 #x40) ;;  
   (cons #x401043 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x401044 #x8b) ;;  
   (cons #x401045 #x45) ;;  
   (cons #x401046 #xe0) ;;  
   (cons #x401047 #x8b) ;; mov (%rax),%eax 
   (cons #x401048 #x00) ;;  
   (cons #x401049 #x48) ;; cltq 
   (cons #x40104a #x98) ;;  
   (cons #x40104b #x48) ;; shl $0x2,%rax 
   (cons #x40104c #xc1) ;;  
   (cons #x40104d #xe0) ;;  
   (cons #x40104e #x02) ;;  
   (cons #x40104f #x48) ;; add %rdx,%rax 
   (cons #x401050 #x01) ;;  
   (cons #x401051 #xd0) ;;  
   (cons #x401052 #x8b) ;; mov (%rax),%eax 
   (cons #x401053 #x00) ;;  
   (cons #x401054 #x83) ;; cmp $0x2,%eax 
   (cons #x401055 #xf8) ;;  
   (cons #x401056 #x02) ;;  
   (cons #x401057 #x75) ;; jne 401084 <analyze+0x45a> 
   (cons #x401058 #x2b) ;;  
   (cons #x401059 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x40105a #x8b) ;;  
   (cons #x40105b #x45) ;;  
   (cons #x40105c #xe0) ;;  
   (cons #x40105d #x8b) ;; mov (%rax),%edx 
   (cons #x40105e #x10) ;;  
   (cons #x40105f #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401060 #x8b) ;;  
   (cons #x401061 #x45) ;;  
   (cons #x401062 #xb8) ;;  
   (cons #x401063 #x89) ;; mov %edx,%esi 
   (cons #x401064 #xd6) ;;  
   (cons #x401065 #x48) ;; mov %rax,%rdi 
   (cons #x401066 #x89) ;;  
   (cons #x401067 #xc7) ;;  
   (cons #x401068 #xe8) ;; callq 400aeb <implied> 
   (cons #x401069 #x7e) ;;  
   (cons #x40106a #xfa) ;;  
   (cons #x40106b #xff) ;;  
   (cons #x40106c #xff) ;;  
   (cons #x40106d #x85) ;; test %eax,%eax 
   (cons #x40106e #xc0) ;;  
   (cons #x40106f #x75) ;; jne 401084 <analyze+0x45a> 
   (cons #x401070 #x13) ;;  
   (cons #x401071 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x401072 #x8b) ;;  
   (cons #x401073 #x45) ;;  
   (cons #x401074 #xe0) ;;  
   (cons #x401075 #x8b) ;; mov (%rax),%edx 
   (cons #x401076 #x10) ;;  
   (cons #x401077 #x8b) ;; mov -0x18(%rbp),%eax 
   (cons #x401078 #x45) ;;  
   (cons #x401079 #xe8) ;;  
   (cons #x40107a #x48) ;; cltq 
   (cons #x40107b #x98) ;;  
   (cons #x40107c #x89) ;; mov %edx,-0x40(%rbp,%rax,4) 
   (cons #x40107d #x54) ;;  
   (cons #x40107e #x85) ;;  
   (cons #x40107f #xc0) ;;  
   (cons #x401080 #x83) ;; addl $0x1,-0x18(%rbp) 
   (cons #x401081 #x45) ;;  
   (cons #x401082 #xe8) ;;  
   (cons #x401083 #x01) ;;  
   (cons #x401084 #x83) ;; cmpl $0x1,-0x18(%rbp) 
   (cons #x401085 #x7d) ;;  
   (cons #x401086 #xe8) ;;  
   (cons #x401087 #x01) ;;  
   (cons #x401088 #x75) ;; jne 4010bc <analyze+0x492> 
   (cons #x401089 #x32) ;;  
   (cons #x40108a #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40108b #x8b) ;;  
   (cons #x40108c #x45) ;;  
   (cons #x40108d #xb8) ;;  
   (cons #x40108e #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x40108f #x8b) ;;  
   (cons #x401090 #x48) ;;  
   (cons #x401091 #x30) ;;  
   (cons #x401092 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x401093 #x8b) ;;  
   (cons #x401094 #x45) ;;  
   (cons #x401095 #xe0) ;;  
   (cons #x401096 #x8b) ;; mov (%rax),%eax 
   (cons #x401097 #x00) ;;  
   (cons #x401098 #x89) ;; mov %eax,%edx 
   (cons #x401099 #xc2) ;;  
   (cons #x40109a #xc1) ;; sar $0x1f,%edx 
   (cons #x40109b #xfa) ;;  
   (cons #x40109c #x1f) ;;  
   (cons #x40109d #x31) ;; xor %edx,%eax 
   (cons #x40109e #xd0) ;;  
   (cons #x40109f #x29) ;; sub %edx,%eax 
   (cons #x4010a0 #xd0) ;;  
   (cons #x4010a1 #x48) ;; cltq 
   (cons #x4010a2 #x98) ;;  
   (cons #x4010a3 #x48) ;; shl $0x2,%rax 
   (cons #x4010a4 #xc1) ;;  
   (cons #x4010a5 #xe0) ;;  
   (cons #x4010a6 #x02) ;;  
   (cons #x4010a7 #x48) ;; add %rcx,%rax 
   (cons #x4010a8 #x01) ;;  
   (cons #x4010a9 #xc8) ;;  
   (cons #x4010aa #x8b) ;; mov (%rax),%eax 
   (cons #x4010ab #x00) ;;  
   (cons #x4010ac #x85) ;; test %eax,%eax 
   (cons #x4010ad #xc0) ;;  
   (cons #x4010ae #x75) ;; jne 4010bc <analyze+0x492> 
   (cons #x4010af #x0c) ;;  
   (cons #x4010b0 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4010b1 #x8b) ;;  
   (cons #x4010b2 #x45) ;;  
   (cons #x4010b3 #xb8) ;;  
   (cons #x4010b4 #x48) ;; mov -0x20(%rbp),%rdx 
   (cons #x4010b5 #x8b) ;;  
   (cons #x4010b6 #x55) ;;  
   (cons #x4010b7 #xe0) ;;  
   (cons #x4010b8 #x48) ;; mov %rdx,0x78(%rax) 
   (cons #x4010b9 #x89) ;;  
   (cons #x4010ba #x50) ;;  
   (cons #x4010bb #x78) ;;  
   (cons #x4010bc #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4010bd #x8b) ;;  
   (cons #x4010be #x45) ;;  
   (cons #x4010bf #xb8) ;;  
   (cons #x4010c0 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x4010c1 #x8b) ;;  
   (cons #x4010c2 #x50) ;;  
   (cons #x4010c3 #x40) ;;  
   (cons #x4010c4 #x48) ;; mov -0x20(%rbp),%rax 
   (cons #x4010c5 #x8b) ;;  
   (cons #x4010c6 #x45) ;;  
   (cons #x4010c7 #xe0) ;;  
   (cons #x4010c8 #x8b) ;; mov (%rax),%eax 
   (cons #x4010c9 #x00) ;;  
   (cons #x4010ca #x48) ;; cltq 
   (cons #x4010cb #x98) ;;  
   (cons #x4010cc #x48) ;; shl $0x2,%rax 
   (cons #x4010cd #xc1) ;;  
   (cons #x4010ce #xe0) ;;  
   (cons #x4010cf #x02) ;;  
   (cons #x4010d0 #x48) ;; add %rdx,%rax 
   (cons #x4010d1 #x01) ;;  
   (cons #x4010d2 #xd0) ;;  
   (cons #x4010d3 #xc7) ;; movl $0x1,(%rax) 
   (cons #x4010d4 #x00) ;;  
   (cons #x4010d5 #x01) ;;  
   (cons #x4010d6 #x00) ;;  
   (cons #x4010d7 #x00) ;;  
   (cons #x4010d8 #x00) ;;  
   (cons #x4010d9 #x48) ;; subq $0x4,-0x20(%rbp) 
   (cons #x4010da #x83) ;;  
   (cons #x4010db #x6d) ;;  
   (cons #x4010dc #xe0) ;;  
   (cons #x4010dd #x04) ;;  
   (cons #x4010de #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4010df #x8b) ;;  
   (cons #x4010e0 #x45) ;;  
   (cons #x4010e1 #xb8) ;;  
   (cons #x4010e2 #x48) ;; mov 0x70(%rax),%rax 
   (cons #x4010e3 #x8b) ;;  
   (cons #x4010e4 #x40) ;;  
   (cons #x4010e5 #x70) ;;  
   (cons #x4010e6 #x48) ;; cmp -0x20(%rbp),%rax 
   (cons #x4010e7 #x3b) ;;  
   (cons #x4010e8 #x45) ;;  
   (cons #x4010e9 #xe0) ;;  
   (cons #x4010ea #x0f) ;; jbe 40103b <analyze+0x411> 
   (cons #x4010eb #x86) ;;  
   (cons #x4010ec #x4b) ;;  
   (cons #x4010ed #xff) ;;  
   (cons #x4010ee #xff) ;;  
   (cons #x4010ef #xff) ;;  
   (cons #x4010f0 #xe9) ;; jmpq 4011ae <analyze+0x584> 
   (cons #x4010f1 #xb9) ;;  
   (cons #x4010f2 #x00) ;;  
   (cons #x4010f3 #x00) ;;  
   (cons #x4010f4 #x00) ;;  
   (cons #x4010f5 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4010f6 #x8b) ;;  
   (cons #x4010f7 #x45) ;;  
   (cons #x4010f8 #xb8) ;;  
   (cons #x4010f9 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4010fa #x8b) ;;  
   (cons #x4010fb #x80) ;;  
   (cons #x4010fc #x80) ;;  
   (cons #x4010fd #x00) ;;  
   (cons #x4010fe #x00) ;;  
   (cons #x4010ff #x00) ;;  
   (cons #x401100 #x8b) ;; mov (%rax),%edx 
   (cons #x401101 #x10) ;;  
   (cons #x401102 #x89) ;; mov %edx,-0x8(%rbp) 
   (cons #x401103 #x55) ;;  
   (cons #x401104 #xf8) ;;  
   (cons #x401105 #x48) ;; lea -0x4(%rax),%rdx 
   (cons #x401106 #x8d) ;;  
   (cons #x401107 #x50) ;;  
   (cons #x401108 #xfc) ;;  
   (cons #x401109 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40110a #x8b) ;;  
   (cons #x40110b #x45) ;;  
   (cons #x40110c #xb8) ;;  
   (cons #x40110d #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x40110e #x89) ;;  
   (cons #x40110f #x90) ;;  
   (cons #x401110 #x80) ;;  
   (cons #x401111 #x00) ;;  
   (cons #x401112 #x00) ;;  
   (cons #x401113 #x00) ;;  
   (cons #x401114 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401115 #x8b) ;;  
   (cons #x401116 #x45) ;;  
   (cons #x401117 #xb8) ;;  
   (cons #x401118 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401119 #x8b) ;;  
   (cons #x40111a #x40) ;;  
   (cons #x40111b #x40) ;;  
   (cons #x40111c #x8b) ;; mov -0x8(%rbp),%edx 
   (cons #x40111d #x55) ;;  
   (cons #x40111e #xf8) ;;  
   (cons #x40111f #x48) ;; movslq %edx,%rdx 
   (cons #x401120 #x63) ;;  
   (cons #x401121 #xd2) ;;  
   (cons #x401122 #x48) ;; shl $0x2,%rdx 
   (cons #x401123 #xc1) ;;  
   (cons #x401124 #xe2) ;;  
   (cons #x401125 #x02) ;;  
   (cons #x401126 #x48) ;; add %rdx,%rax 
   (cons #x401127 #x01) ;;  
   (cons #x401128 #xd0) ;;  
   (cons #x401129 #xc7) ;; movl $0x0,(%rax) 
   (cons #x40112a #x00) ;;  
   (cons #x40112b #x00) ;;  
   (cons #x40112c #x00) ;;  
   (cons #x40112d #x00) ;;  
   (cons #x40112e #x00) ;;  
   (cons #x40112f #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401130 #x8b) ;;  
   (cons #x401131 #x45) ;;  
   (cons #x401132 #xb8) ;;  
   (cons #x401133 #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x401134 #x8b) ;;  
   (cons #x401135 #x48) ;;  
   (cons #x401136 #x60) ;;  
   (cons #x401137 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x401138 #x45) ;;  
   (cons #x401139 #xf8) ;;  
   (cons #x40113a #x89) ;; mov %eax,%edx 
   (cons #x40113b #xc2) ;;  
   (cons #x40113c #xc1) ;; sar $0x1f,%edx 
   (cons #x40113d #xfa) ;;  
   (cons #x40113e #x1f) ;;  
   (cons #x40113f #x89) ;; mov %edx,%eax 
   (cons #x401140 #xd0) ;;  
   (cons #x401141 #x33) ;; xor -0x8(%rbp),%eax 
   (cons #x401142 #x45) ;;  
   (cons #x401143 #xf8) ;;  
   (cons #x401144 #x29) ;; sub %edx,%eax 
   (cons #x401145 #xd0) ;;  
   (cons #x401146 #x48) ;; cltq 
   (cons #x401147 #x98) ;;  
   (cons #x401148 #x48) ;; shl $0x2,%rax 
   (cons #x401149 #xc1) ;;  
   (cons #x40114a #xe0) ;;  
   (cons #x40114b #x02) ;;  
   (cons #x40114c #x48) ;; add %rcx,%rax 
   (cons #x40114d #x01) ;;  
   (cons #x40114e #xc8) ;;  
   (cons #x40114f #x8b) ;; mov (%rax),%eax 
   (cons #x401150 #x00) ;;  
   (cons #x401151 #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x401152 #xf8) ;;  
   (cons #x401153 #xf7) ;;  
   (cons #x401154 #x75) ;; jne 4011ae <analyze+0x584> 
   (cons #x401155 #x58) ;;  
   (cons #x401156 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401157 #x8b) ;;  
   (cons #x401158 #x45) ;;  
   (cons #x401159 #xb8) ;;  
   (cons #x40115a #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x40115b #x8b) ;;  
   (cons #x40115c #x48) ;;  
   (cons #x40115d #x60) ;;  
   (cons #x40115e #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x40115f #x45) ;;  
   (cons #x401160 #xf8) ;;  
   (cons #x401161 #x89) ;; mov %eax,%edx 
   (cons #x401162 #xc2) ;;  
   (cons #x401163 #xc1) ;; sar $0x1f,%edx 
   (cons #x401164 #xfa) ;;  
   (cons #x401165 #x1f) ;;  
   (cons #x401166 #x89) ;; mov %edx,%eax 
   (cons #x401167 #xd0) ;;  
   (cons #x401168 #x33) ;; xor -0x8(%rbp),%eax 
   (cons #x401169 #x45) ;;  
   (cons #x40116a #xf8) ;;  
   (cons #x40116b #x29) ;; sub %edx,%eax 
   (cons #x40116c #xd0) ;;  
   (cons #x40116d #x48) ;; cltq 
   (cons #x40116e #x98) ;;  
   (cons #x40116f #x48) ;; shl $0x2,%rax 
   (cons #x401170 #xc1) ;;  
   (cons #x401171 #xe0) ;;  
   (cons #x401172 #x02) ;;  
   (cons #x401173 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401174 #x8d) ;;  
   (cons #x401175 #x14) ;;  
   (cons #x401176 #x01) ;;  
   (cons #x401177 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401178 #x8b) ;;  
   (cons #x401179 #x45) ;;  
   (cons #x40117a #xb8) ;;  
   (cons #x40117b #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x40117c #x40) ;;  
   (cons #x40117d #x58) ;;  
   (cons #x40117e #x8d) ;; lea 0x1(%rax),%ecx 
   (cons #x40117f #x48) ;;  
   (cons #x401180 #x01) ;;  
   (cons #x401181 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401182 #x8b) ;;  
   (cons #x401183 #x45) ;;  
   (cons #x401184 #xb8) ;;  
   (cons #x401185 #x89) ;; mov %ecx,0x58(%rax) 
   (cons #x401186 #x48) ;;  
   (cons #x401187 #x58) ;;  
   (cons #x401188 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401189 #x8b) ;;  
   (cons #x40118a #x45) ;;  
   (cons #x40118b #xb8) ;;  
   (cons #x40118c #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x40118d #x40) ;;  
   (cons #x40118e #x58) ;;  
   (cons #x40118f #x89) ;; mov %eax,(%rdx) 
   (cons #x401190 #x02) ;;  
   (cons #x401191 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x401192 #x45) ;;  
   (cons #x401193 #xf8) ;;  
   (cons #x401194 #x89) ;; mov %eax,%edx 
   (cons #x401195 #xc2) ;;  
   (cons #x401196 #xc1) ;; sar $0x1f,%edx 
   (cons #x401197 #xfa) ;;  
   (cons #x401198 #x1f) ;;  
   (cons #x401199 #x89) ;; mov %edx,%eax 
   (cons #x40119a #xd0) ;;  
   (cons #x40119b #x33) ;; xor -0x8(%rbp),%eax 
   (cons #x40119c #x45) ;;  
   (cons #x40119d #xf8) ;;  
   (cons #x40119e #x29) ;; sub %edx,%eax 
   (cons #x40119f #xd0) ;;  
   (cons #x4011a0 #x48) ;; mov -0x48(%rbp),%rdx 
   (cons #x4011a1 #x8b) ;;  
   (cons #x4011a2 #x55) ;;  
   (cons #x4011a3 #xb8) ;;  
   (cons #x4011a4 #x89) ;; mov %eax,%esi 
   (cons #x4011a5 #xc6) ;;  
   (cons #x4011a6 #x48) ;; mov %rdx,%rdi 
   (cons #x4011a7 #x89) ;;  
   (cons #x4011a8 #xd7) ;;  
   (cons #x4011a9 #xe8) ;; callq 4009cb <heapUp> 
   (cons #x4011aa #x1d) ;;  
   (cons #x4011ab #xf8) ;;  
   (cons #x4011ac #xff) ;;  
   (cons #x4011ad #xff) ;;  
   (cons #x4011ae #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4011af #x8b) ;;  
   (cons #x4011b0 #x45) ;;  
   (cons #x4011b1 #xb8) ;;  
   (cons #x4011b2 #x48) ;; mov 0x80(%rax),%rdx 
   (cons #x4011b3 #x8b) ;;  
   (cons #x4011b4 #x90) ;;  
   (cons #x4011b5 #x80) ;;  
   (cons #x4011b6 #x00) ;;  
   (cons #x4011b7 #x00) ;;  
   (cons #x4011b8 #x00) ;;  
   (cons #x4011b9 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4011ba #x8b) ;;  
   (cons #x4011bb #x45) ;;  
   (cons #x4011bc #xb8) ;;  
   (cons #x4011bd #x48) ;; mov 0x78(%rax),%rax 
   (cons #x4011be #x8b) ;;  
   (cons #x4011bf #x40) ;;  
   (cons #x4011c0 #x78) ;;  
   (cons #x4011c1 #x48) ;; cmp %rax,%rdx 
   (cons #x4011c2 #x39) ;;  
   (cons #x4011c3 #xc2) ;;  
   (cons #x4011c4 #x0f) ;; ja 4010f5 <analyze+0x4cb> 
   (cons #x4011c5 #x87) ;;  
   (cons #x4011c6 #x2b) ;;  
   (cons #x4011c7 #xff) ;;  
   (cons #x4011c8 #xff) ;;  
   (cons #x4011c9 #xff) ;;  
   (cons #x4011ca #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4011cb #x8b) ;;  
   (cons #x4011cc #x45) ;;  
   (cons #x4011cd #xb8) ;;  
   (cons #x4011ce #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4011cf #x8b) ;;  
   (cons #x4011d0 #x80) ;;  
   (cons #x4011d1 #x80) ;;  
   (cons #x4011d2 #x00) ;;  
   (cons #x4011d3 #x00) ;;  
   (cons #x4011d4 #x00) ;;  
   (cons #x4011d5 #x8b) ;; mov (%rax),%eax 
   (cons #x4011d6 #x00) ;;  
   (cons #x4011d7 #x89) ;; mov %eax,-0x4(%rbp) 
   (cons #x4011d8 #x45) ;;  
   (cons #x4011d9 #xfc) ;;  
   (cons #x4011da #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4011db #x8b) ;;  
   (cons #x4011dc #x45) ;;  
   (cons #x4011dd #xb8) ;;  
   (cons #x4011de #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4011df #x8b) ;;  
   (cons #x4011e0 #x40) ;;  
   (cons #x4011e1 #x40) ;;  
   (cons #x4011e2 #x8b) ;; mov -0x4(%rbp),%edx 
   (cons #x4011e3 #x55) ;;  
   (cons #x4011e4 #xfc) ;;  
   (cons #x4011e5 #x48) ;; movslq %edx,%rdx 
   (cons #x4011e6 #x63) ;;  
   (cons #x4011e7 #xd2) ;;  
   (cons #x4011e8 #x48) ;; shl $0x2,%rdx 
   (cons #x4011e9 #xc1) ;;  
   (cons #x4011ea #xe2) ;;  
   (cons #x4011eb #x02) ;;  
   (cons #x4011ec #x48) ;; add %rdx,%rax 
   (cons #x4011ed #x01) ;;  
   (cons #x4011ee #xd0) ;;  
   (cons #x4011ef #xc7) ;; movl $0x0,(%rax) 
   (cons #x4011f0 #x00) ;;  
   (cons #x4011f1 #x00) ;;  
   (cons #x4011f2 #x00) ;;  
   (cons #x4011f3 #x00) ;;  
   (cons #x4011f4 #x00) ;;  
   (cons #x4011f5 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4011f6 #x8b) ;;  
   (cons #x4011f7 #x45) ;;  
   (cons #x4011f8 #xb8) ;;  
   (cons #x4011f9 #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x4011fa #x8b) ;;  
   (cons #x4011fb #x48) ;;  
   (cons #x4011fc #x60) ;;  
   (cons #x4011fd #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x4011fe #x45) ;;  
   (cons #x4011ff #xfc) ;;  
   (cons #x401200 #x89) ;; mov %eax,%edx 
   (cons #x401201 #xc2) ;;  
   (cons #x401202 #xc1) ;; sar $0x1f,%edx 
   (cons #x401203 #xfa) ;;  
   (cons #x401204 #x1f) ;;  
   (cons #x401205 #x89) ;; mov %edx,%eax 
   (cons #x401206 #xd0) ;;  
   (cons #x401207 #x33) ;; xor -0x4(%rbp),%eax 
   (cons #x401208 #x45) ;;  
   (cons #x401209 #xfc) ;;  
   (cons #x40120a #x29) ;; sub %edx,%eax 
   (cons #x40120b #xd0) ;;  
   (cons #x40120c #x48) ;; cltq 
   (cons #x40120d #x98) ;;  
   (cons #x40120e #x48) ;; shl $0x2,%rax 
   (cons #x40120f #xc1) ;;  
   (cons #x401210 #xe0) ;;  
   (cons #x401211 #x02) ;;  
   (cons #x401212 #x48) ;; add %rcx,%rax 
   (cons #x401213 #x01) ;;  
   (cons #x401214 #xc8) ;;  
   (cons #x401215 #x8b) ;; mov (%rax),%eax 
   (cons #x401216 #x00) ;;  
   (cons #x401217 #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x401218 #xf8) ;;  
   (cons #x401219 #xf7) ;;  
   (cons #x40121a #x75) ;; jne 401274 <analyze+0x64a> 
   (cons #x40121b #x58) ;;  
   (cons #x40121c #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40121d #x8b) ;;  
   (cons #x40121e #x45) ;;  
   (cons #x40121f #xb8) ;;  
   (cons #x401220 #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x401221 #x8b) ;;  
   (cons #x401222 #x48) ;;  
   (cons #x401223 #x60) ;;  
   (cons #x401224 #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x401225 #x45) ;;  
   (cons #x401226 #xfc) ;;  
   (cons #x401227 #x89) ;; mov %eax,%edx 
   (cons #x401228 #xc2) ;;  
   (cons #x401229 #xc1) ;; sar $0x1f,%edx 
   (cons #x40122a #xfa) ;;  
   (cons #x40122b #x1f) ;;  
   (cons #x40122c #x89) ;; mov %edx,%eax 
   (cons #x40122d #xd0) ;;  
   (cons #x40122e #x33) ;; xor -0x4(%rbp),%eax 
   (cons #x40122f #x45) ;;  
   (cons #x401230 #xfc) ;;  
   (cons #x401231 #x29) ;; sub %edx,%eax 
   (cons #x401232 #xd0) ;;  
   (cons #x401233 #x48) ;; cltq 
   (cons #x401234 #x98) ;;  
   (cons #x401235 #x48) ;; shl $0x2,%rax 
   (cons #x401236 #xc1) ;;  
   (cons #x401237 #xe0) ;;  
   (cons #x401238 #x02) ;;  
   (cons #x401239 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40123a #x8d) ;;  
   (cons #x40123b #x14) ;;  
   (cons #x40123c #x01) ;;  
   (cons #x40123d #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40123e #x8b) ;;  
   (cons #x40123f #x45) ;;  
   (cons #x401240 #xb8) ;;  
   (cons #x401241 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x401242 #x40) ;;  
   (cons #x401243 #x58) ;;  
   (cons #x401244 #x8d) ;; lea 0x1(%rax),%ecx 
   (cons #x401245 #x48) ;;  
   (cons #x401246 #x01) ;;  
   (cons #x401247 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401248 #x8b) ;;  
   (cons #x401249 #x45) ;;  
   (cons #x40124a #xb8) ;;  
   (cons #x40124b #x89) ;; mov %ecx,0x58(%rax) 
   (cons #x40124c #x48) ;;  
   (cons #x40124d #x58) ;;  
   (cons #x40124e #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40124f #x8b) ;;  
   (cons #x401250 #x45) ;;  
   (cons #x401251 #xb8) ;;  
   (cons #x401252 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x401253 #x40) ;;  
   (cons #x401254 #x58) ;;  
   (cons #x401255 #x89) ;; mov %eax,(%rdx) 
   (cons #x401256 #x02) ;;  
   (cons #x401257 #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x401258 #x45) ;;  
   (cons #x401259 #xfc) ;;  
   (cons #x40125a #x89) ;; mov %eax,%edx 
   (cons #x40125b #xc2) ;;  
   (cons #x40125c #xc1) ;; sar $0x1f,%edx 
   (cons #x40125d #xfa) ;;  
   (cons #x40125e #x1f) ;;  
   (cons #x40125f #x89) ;; mov %edx,%eax 
   (cons #x401260 #xd0) ;;  
   (cons #x401261 #x33) ;; xor -0x4(%rbp),%eax 
   (cons #x401262 #x45) ;;  
   (cons #x401263 #xfc) ;;  
   (cons #x401264 #x29) ;; sub %edx,%eax 
   (cons #x401265 #xd0) ;;  
   (cons #x401266 #x48) ;; mov -0x48(%rbp),%rdx 
   (cons #x401267 #x8b) ;;  
   (cons #x401268 #x55) ;;  
   (cons #x401269 #xb8) ;;  
   (cons #x40126a #x89) ;; mov %eax,%esi 
   (cons #x40126b #xc6) ;;  
   (cons #x40126c #x48) ;; mov %rdx,%rdi 
   (cons #x40126d #x89) ;;  
   (cons #x40126e #xd7) ;;  
   (cons #x40126f #xe8) ;; callq 4009cb <heapUp> 
   (cons #x401270 #x57) ;;  
   (cons #x401271 #xf7) ;;  
   (cons #x401272 #xff) ;;  
   (cons #x401273 #xff) ;;  
   (cons #x401274 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x401275 #x55) ;;  
   (cons #x401276 #xe8) ;;  
   (cons #x401277 #x48) ;; lea -0x40(%rbp),%rcx 
   (cons #x401278 #x8d) ;;  
   (cons #x401279 #x4d) ;;  
   (cons #x40127a #xc0) ;;  
   (cons #x40127b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40127c #x8b) ;;  
   (cons #x40127d #x45) ;;  
   (cons #x40127e #xb8) ;;  
   (cons #x40127f #x48) ;; mov %rcx,%rsi 
   (cons #x401280 #x89) ;;  
   (cons #x401281 #xce) ;;  
   (cons #x401282 #x48) ;; mov %rax,%rdi 
   (cons #x401283 #x89) ;;  
   (cons #x401284 #xc7) ;;  
   (cons #x401285 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x401286 #x69) ;;  
   (cons #x401287 #xf2) ;;  
   (cons #x401288 #xff) ;;  
   (cons #x401289 #xff) ;;  
   (cons #x40128a #xc9) ;; leaveq 
   (cons #x40128b #xc3) ;; retq 
   
;; Section: <propagate>:


   (cons #x40128c #x55) ;; push %rbp 
   (cons #x40128d #x48) ;; mov %rsp,%rbp 
   (cons #x40128e #x89) ;;  
   (cons #x40128f #xe5) ;;  
   (cons #x401290 #x53) ;; push %rbx 
   (cons #x401291 #x48) ;; sub $0x48,%rsp 
   (cons #x401292 #x83) ;;  
   (cons #x401293 #xec) ;;  
   (cons #x401294 #x48) ;;  
   (cons #x401295 #x48) ;; mov %rdi,-0x48(%rbp) 
   (cons #x401296 #x89) ;;  
   (cons #x401297 #x7d) ;;  
   (cons #x401298 #xb8) ;;  
   (cons #x401299 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40129a #x8b) ;;  
   (cons #x40129b #x45) ;;  
   (cons #x40129c #xb8) ;;  
   (cons #x40129d #x48) ;; mov 0x78(%rax),%rax 
   (cons #x40129e #x8b) ;;  
   (cons #x40129f #x40) ;;  
   (cons #x4012a0 #x78) ;;  
   (cons #x4012a1 #x8b) ;; mov (%rax),%eax 
   (cons #x4012a2 #x00) ;;  
   (cons #x4012a3 #x89) ;; mov %eax,-0x20(%rbp) 
   (cons #x4012a4 #x45) ;;  
   (cons #x4012a5 #xe0) ;;  
   (cons #x4012a6 #x8b) ;; mov -0x20(%rbp),%eax 
   (cons #x4012a7 #x45) ;;  
   (cons #x4012a8 #xe0) ;;  
   (cons #x4012a9 #xc1) ;; sar $0x1f,%eax 
   (cons #x4012aa #xf8) ;;  
   (cons #x4012ab #x1f) ;;  
   (cons #x4012ac #x89) ;; mov %eax,%edx 
   (cons #x4012ad #xc2) ;;  
   (cons #x4012ae #x33) ;; xor -0x20(%rbp),%edx 
   (cons #x4012af #x55) ;;  
   (cons #x4012b0 #xe0) ;;  
   (cons #x4012b1 #x89) ;; mov %edx,-0x1c(%rbp) 
   (cons #x4012b2 #x55) ;;  
   (cons #x4012b3 #xe4) ;;  
   (cons #x4012b4 #x29) ;; sub %eax,-0x1c(%rbp) 
   (cons #x4012b5 #x45) ;;  
   (cons #x4012b6 #xe4) ;;  
   (cons #x4012b7 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4012b8 #x8b) ;;  
   (cons #x4012b9 #x45) ;;  
   (cons #x4012ba #xb8) ;;  
   (cons #x4012bb #x48) ;; mov 0x30(%rax),%rax 
   (cons #x4012bc #x8b) ;;  
   (cons #x4012bd #x40) ;;  
   (cons #x4012be #x30) ;;  
   (cons #x4012bf #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x4012c0 #x55) ;;  
   (cons #x4012c1 #xe4) ;;  
   (cons #x4012c2 #x48) ;; movslq %edx,%rdx 
   (cons #x4012c3 #x63) ;;  
   (cons #x4012c4 #xd2) ;;  
   (cons #x4012c5 #x48) ;; shl $0x2,%rdx 
   (cons #x4012c6 #xc1) ;;  
   (cons #x4012c7 #xe2) ;;  
   (cons #x4012c8 #x02) ;;  
   (cons #x4012c9 #x48) ;; add %rdx,%rax 
   (cons #x4012ca #x01) ;;  
   (cons #x4012cb #xd0) ;;  
   (cons #x4012cc #x8b) ;; mov (%rax),%eax 
   (cons #x4012cd #x00) ;;  
   (cons #x4012ce #x89) ;; mov %eax,-0x28(%rbp) 
   (cons #x4012cf #x45) ;;  
   (cons #x4012d0 #xd8) ;;  
   (cons #x4012d1 #xe9) ;; jmpq 401689 <propagate+0x3fd> 
   (cons #x4012d2 #xb3) ;;  
   (cons #x4012d3 #x03) ;;  
   (cons #x4012d4 #x00) ;;  
   (cons #x4012d5 #x00) ;;  
   (cons #x4012d6 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4012d7 #x8b) ;;  
   (cons #x4012d8 #x45) ;;  
   (cons #x4012d9 #xb8) ;;  
   (cons #x4012da #x48) ;; mov 0x78(%rax),%rax 
   (cons #x4012db #x8b) ;;  
   (cons #x4012dc #x40) ;;  
   (cons #x4012dd #x78) ;;  
   (cons #x4012de #x8b) ;; mov (%rax),%edx 
   (cons #x4012df #x10) ;;  
   (cons #x4012e0 #x89) ;; mov %edx,-0x18(%rbp) 
   (cons #x4012e1 #x55) ;;  
   (cons #x4012e2 #xe8) ;;  
   (cons #x4012e3 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4012e4 #x8d) ;;  
   (cons #x4012e5 #x50) ;;  
   (cons #x4012e6 #x04) ;;  
   (cons #x4012e7 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4012e8 #x8b) ;;  
   (cons #x4012e9 #x45) ;;  
   (cons #x4012ea #xb8) ;;  
   (cons #x4012eb #x48) ;; mov %rdx,0x78(%rax) 
   (cons #x4012ec #x89) ;;  
   (cons #x4012ed #x50) ;;  
   (cons #x4012ee #x78) ;;  
   (cons #x4012ef #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4012f0 #x8b) ;;  
   (cons #x4012f1 #x45) ;;  
   (cons #x4012f2 #xb8) ;;  
   (cons #x4012f3 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x4012f4 #x8b) ;;  
   (cons #x4012f5 #x40) ;;  
   (cons #x4012f6 #x48) ;;  
   (cons #x4012f7 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x4012f8 #x55) ;;  
   (cons #x4012f9 #xe8) ;;  
   (cons #x4012fa #x48) ;; movslq %edx,%rdx 
   (cons #x4012fb #x63) ;;  
   (cons #x4012fc #xd2) ;;  
   (cons #x4012fd #x48) ;; shl $0x2,%rdx 
   (cons #x4012fe #xc1) ;;  
   (cons #x4012ff #xe2) ;;  
   (cons #x401300 #x02) ;;  
   (cons #x401301 #x48) ;; add %rdx,%rax 
   (cons #x401302 #x01) ;;  
   (cons #x401303 #xd0) ;;  
   (cons #x401304 #x48) ;; mov %rax,-0x40(%rbp) 
   (cons #x401305 #x89) ;;  
   (cons #x401306 #x45) ;;  
   (cons #x401307 #xc0) ;;  
   (cons #x401308 #xe9) ;; jmpq 40167a <propagate+0x3ee> 
   (cons #x401309 #x6d) ;;  
   (cons #x40130a #x03) ;;  
   (cons #x40130b #x00) ;;  
   (cons #x40130c #x00) ;;  
   (cons #x40130d #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40130e #x8b) ;;  
   (cons #x40130f #x45) ;;  
   (cons #x401310 #xb8) ;;  
   (cons #x401311 #x48) ;; mov (%rax),%rdx 
   (cons #x401312 #x8b) ;;  
   (cons #x401313 #x10) ;;  
   (cons #x401314 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401315 #x8b) ;;  
   (cons #x401316 #x45) ;;  
   (cons #x401317 #xc0) ;;  
   (cons #x401318 #x8b) ;; mov (%rax),%eax 
   (cons #x401319 #x00) ;;  
   (cons #x40131a #x48) ;; cltq 
   (cons #x40131b #x98) ;;  
   (cons #x40131c #x48) ;; add $0x1,%rax 
   (cons #x40131d #x83) ;;  
   (cons #x40131e #xc0) ;;  
   (cons #x40131f #x01) ;;  
   (cons #x401320 #x48) ;; shl $0x2,%rax 
   (cons #x401321 #xc1) ;;  
   (cons #x401322 #xe0) ;;  
   (cons #x401323 #x02) ;;  
   (cons #x401324 #x48) ;; add %rdx,%rax 
   (cons #x401325 #x01) ;;  
   (cons #x401326 #xd0) ;;  
   (cons #x401327 #x48) ;; mov %rax,-0x38(%rbp) 
   (cons #x401328 #x89) ;;  
   (cons #x401329 #x45) ;;  
   (cons #x40132a #xc8) ;;  
   (cons #x40132b #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40132c #x8b) ;;  
   (cons #x40132d #x45) ;;  
   (cons #x40132e #xc8) ;;  
   (cons #x40132f #x48) ;; sub $0x8,%rax 
   (cons #x401330 #x83) ;;  
   (cons #x401331 #xe8) ;;  
   (cons #x401332 #x08) ;;  
   (cons #x401333 #x8b) ;; mov (%rax),%eax 
   (cons #x401334 #x00) ;;  
   (cons #x401335 #x85) ;; test %eax,%eax 
   (cons #x401336 #xc0) ;;  
   (cons #x401337 #x75) ;; jne 40133e <propagate+0xb2> 
   (cons #x401338 #x05) ;;  
   (cons #x401339 #x48) ;; addq $0x4,-0x38(%rbp) 
   (cons #x40133a #x83) ;;  
   (cons #x40133b #x45) ;;  
   (cons #x40133c #xc8) ;;  
   (cons #x40133d #x04) ;;  
   (cons #x40133e #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40133f #x8b) ;;  
   (cons #x401340 #x45) ;;  
   (cons #x401341 #xc8) ;;  
   (cons #x401342 #x8b) ;; mov (%rax),%eax 
   (cons #x401343 #x00) ;;  
   (cons #x401344 #x3b) ;; cmp -0x18(%rbp),%eax 
   (cons #x401345 #x45) ;;  
   (cons #x401346 #xe8) ;;  
   (cons #x401347 #x75) ;; jne 401356 <propagate+0xca> 
   (cons #x401348 #x0d) ;;  
   (cons #x401349 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40134a #x8b) ;;  
   (cons #x40134b #x45) ;;  
   (cons #x40134c #xc8) ;;  
   (cons #x40134d #x8b) ;; mov 0x4(%rax),%edx 
   (cons #x40134e #x50) ;;  
   (cons #x40134f #x04) ;;  
   (cons #x401350 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x401351 #x8b) ;;  
   (cons #x401352 #x45) ;;  
   (cons #x401353 #xc8) ;;  
   (cons #x401354 #x89) ;; mov %edx,(%rax) 
   (cons #x401355 #x10) ;;  
   (cons #x401356 #xc7) ;; movl $0x2,-0x24(%rbp) 
   (cons #x401357 #x45) ;;  
   (cons #x401358 #xdc) ;;  
   (cons #x401359 #x02) ;;  
   (cons #x40135a #x00) ;;  
   (cons #x40135b #x00) ;;  
   (cons #x40135c #x00) ;;  
   (cons #x40135d #xe9) ;; jmpq 40143c <propagate+0x1b0> 
   (cons #x40135e #xda) ;;  
   (cons #x40135f #x00) ;;  
   (cons #x401360 #x00) ;;  
   (cons #x401361 #x00) ;;  
   (cons #x401362 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401363 #x8b) ;;  
   (cons #x401364 #x45) ;;  
   (cons #x401365 #xb8) ;;  
   (cons #x401366 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x401367 #x8b) ;;  
   (cons #x401368 #x50) ;;  
   (cons #x401369 #x40) ;;  
   (cons #x40136a #x8b) ;; mov -0x24(%rbp),%eax 
   (cons #x40136b #x45) ;;  
   (cons #x40136c #xdc) ;;  
   (cons #x40136d #x48) ;; cltq 
   (cons #x40136e #x98) ;;  
   (cons #x40136f #x48) ;; shl $0x2,%rax 
   (cons #x401370 #xc1) ;;  
   (cons #x401371 #xe0) ;;  
   (cons #x401372 #x02) ;;  
   (cons #x401373 #x48) ;; add -0x38(%rbp),%rax 
   (cons #x401374 #x03) ;;  
   (cons #x401375 #x45) ;;  
   (cons #x401376 #xc8) ;;  
   (cons #x401377 #x8b) ;; mov (%rax),%eax 
   (cons #x401378 #x00) ;;  
   (cons #x401379 #x48) ;; cltq 
   (cons #x40137a #x98) ;;  
   (cons #x40137b #x48) ;; shl $0x2,%rax 
   (cons #x40137c #xc1) ;;  
   (cons #x40137d #xe0) ;;  
   (cons #x40137e #x02) ;;  
   (cons #x40137f #x48) ;; add %rdx,%rax 
   (cons #x401380 #x01) ;;  
   (cons #x401381 #xd0) ;;  
   (cons #x401382 #x8b) ;; mov (%rax),%eax 
   (cons #x401383 #x00) ;;  
   (cons #x401384 #x85) ;; test %eax,%eax 
   (cons #x401385 #xc0) ;;  
   (cons #x401386 #x0f) ;; jne 401438 <propagate+0x1ac> 
   (cons #x401387 #x85) ;;  
   (cons #x401388 #xac) ;;  
   (cons #x401389 #x00) ;;  
   (cons #x40138a #x00) ;;  
   (cons #x40138b #x00) ;;  
   (cons #x40138c #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40138d #x8b) ;;  
   (cons #x40138e #x45) ;;  
   (cons #x40138f #xc8) ;;  
   (cons #x401390 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x401391 #x8d) ;;  
   (cons #x401392 #x50) ;;  
   (cons #x401393 #x04) ;;  
   (cons #x401394 #x8b) ;; mov -0x24(%rbp),%eax 
   (cons #x401395 #x45) ;;  
   (cons #x401396 #xdc) ;;  
   (cons #x401397 #x48) ;; cltq 
   (cons #x401398 #x98) ;;  
   (cons #x401399 #x48) ;; shl $0x2,%rax 
   (cons #x40139a #xc1) ;;  
   (cons #x40139b #xe0) ;;  
   (cons #x40139c #x02) ;;  
   (cons #x40139d #x48) ;; add -0x38(%rbp),%rax 
   (cons #x40139e #x03) ;;  
   (cons #x40139f #x45) ;;  
   (cons #x4013a0 #xc8) ;;  
   (cons #x4013a1 #x8b) ;; mov (%rax),%eax 
   (cons #x4013a2 #x00) ;;  
   (cons #x4013a3 #x89) ;; mov %eax,(%rdx) 
   (cons #x4013a4 #x02) ;;  
   (cons #x4013a5 #x8b) ;; mov -0x24(%rbp),%eax 
   (cons #x4013a6 #x45) ;;  
   (cons #x4013a7 #xdc) ;;  
   (cons #x4013a8 #x48) ;; cltq 
   (cons #x4013a9 #x98) ;;  
   (cons #x4013aa #x48) ;; shl $0x2,%rax 
   (cons #x4013ab #xc1) ;;  
   (cons #x4013ac #xe0) ;;  
   (cons #x4013ad #x02) ;;  
   (cons #x4013ae #x48) ;; add -0x38(%rbp),%rax 
   (cons #x4013af #x03) ;;  
   (cons #x4013b0 #x45) ;;  
   (cons #x4013b1 #xc8) ;;  
   (cons #x4013b2 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x4013b3 #x55) ;;  
   (cons #x4013b4 #xe8) ;;  
   (cons #x4013b5 #x89) ;; mov %edx,(%rax) 
   (cons #x4013b6 #x10) ;;  
   (cons #x4013b7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4013b8 #x8b) ;;  
   (cons #x4013b9 #x45) ;;  
   (cons #x4013ba #xc0) ;;  
   (cons #x4013bb #x8b) ;; mov (%rax),%eax 
   (cons #x4013bc #x00) ;;  
   (cons #x4013bd #x89) ;; mov %eax,-0x14(%rbp) 
   (cons #x4013be #x45) ;;  
   (cons #x4013bf #xec) ;;  
   (cons #x4013c0 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4013c1 #x8b) ;;  
   (cons #x4013c2 #x45) ;;  
   (cons #x4013c3 #xb8) ;;  
   (cons #x4013c4 #x48) ;; mov (%rax),%rdx 
   (cons #x4013c5 #x8b) ;;  
   (cons #x4013c6 #x10) ;;  
   (cons #x4013c7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4013c8 #x8b) ;;  
   (cons #x4013c9 #x45) ;;  
   (cons #x4013ca #xc0) ;;  
   (cons #x4013cb #x8b) ;; mov (%rax),%eax 
   (cons #x4013cc #x00) ;;  
   (cons #x4013cd #x48) ;; cltq 
   (cons #x4013ce #x98) ;;  
   (cons #x4013cf #x48) ;; shl $0x2,%rax 
   (cons #x4013d0 #xc1) ;;  
   (cons #x4013d1 #xe0) ;;  
   (cons #x4013d2 #x02) ;;  
   (cons #x4013d3 #x48) ;; add %rdx,%rax 
   (cons #x4013d4 #x01) ;;  
   (cons #x4013d5 #xd0) ;;  
   (cons #x4013d6 #x8b) ;; mov (%rax),%edx 
   (cons #x4013d7 #x10) ;;  
   (cons #x4013d8 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4013d9 #x8b) ;;  
   (cons #x4013da #x45) ;;  
   (cons #x4013db #xc0) ;;  
   (cons #x4013dc #x89) ;; mov %edx,(%rax) 
   (cons #x4013dd #x10) ;;  
   (cons #x4013de #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4013df #x8b) ;;  
   (cons #x4013e0 #x45) ;;  
   (cons #x4013e1 #xb8) ;;  
   (cons #x4013e2 #x48) ;; mov (%rax),%rax 
   (cons #x4013e3 #x8b) ;;  
   (cons #x4013e4 #x00) ;;  
   (cons #x4013e5 #x8b) ;; mov -0x14(%rbp),%edx 
   (cons #x4013e6 #x55) ;;  
   (cons #x4013e7 #xec) ;;  
   (cons #x4013e8 #x48) ;; movslq %edx,%rdx 
   (cons #x4013e9 #x63) ;;  
   (cons #x4013ea #xd2) ;;  
   (cons #x4013eb #x48) ;; shl $0x2,%rdx 
   (cons #x4013ec #xc1) ;;  
   (cons #x4013ed #xe2) ;;  
   (cons #x4013ee #x02) ;;  
   (cons #x4013ef #x48) ;; add %rax,%rdx 
   (cons #x4013f0 #x01) ;;  
   (cons #x4013f1 #xc2) ;;  
   (cons #x4013f2 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4013f3 #x8b) ;;  
   (cons #x4013f4 #x45) ;;  
   (cons #x4013f5 #xb8) ;;  
   (cons #x4013f6 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x4013f7 #x8b) ;;  
   (cons #x4013f8 #x40) ;;  
   (cons #x4013f9 #x48) ;;  
   (cons #x4013fa #x48) ;; mov -0x38(%rbp),%rcx 
   (cons #x4013fb #x8b) ;;  
   (cons #x4013fc #x4d) ;;  
   (cons #x4013fd #xc8) ;;  
   (cons #x4013fe #x48) ;; add $0x4,%rcx 
   (cons #x4013ff #x83) ;;  
   (cons #x401400 #xc1) ;;  
   (cons #x401401 #x04) ;;  
   (cons #x401402 #x8b) ;; mov (%rcx),%ecx 
   (cons #x401403 #x09) ;;  
   (cons #x401404 #x48) ;; movslq %ecx,%rcx 
   (cons #x401405 #x63) ;;  
   (cons #x401406 #xc9) ;;  
   (cons #x401407 #x48) ;; shl $0x2,%rcx 
   (cons #x401408 #xc1) ;;  
   (cons #x401409 #xe1) ;;  
   (cons #x40140a #x02) ;;  
   (cons #x40140b #x48) ;; add %rcx,%rax 
   (cons #x40140c #x01) ;;  
   (cons #x40140d #xc8) ;;  
   (cons #x40140e #x8b) ;; mov (%rax),%eax 
   (cons #x40140f #x00) ;;  
   (cons #x401410 #x89) ;; mov %eax,(%rdx) 
   (cons #x401411 #x02) ;;  
   (cons #x401412 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401413 #x8b) ;;  
   (cons #x401414 #x45) ;;  
   (cons #x401415 #xb8) ;;  
   (cons #x401416 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x401417 #x8b) ;;  
   (cons #x401418 #x40) ;;  
   (cons #x401419 #x48) ;;  
   (cons #x40141a #x48) ;; mov -0x38(%rbp),%rdx 
   (cons #x40141b #x8b) ;;  
   (cons #x40141c #x55) ;;  
   (cons #x40141d #xc8) ;;  
   (cons #x40141e #x48) ;; add $0x4,%rdx 
   (cons #x40141f #x83) ;;  
   (cons #x401420 #xc2) ;;  
   (cons #x401421 #x04) ;;  
   (cons #x401422 #x8b) ;; mov (%rdx),%edx 
   (cons #x401423 #x12) ;;  
   (cons #x401424 #x48) ;; movslq %edx,%rdx 
   (cons #x401425 #x63) ;;  
   (cons #x401426 #xd2) ;;  
   (cons #x401427 #x48) ;; shl $0x2,%rdx 
   (cons #x401428 #xc1) ;;  
   (cons #x401429 #xe2) ;;  
   (cons #x40142a #x02) ;;  
   (cons #x40142b #x48) ;; add %rax,%rdx 
   (cons #x40142c #x01) ;;  
   (cons #x40142d #xc2) ;;  
   (cons #x40142e #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x40142f #x45) ;;  
   (cons #x401430 #xec) ;;  
   (cons #x401431 #x89) ;; mov %eax,(%rdx) 
   (cons #x401432 #x02) ;;  
   (cons #x401433 #xe9) ;; jmpq 40167a <propagate+0x3ee> 
   (cons #x401434 #x42) ;;  
   (cons #x401435 #x02) ;;  
   (cons #x401436 #x00) ;;  
   (cons #x401437 #x00) ;;  
   (cons #x401438 #x83) ;; addl $0x1,-0x24(%rbp) 
   (cons #x401439 #x45) ;;  
   (cons #x40143a #xdc) ;;  
   (cons #x40143b #x01) ;;  
   (cons #x40143c #x8b) ;; mov -0x24(%rbp),%eax 
   (cons #x40143d #x45) ;;  
   (cons #x40143e #xdc) ;;  
   (cons #x40143f #x48) ;; cltq 
   (cons #x401440 #x98) ;;  
   (cons #x401441 #x48) ;; shl $0x2,%rax 
   (cons #x401442 #xc1) ;;  
   (cons #x401443 #xe0) ;;  
   (cons #x401444 #x02) ;;  
   (cons #x401445 #x48) ;; add -0x38(%rbp),%rax 
   (cons #x401446 #x03) ;;  
   (cons #x401447 #x45) ;;  
   (cons #x401448 #xc8) ;;  
   (cons #x401449 #x8b) ;; mov (%rax),%eax 
   (cons #x40144a #x00) ;;  
   (cons #x40144b #x85) ;; test %eax,%eax 
   (cons #x40144c #xc0) ;;  
   (cons #x40144d #x0f) ;; jne 401362 <propagate+0xd6> 
   (cons #x40144e #x85) ;;  
   (cons #x40144f #x0f) ;;  
   (cons #x401450 #xff) ;;  
   (cons #x401451 #xff) ;;  
   (cons #x401452 #xff) ;;  
   (cons #x401453 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x401454 #x8b) ;;  
   (cons #x401455 #x45) ;;  
   (cons #x401456 #xc8) ;;  
   (cons #x401457 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x401458 #x8d) ;;  
   (cons #x401459 #x50) ;;  
   (cons #x40145a #x04) ;;  
   (cons #x40145b #x8b) ;; mov -0x18(%rbp),%eax 
   (cons #x40145c #x45) ;;  
   (cons #x40145d #xe8) ;;  
   (cons #x40145e #x89) ;; mov %eax,(%rdx) 
   (cons #x40145f #x02) ;;  
   (cons #x401460 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401461 #x8b) ;;  
   (cons #x401462 #x45) ;;  
   (cons #x401463 #xb8) ;;  
   (cons #x401464 #x48) ;; mov (%rax),%rdx 
   (cons #x401465 #x8b) ;;  
   (cons #x401466 #x10) ;;  
   (cons #x401467 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401468 #x8b) ;;  
   (cons #x401469 #x45) ;;  
   (cons #x40146a #xc0) ;;  
   (cons #x40146b #x8b) ;; mov (%rax),%eax 
   (cons #x40146c #x00) ;;  
   (cons #x40146d #x48) ;; cltq 
   (cons #x40146e #x98) ;;  
   (cons #x40146f #x48) ;; shl $0x2,%rax 
   (cons #x401470 #xc1) ;;  
   (cons #x401471 #xe0) ;;  
   (cons #x401472 #x02) ;;  
   (cons #x401473 #x48) ;; add %rdx,%rax 
   (cons #x401474 #x01) ;;  
   (cons #x401475 #xd0) ;;  
   (cons #x401476 #x48) ;; mov %rax,-0x40(%rbp) 
   (cons #x401477 #x89) ;;  
   (cons #x401478 #x45) ;;  
   (cons #x401479 #xc0) ;;  
   (cons #x40147a #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40147b #x8b) ;;  
   (cons #x40147c #x45) ;;  
   (cons #x40147d #xb8) ;;  
   (cons #x40147e #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x40147f #x8b) ;;  
   (cons #x401480 #x50) ;;  
   (cons #x401481 #x40) ;;  
   (cons #x401482 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x401483 #x8b) ;;  
   (cons #x401484 #x45) ;;  
   (cons #x401485 #xc8) ;;  
   (cons #x401486 #x8b) ;; mov (%rax),%eax 
   (cons #x401487 #x00) ;;  
   (cons #x401488 #xf7) ;; neg %eax 
   (cons #x401489 #xd8) ;;  
   (cons #x40148a #x48) ;; cltq 
   (cons #x40148b #x98) ;;  
   (cons #x40148c #x48) ;; shl $0x2,%rax 
   (cons #x40148d #xc1) ;;  
   (cons #x40148e #xe0) ;;  
   (cons #x40148f #x02) ;;  
   (cons #x401490 #x48) ;; add %rdx,%rax 
   (cons #x401491 #x01) ;;  
   (cons #x401492 #xd0) ;;  
   (cons #x401493 #x8b) ;; mov (%rax),%eax 
   (cons #x401494 #x00) ;;  
   (cons #x401495 #x85) ;; test %eax,%eax 
   (cons #x401496 #xc0) ;;  
   (cons #x401497 #x0f) ;; jne 401679 <propagate+0x3ed> 
   (cons #x401498 #x85) ;;  
   (cons #x401499 #xdc) ;;  
   (cons #x40149a #x01) ;;  
   (cons #x40149b #x00) ;;  
   (cons #x40149c #x00) ;;  
   (cons #x40149d #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40149e #x8b) ;;  
   (cons #x40149f #x45) ;;  
   (cons #x4014a0 #xb8) ;;  
   (cons #x4014a1 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x4014a2 #x8b) ;;  
   (cons #x4014a3 #x50) ;;  
   (cons #x4014a4 #x40) ;;  
   (cons #x4014a5 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4014a6 #x8b) ;;  
   (cons #x4014a7 #x45) ;;  
   (cons #x4014a8 #xc8) ;;  
   (cons #x4014a9 #x8b) ;; mov (%rax),%eax 
   (cons #x4014aa #x00) ;;  
   (cons #x4014ab #x48) ;; cltq 
   (cons #x4014ac #x98) ;;  
   (cons #x4014ad #x48) ;; shl $0x2,%rax 
   (cons #x4014ae #xc1) ;;  
   (cons #x4014af #xe0) ;;  
   (cons #x4014b0 #x02) ;;  
   (cons #x4014b1 #x48) ;; add %rdx,%rax 
   (cons #x4014b2 #x01) ;;  
   (cons #x4014b3 #xd0) ;;  
   (cons #x4014b4 #x8b) ;; mov (%rax),%eax 
   (cons #x4014b5 #x00) ;;  
   (cons #x4014b6 #x85) ;; test %eax,%eax 
   (cons #x4014b7 #xc0) ;;  
   (cons #x4014b8 #x0f) ;; jne 40157f <propagate+0x2f3> 
   (cons #x4014b9 #x85) ;;  
   (cons #x4014ba #xc1) ;;  
   (cons #x4014bb #x00) ;;  
   (cons #x4014bc #x00) ;;  
   (cons #x4014bd #x00) ;;  
   (cons #x4014be #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4014bf #x8b) ;;  
   (cons #x4014c0 #x45) ;;  
   (cons #x4014c1 #xb8) ;;  
   (cons #x4014c2 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x4014c3 #x8b) ;;  
   (cons #x4014c4 #x50) ;;  
   (cons #x4014c5 #x40) ;;  
   (cons #x4014c6 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x4014c7 #x8b) ;;  
   (cons #x4014c8 #x45) ;;  
   (cons #x4014c9 #xc8) ;;  
   (cons #x4014ca #x8b) ;; mov (%rax),%eax 
   (cons #x4014cb #x00) ;;  
   (cons #x4014cc #xf7) ;; neg %eax 
   (cons #x4014cd #xd8) ;;  
   (cons #x4014ce #x48) ;; cltq 
   (cons #x4014cf #x98) ;;  
   (cons #x4014d0 #x48) ;; shl $0x2,%rax 
   (cons #x4014d1 #xc1) ;;  
   (cons #x4014d2 #xe0) ;;  
   (cons #x4014d3 #x02) ;;  
   (cons #x4014d4 #x48) ;; lea (%rdx,%rax,1),%rcx 
   (cons #x4014d5 #x8d) ;;  
   (cons #x4014d6 #x0c) ;;  
   (cons #x4014d7 #x02) ;;  
   (cons #x4014d8 #x8b) ;; mov -0x28(%rbp),%edx 
   (cons #x4014d9 #x55) ;;  
   (cons #x4014da #xd8) ;;  
   (cons #x4014db #x89) ;; mov %edx,%eax 
   (cons #x4014dc #xd0) ;;  
   (cons #x4014dd #xc1) ;; shl $0x2,%eax 
   (cons #x4014de #xe0) ;;  
   (cons #x4014df #x02) ;;  
   (cons #x4014e0 #x01) ;; add %edx,%eax 
   (cons #x4014e1 #xd0) ;;  
   (cons #x4014e2 #x83) ;; add $0x1,%eax 
   (cons #x4014e3 #xc0) ;;  
   (cons #x4014e4 #x01) ;;  
   (cons #x4014e5 #x89) ;; mov %eax,(%rcx) 
   (cons #x4014e6 #x01) ;;  
   (cons #x4014e7 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4014e8 #x8b) ;;  
   (cons #x4014e9 #x45) ;;  
   (cons #x4014ea #xb8) ;;  
   (cons #x4014eb #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4014ec #x8b) ;;  
   (cons #x4014ed #x80) ;;  
   (cons #x4014ee #x80) ;;  
   (cons #x4014ef #x00) ;;  
   (cons #x4014f0 #x00) ;;  
   (cons #x4014f1 #x00) ;;  
   (cons #x4014f2 #x48) ;; mov -0x38(%rbp),%rdx 
   (cons #x4014f3 #x8b) ;;  
   (cons #x4014f4 #x55) ;;  
   (cons #x4014f5 #xc8) ;;  
   (cons #x4014f6 #x8b) ;; mov (%rdx),%edx 
   (cons #x4014f7 #x12) ;;  
   (cons #x4014f8 #xf7) ;; neg %edx 
   (cons #x4014f9 #xda) ;;  
   (cons #x4014fa #x89) ;; mov %edx,(%rax) 
   (cons #x4014fb #x10) ;;  
   (cons #x4014fc #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4014fd #x8d) ;;  
   (cons #x4014fe #x50) ;;  
   (cons #x4014ff #x04) ;;  
   (cons #x401500 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401501 #x8b) ;;  
   (cons #x401502 #x45) ;;  
   (cons #x401503 #xb8) ;;  
   (cons #x401504 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x401505 #x89) ;;  
   (cons #x401506 #x90) ;;  
   (cons #x401507 #x80) ;;  
   (cons #x401508 #x00) ;;  
   (cons #x401509 #x00) ;;  
   (cons #x40150a #x00) ;;  
   (cons #x40150b #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40150c #x8b) ;;  
   (cons #x40150d #x45) ;;  
   (cons #x40150e #xb8) ;;  
   (cons #x40150f #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x401510 #x8b) ;;  
   (cons #x401511 #x48) ;;  
   (cons #x401512 #x30) ;;  
   (cons #x401513 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x401514 #x8b) ;;  
   (cons #x401515 #x45) ;;  
   (cons #x401516 #xc8) ;;  
   (cons #x401517 #x8b) ;; mov (%rax),%eax 
   (cons #x401518 #x00) ;;  
   (cons #x401519 #x89) ;; mov %eax,%edx 
   (cons #x40151a #xc2) ;;  
   (cons #x40151b #xc1) ;; sar $0x1f,%edx 
   (cons #x40151c #xfa) ;;  
   (cons #x40151d #x1f) ;;  
   (cons #x40151e #x31) ;; xor %edx,%eax 
   (cons #x40151f #xd0) ;;  
   (cons #x401520 #x29) ;; sub %edx,%eax 
   (cons #x401521 #xd0) ;;  
   (cons #x401522 #x48) ;; cltq 
   (cons #x401523 #x98) ;;  
   (cons #x401524 #x48) ;; shl $0x2,%rax 
   (cons #x401525 #xc1) ;;  
   (cons #x401526 #xe0) ;;  
   (cons #x401527 #x02) ;;  
   (cons #x401528 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401529 #x8d) ;;  
   (cons #x40152a #x14) ;;  
   (cons #x40152b #x01) ;;  
   (cons #x40152c #x48) ;; mov -0x38(%rbp),%rcx 
   (cons #x40152d #x8b) ;;  
   (cons #x40152e #x4d) ;;  
   (cons #x40152f #xc8) ;;  
   (cons #x401530 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401531 #x8b) ;;  
   (cons #x401532 #x45) ;;  
   (cons #x401533 #xb8) ;;  
   (cons #x401534 #x48) ;; mov (%rax),%rax 
   (cons #x401535 #x8b) ;;  
   (cons #x401536 #x00) ;;  
   (cons #x401537 #x48) ;; mov %rcx,%rbx 
   (cons #x401538 #x89) ;;  
   (cons #x401539 #xcb) ;;  
   (cons #x40153a #x48) ;; sub %rax,%rbx 
   (cons #x40153b #x29) ;;  
   (cons #x40153c #xc3) ;;  
   (cons #x40153d #x48) ;; mov %rbx,%rax 
   (cons #x40153e #x89) ;;  
   (cons #x40153f #xd8) ;;  
   (cons #x401540 #x48) ;; sar $0x2,%rax 
   (cons #x401541 #xc1) ;;  
   (cons #x401542 #xf8) ;;  
   (cons #x401543 #x02) ;;  
   (cons #x401544 #x83) ;; add $0x1,%eax 
   (cons #x401545 #xc0) ;;  
   (cons #x401546 #x01) ;;  
   (cons #x401547 #x89) ;; mov %eax,(%rdx) 
   (cons #x401548 #x02) ;;  
   (cons #x401549 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40154a #x8b) ;;  
   (cons #x40154b #x45) ;;  
   (cons #x40154c #xb8) ;;  
   (cons #x40154d #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x40154e #x8b) ;;  
   (cons #x40154f #x48) ;;  
   (cons #x401550 #x28) ;;  
   (cons #x401551 #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x401552 #x8b) ;;  
   (cons #x401553 #x45) ;;  
   (cons #x401554 #xc8) ;;  
   (cons #x401555 #x8b) ;; mov (%rax),%eax 
   (cons #x401556 #x00) ;;  
   (cons #x401557 #x89) ;; mov %eax,%edx 
   (cons #x401558 #xc2) ;;  
   (cons #x401559 #xc1) ;; sar $0x1f,%edx 
   (cons #x40155a #xfa) ;;  
   (cons #x40155b #x1f) ;;  
   (cons #x40155c #x31) ;; xor %edx,%eax 
   (cons #x40155d #xd0) ;;  
   (cons #x40155e #x29) ;; sub %edx,%eax 
   (cons #x40155f #xd0) ;;  
   (cons #x401560 #x48) ;; cltq 
   (cons #x401561 #x98) ;;  
   (cons #x401562 #x48) ;; shl $0x2,%rax 
   (cons #x401563 #xc1) ;;  
   (cons #x401564 #xe0) ;;  
   (cons #x401565 #x02) ;;  
   (cons #x401566 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401567 #x8d) ;;  
   (cons #x401568 #x14) ;;  
   (cons #x401569 #x01) ;;  
   (cons #x40156a #x48) ;; mov -0x38(%rbp),%rax 
   (cons #x40156b #x8b) ;;  
   (cons #x40156c #x45) ;;  
   (cons #x40156d #xc8) ;;  
   (cons #x40156e #x8b) ;; mov (%rax),%eax 
   (cons #x40156f #x00) ;;  
   (cons #x401570 #x85) ;; test %eax,%eax 
   (cons #x401571 #xc0) ;;  
   (cons #x401572 #x0f) ;; setg %al ;; This supposed to write 1 to al if (ZF=0 and SF=OF)
   (cons #x401573 #x9f) ;;          ;; but it appears to be modifying
   (cons #x401574 #xc0) ;;          ;; the memory??!!
   (cons #x401575 #x0f) ;; movzbl %al,%eax 
   (cons #x401576 #xb6) ;;  
   (cons #x401577 #xc0) ;;  
   (cons #x401578 #x89) ;; mov %eax,(%rdx) 
   (cons #x401579 #x02) ;;  
   (cons #x40157a #xe9) ;; jmpq 40167a <propagate+0x3ee> 
   (cons #x40157b #xfb) ;;  
   (cons #x40157c #x00) ;;  
   (cons #x40157d #x00) ;;  
   (cons #x40157e #x00) ;;  
   (cons #x40157f #x83) ;; cmpl $0x0,-0x28(%rbp) 
   (cons #x401580 #x7d) ;;  
   (cons #x401581 #xd8) ;;  
   (cons #x401582 #x00) ;;  
   (cons #x401583 #x74) ;; je 40158f <propagate+0x303> 
   (cons #x401584 #x0a) ;;  
   (cons #x401585 #xb8) ;; mov $0x0,%eax 
   (cons #x401586 #x00) ;;  
   (cons #x401587 #x00) ;;  
   (cons #x401588 #x00) ;;  
   (cons #x401589 #x00) ;;  
   (cons #x40158a #xe9) ;; jmpq 4016c0 <propagate+0x434> 
   (cons #x40158b #x31) ;;  
   (cons #x40158c #x01) ;;  
   (cons #x40158d #x00) ;;  
   (cons #x40158e #x00) ;;  
   (cons #x40158f #x48) ;; mov -0x38(%rbp),%rdx 
   (cons #x401590 #x8b) ;;  
   (cons #x401591 #x55) ;;  
   (cons #x401592 #xc8) ;;  
   (cons #x401593 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401594 #x8b) ;;  
   (cons #x401595 #x45) ;;  
   (cons #x401596 #xb8) ;;  
   (cons #x401597 #x48) ;; mov %rdx,%rsi 
   (cons #x401598 #x89) ;;  
   (cons #x401599 #xd6) ;;  
   (cons #x40159a #x48) ;; mov %rax,%rdi 
   (cons #x40159b #x89) ;;  
   (cons #x40159c #xc7) ;;  
   (cons #x40159d #xe8) ;; callq 400c2a <analyze> 
   (cons #x40159e #x88) ;;  
   (cons #x40159f #xf6) ;;  
   (cons #x4015a0 #xff) ;;  
   (cons #x4015a1 #xff) ;;  
   (cons #x4015a2 #x48) ;; mov %rax,-0x30(%rbp) 
   (cons #x4015a3 #x89) ;;  
   (cons #x4015a4 #x45) ;;  
   (cons #x4015a5 #xd0) ;;  
   (cons #x4015a6 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4015a7 #x8b) ;;  
   (cons #x4015a8 #x45) ;;  
   (cons #x4015a9 #xb8) ;;  
   (cons #x4015aa #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x4015ab #x8b) ;;  
   (cons #x4015ac #x50) ;;  
   (cons #x4015ad #x40) ;;  
   (cons #x4015ae #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x4015af #x8b) ;;  
   (cons #x4015b0 #x45) ;;  
   (cons #x4015b1 #xd0) ;;  
   (cons #x4015b2 #x8b) ;; mov (%rax),%eax 
   (cons #x4015b3 #x00) ;;  
   (cons #x4015b4 #xf7) ;; neg %eax 
   (cons #x4015b5 #xd8) ;;  
   (cons #x4015b6 #x48) ;; cltq 
   (cons #x4015b7 #x98) ;;  
   (cons #x4015b8 #x48) ;; shl $0x2,%rax 
   (cons #x4015b9 #xc1) ;;  
   (cons #x4015ba #xe0) ;;  
   (cons #x4015bb #x02) ;;  
   (cons #x4015bc #x48) ;; lea (%rdx,%rax,1),%rcx 
   (cons #x4015bd #x8d) ;;  
   (cons #x4015be #x0c) ;;  
   (cons #x4015bf #x02) ;;  
   (cons #x4015c0 #x8b) ;; mov -0x28(%rbp),%edx 
   (cons #x4015c1 #x55) ;;  
   (cons #x4015c2 #xd8) ;;  
   (cons #x4015c3 #x89) ;; mov %edx,%eax 
   (cons #x4015c4 #xd0) ;;  
   (cons #x4015c5 #xc1) ;; shl $0x2,%eax 
   (cons #x4015c6 #xe0) ;;  
   (cons #x4015c7 #x02) ;;  
   (cons #x4015c8 #x01) ;; add %edx,%eax 
   (cons #x4015c9 #xd0) ;;  
   (cons #x4015ca #x83) ;; add $0x1,%eax 
   (cons #x4015cb #xc0) ;;  
   (cons #x4015cc #x01) ;;  
   (cons #x4015cd #x89) ;; mov %eax,(%rcx) 
   (cons #x4015ce #x01) ;;  
   (cons #x4015cf #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4015d0 #x8b) ;;  
   (cons #x4015d1 #x45) ;;  
   (cons #x4015d2 #xb8) ;;  
   (cons #x4015d3 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4015d4 #x8b) ;;  
   (cons #x4015d5 #x80) ;;  
   (cons #x4015d6 #x80) ;;  
   (cons #x4015d7 #x00) ;;  
   (cons #x4015d8 #x00) ;;  
   (cons #x4015d9 #x00) ;;  
   (cons #x4015da #x48) ;; mov -0x30(%rbp),%rdx 
   (cons #x4015db #x8b) ;;  
   (cons #x4015dc #x55) ;;  
   (cons #x4015dd #xd0) ;;  
   (cons #x4015de #x8b) ;; mov (%rdx),%edx 
   (cons #x4015df #x12) ;;  
   (cons #x4015e0 #xf7) ;; neg %edx 
   (cons #x4015e1 #xda) ;;  
   (cons #x4015e2 #x89) ;; mov %edx,(%rax) 
   (cons #x4015e3 #x10) ;;  
   (cons #x4015e4 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4015e5 #x8d) ;;  
   (cons #x4015e6 #x50) ;;  
   (cons #x4015e7 #x04) ;;  
   (cons #x4015e8 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4015e9 #x8b) ;;  
   (cons #x4015ea #x45) ;;  
   (cons #x4015eb #xb8) ;;  
   (cons #x4015ec #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x4015ed #x89) ;;  
   (cons #x4015ee #x90) ;;  
   (cons #x4015ef #x80) ;;  
   (cons #x4015f0 #x00) ;;  
   (cons #x4015f1 #x00) ;;  
   (cons #x4015f2 #x00) ;;  
   (cons #x4015f3 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4015f4 #x8b) ;;  
   (cons #x4015f5 #x45) ;;  
   (cons #x4015f6 #xb8) ;;  
   (cons #x4015f7 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x4015f8 #x8b) ;;  
   (cons #x4015f9 #x48) ;;  
   (cons #x4015fa #x30) ;;  
   (cons #x4015fb #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x4015fc #x8b) ;;  
   (cons #x4015fd #x45) ;;  
   (cons #x4015fe #xd0) ;;  
   (cons #x4015ff #x8b) ;; mov (%rax),%eax 
   (cons #x401600 #x00) ;;  
   (cons #x401601 #x89) ;; mov %eax,%edx 
   (cons #x401602 #xc2) ;;  
   (cons #x401603 #xc1) ;; sar $0x1f,%edx 
   (cons #x401604 #xfa) ;;  
   (cons #x401605 #x1f) ;;  
   (cons #x401606 #x31) ;; xor %edx,%eax 
   (cons #x401607 #xd0) ;;  
   (cons #x401608 #x29) ;; sub %edx,%eax 
   (cons #x401609 #xd0) ;;  
   (cons #x40160a #x48) ;; cltq 
   (cons #x40160b #x98) ;;  
   (cons #x40160c #x48) ;; shl $0x2,%rax 
   (cons #x40160d #xc1) ;;  
   (cons #x40160e #xe0) ;;  
   (cons #x40160f #x02) ;;  
   (cons #x401610 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401611 #x8d) ;;  
   (cons #x401612 #x14) ;;  
   (cons #x401613 #x01) ;;  
   (cons #x401614 #x48) ;; mov -0x30(%rbp),%rcx 
   (cons #x401615 #x8b) ;;  
   (cons #x401616 #x4d) ;;  
   (cons #x401617 #xd0) ;;  
   (cons #x401618 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401619 #x8b) ;;  
   (cons #x40161a #x45) ;;  
   (cons #x40161b #xb8) ;;  
   (cons #x40161c #x48) ;; mov (%rax),%rax 
   (cons #x40161d #x8b) ;;  
   (cons #x40161e #x00) ;;  
   (cons #x40161f #x48) ;; mov %rcx,%rbx 
   (cons #x401620 #x89) ;;  
   (cons #x401621 #xcb) ;;  
   (cons #x401622 #x48) ;; sub %rax,%rbx 
   (cons #x401623 #x29) ;;  
   (cons #x401624 #xc3) ;;  
   (cons #x401625 #x48) ;; mov %rbx,%rax 
   (cons #x401626 #x89) ;;  
   (cons #x401627 #xd8) ;;  
   (cons #x401628 #x48) ;; sar $0x2,%rax 
   (cons #x401629 #xc1) ;;  
   (cons #x40162a #xf8) ;;  
   (cons #x40162b #x02) ;;  
   (cons #x40162c #x83) ;; add $0x1,%eax 
   (cons #x40162d #xc0) ;;  
   (cons #x40162e #x01) ;;  
   (cons #x40162f #x89) ;; mov %eax,(%rdx) 
   (cons #x401630 #x02) ;;  
   (cons #x401631 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401632 #x8b) ;;  
   (cons #x401633 #x45) ;;  
   (cons #x401634 #xb8) ;;  
   (cons #x401635 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x401636 #x8b) ;;  
   (cons #x401637 #x48) ;;  
   (cons #x401638 #x28) ;;  
   (cons #x401639 #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x40163a #x8b) ;;  
   (cons #x40163b #x45) ;;  
   (cons #x40163c #xd0) ;;  
   (cons #x40163d #x8b) ;; mov (%rax),%eax 
   (cons #x40163e #x00) ;;  
   (cons #x40163f #x89) ;; mov %eax,%edx 
   (cons #x401640 #xc2) ;;  
   (cons #x401641 #xc1) ;; sar $0x1f,%edx 
   (cons #x401642 #xfa) ;;  
   (cons #x401643 #x1f) ;;  
   (cons #x401644 #x31) ;; xor %edx,%eax 
   (cons #x401645 #xd0) ;;  
   (cons #x401646 #x29) ;; sub %edx,%eax 
   (cons #x401647 #xd0) ;;  
   (cons #x401648 #x48) ;; cltq 
   (cons #x401649 #x98) ;;  
   (cons #x40164a #x48) ;; shl $0x2,%rax 
   (cons #x40164b #xc1) ;;  
   (cons #x40164c #xe0) ;;  
   (cons #x40164d #x02) ;;  
   (cons #x40164e #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40164f #x8d) ;;  
   (cons #x401650 #x14) ;;  
   (cons #x401651 #x01) ;;  
   (cons #x401652 #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x401653 #x8b) ;;  
   (cons #x401654 #x45) ;;  
   (cons #x401655 #xd0) ;;  
   (cons #x401656 #x8b) ;; mov (%rax),%eax 
   (cons #x401657 #x00) ;;  
   (cons #x401658 #x85) ;; test %eax,%eax 
   (cons #x401659 #xc0) ;;  
   (cons #x40165a #x0f) ;; setg %al 
   (cons #x40165b #x9f) ;;  
   (cons #x40165c #xc0) ;;  
   (cons #x40165d #x0f) ;; movzbl %al,%eax 
   (cons #x40165e #xb6) ;;  
   (cons #x40165f #xc0) ;;  
   (cons #x401660 #x89) ;; mov %eax,(%rdx) 
   (cons #x401661 #x02) ;;  
   (cons #x401662 #x48) ;; mov -0x30(%rbp),%rax 
   (cons #x401663 #x8b) ;;  
   (cons #x401664 #x45) ;;  
   (cons #x401665 #xd0) ;;  
   (cons #x401666 #x48) ;; add $0x4,%rax 
   (cons #x401667 #x83) ;;  
   (cons #x401668 #xc0) ;;  
   (cons #x401669 #x04) ;;  
   (cons #x40166a #x8b) ;; mov (%rax),%eax 
   (cons #x40166b #x00) ;;  
   (cons #x40166c #x85) ;; test %eax,%eax 
   (cons #x40166d #xc0) ;;  
   (cons #x40166e #x0f) ;; sete %al 
   (cons #x40166f #x94) ;;  
   (cons #x401670 #xc0) ;;  
   (cons #x401671 #x0f) ;; movzbl %al,%eax 
   (cons #x401672 #xb6) ;;  
   (cons #x401673 #xc0) ;;  
   (cons #x401674 #x89) ;; mov %eax,-0x28(%rbp) 
   (cons #x401675 #x45) ;;  
   (cons #x401676 #xd8) ;;  
   (cons #x401677 #xeb) ;; jmp 401689 <propagate+0x3fd> 
   (cons #x401678 #x10) ;;  
   (cons #x401679 #x90) ;; nop 
   (cons #x40167a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40167b #x8b) ;;  
   (cons #x40167c #x45) ;;  
   (cons #x40167d #xc0) ;;  
   (cons #x40167e #x8b) ;; mov (%rax),%eax 
   (cons #x40167f #x00) ;;  
   (cons #x401680 #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x401681 #xf8) ;;  
   (cons #x401682 #xf7) ;;  
   (cons #x401683 #x0f) ;; jne 40130d <propagate+0x81> 
   (cons #x401684 #x85) ;;  
   (cons #x401685 #x84) ;;  
   (cons #x401686 #xfc) ;;  
   (cons #x401687 #xff) ;;  
   (cons #x401688 #xff) ;;  
   (cons #x401689 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x40168a #x8b) ;;  
   (cons #x40168b #x45) ;;  
   (cons #x40168c #xb8) ;;  
   (cons #x40168d #x48) ;; mov 0x78(%rax),%rdx 
   (cons #x40168e #x8b) ;;  
   (cons #x40168f #x50) ;;  
   (cons #x401690 #x78) ;;  
   (cons #x401691 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x401692 #x8b) ;;  
   (cons #x401693 #x45) ;;  
   (cons #x401694 #xb8) ;;  
   (cons #x401695 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x401696 #x8b) ;;  
   (cons #x401697 #x80) ;;  
   (cons #x401698 #x80) ;;  
   (cons #x401699 #x00) ;;  
   (cons #x40169a #x00) ;;  
   (cons #x40169b #x00) ;;  
   (cons #x40169c #x48) ;; cmp %rax,%rdx 
   (cons #x40169d #x39) ;;  
   (cons #x40169e #xc2) ;;  
   (cons #x40169f #x0f) ;; jb 4012d6 <propagate+0x4a> 
   (cons #x4016a0 #x82) ;;  
   (cons #x4016a1 #x31) ;;  
   (cons #x4016a2 #xfc) ;;  
   (cons #x4016a3 #xff) ;;  
   (cons #x4016a4 #xff) ;;  
   (cons #x4016a5 #x83) ;; cmpl $0x0,-0x28(%rbp) 
   (cons #x4016a6 #x7d) ;;  
   (cons #x4016a7 #xd8) ;;  
   (cons #x4016a8 #x00) ;;  
   (cons #x4016a9 #x74) ;; je 4016bb <propagate+0x42f> 
   (cons #x4016aa #x10) ;;  
   (cons #x4016ab #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4016ac #x8b) ;;  
   (cons #x4016ad #x45) ;;  
   (cons #x4016ae #xb8) ;;  
   (cons #x4016af #x48) ;; mov 0x78(%rax),%rdx 
   (cons #x4016b0 #x8b) ;;  
   (cons #x4016b1 #x50) ;;  
   (cons #x4016b2 #x78) ;;  
   (cons #x4016b3 #x48) ;; mov -0x48(%rbp),%rax 
   (cons #x4016b4 #x8b) ;;  
   (cons #x4016b5 #x45) ;;  
   (cons #x4016b6 #xb8) ;;  
   (cons #x4016b7 #x48) ;; mov %rdx,0x70(%rax) 
   (cons #x4016b8 #x89) ;;  
   (cons #x4016b9 #x50) ;;  
   (cons #x4016ba #x70) ;;  
   (cons #x4016bb #xb8) ;; mov $0x1,%eax 
   (cons #x4016bc #x01) ;;  
   (cons #x4016bd #x00) ;;  
   (cons #x4016be #x00) ;;  
   (cons #x4016bf #x00) ;;  
   (cons #x4016c0 #x48) ;; add $0x48,%rsp 
   (cons #x4016c1 #x83) ;;  
   (cons #x4016c2 #xc4) ;;  
   (cons #x4016c3 #x48) ;;  
   (cons #x4016c4 #x5b) ;; pop %rbx 
   (cons #x4016c5 #x5d) ;; pop %rbp 
   (cons #x4016c6 #xc3) ;; retq 
   
;; Section: <luby>:


   (cons #x4016c7 #x55) ;; push %rbp 
   (cons #x4016c8 #x48) ;; mov %rsp,%rbp 
   (cons #x4016c9 #x89) ;;  
   (cons #x4016ca #xe5) ;;  
   (cons #x4016cb #x89) ;; mov %edi,-0x14(%rbp) 
   (cons #x4016cc #x7d) ;;  
   (cons #x4016cd #xec) ;;  
   (cons #x4016ce #xc7) ;; movl $0x1,-0x8(%rbp) 
   (cons #x4016cf #x45) ;;  
   (cons #x4016d0 #xf8) ;;  
   (cons #x4016d1 #x01) ;;  
   (cons #x4016d2 #x00) ;;  
   (cons #x4016d3 #x00) ;;  
   (cons #x4016d4 #x00) ;;  
   (cons #x4016d5 #xc7) ;; movl $0x0,-0x4(%rbp) 
   (cons #x4016d6 #x45) ;;  
   (cons #x4016d7 #xfc) ;;  
   (cons #x4016d8 #x00) ;;  
   (cons #x4016d9 #x00) ;;  
   (cons #x4016da #x00) ;;  
   (cons #x4016db #x00) ;;  
   (cons #x4016dc #xeb) ;; jmp 4016ed <luby+0x26> 
   (cons #x4016dd #x0f) ;;  
   (cons #x4016de #x83) ;; addl $0x1,-0x4(%rbp) 
   (cons #x4016df #x45) ;;  
   (cons #x4016e0 #xfc) ;;  
   (cons #x4016e1 #x01) ;;  
   (cons #x4016e2 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x4016e3 #x45) ;;  
   (cons #x4016e4 #xf8) ;;  
   (cons #x4016e5 #x01) ;; add %eax,%eax 
   (cons #x4016e6 #xc0) ;;  
   (cons #x4016e7 #x83) ;; add $0x1,%eax 
   (cons #x4016e8 #xc0) ;;  
   (cons #x4016e9 #x01) ;;  
   (cons #x4016ea #x89) ;; mov %eax,-0x8(%rbp) 
   (cons #x4016eb #x45) ;;  
   (cons #x4016ec #xf8) ;;  
   (cons #x4016ed #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x4016ee #x45) ;;  
   (cons #x4016ef #xec) ;;  
   (cons #x4016f0 #x83) ;; add $0x1,%eax 
   (cons #x4016f1 #xc0) ;;  
   (cons #x4016f2 #x01) ;;  
   (cons #x4016f3 #x3b) ;; cmp -0x8(%rbp),%eax 
   (cons #x4016f4 #x45) ;;  
   (cons #x4016f5 #xf8) ;;  
   (cons #x4016f6 #x7f) ;; jg 4016de <luby+0x17> 
   (cons #x4016f7 #xe6) ;;  
   (cons #x4016f8 #xeb) ;; jmp 401717 <luby+0x50> 
   (cons #x4016f9 #x1d) ;;  
   (cons #x4016fa #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x4016fb #x45) ;;  
   (cons #x4016fc #xf8) ;;  
   (cons #x4016fd #x83) ;; sub $0x1,%eax 
   (cons #x4016fe #xe8) ;;  
   (cons #x4016ff #x01) ;;  
   (cons #x401700 #xd1) ;; sar %eax 
   (cons #x401701 #xf8) ;;  
   (cons #x401702 #x89) ;; mov %eax,-0x8(%rbp) 
   (cons #x401703 #x45) ;;  
   (cons #x401704 #xf8) ;;  
   (cons #x401705 #x83) ;; subl $0x1,-0x4(%rbp) 
   (cons #x401706 #x6d) ;;  
   (cons #x401707 #xfc) ;;  
   (cons #x401708 #x01) ;;  
   (cons #x401709 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x40170a #x45) ;;  
   (cons #x40170b #xec) ;;  
   (cons #x40170c #x89) ;; mov %eax,%edx 
   (cons #x40170d #xc2) ;;  
   (cons #x40170e #xc1) ;; sar $0x1f,%edx 
   (cons #x40170f #xfa) ;;  
   (cons #x401710 #x1f) ;;  
   (cons #x401711 #xf7) ;; idivl -0x8(%rbp) 
   (cons #x401712 #x7d) ;;  
   (cons #x401713 #xf8) ;;  
   (cons #x401714 #x89) ;; mov %edx,-0x14(%rbp) 
   (cons #x401715 #x55) ;;  
   (cons #x401716 #xec) ;;  
   (cons #x401717 #x8b) ;; mov -0x8(%rbp),%eax 
   (cons #x401718 #x45) ;;  
   (cons #x401719 #xf8) ;;  
   (cons #x40171a #x83) ;; sub $0x1,%eax 
   (cons #x40171b #xe8) ;;  
   (cons #x40171c #x01) ;;  
   (cons #x40171d #x3b) ;; cmp -0x14(%rbp),%eax 
   (cons #x40171e #x45) ;;  
   (cons #x40171f #xec) ;;  
   (cons #x401720 #x75) ;; jne 4016fa <luby+0x33> 
   (cons #x401721 #xd8) ;;  
   (cons #x401722 #x8b) ;; mov -0x4(%rbp),%eax 
   (cons #x401723 #x45) ;;  
   (cons #x401724 #xfc) ;;  
   (cons #x401725 #x5d) ;; pop %rbp 
   (cons #x401726 #xc3) ;; retq 
   
;; Section: <solve>:


   (cons #x401727 #x55) ;; push %rbp 
   (cons #x401728 #x48) ;; mov %rsp,%rbp 
   (cons #x401729 #x89) ;;  
   (cons #x40172a #xe5) ;;  
   (cons #x40172b #x53) ;; push %rbx 
   (cons #x40172c #x48) ;; sub $0x28,%rsp 
   (cons #x40172d #x83) ;;  
   (cons #x40172e #xec) ;;  
   (cons #x40172f #x28) ;;  
   (cons #x401730 #x48) ;; mov %rdi,-0x28(%rbp) 
   (cons #x401731 #x89) ;;  
   (cons #x401732 #x7d) ;;  
   (cons #x401733 #xd8) ;;  
   (cons #x401734 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x401735 #x45) ;;  
   (cons #x401736 #xe4) ;;  
   (cons #x401737 #x00) ;;  
   (cons #x401738 #x00) ;;  
   (cons #x401739 #x00) ;;  
   (cons #x40173a #x00) ;;  
   (cons #x40173b #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x40173c #x45) ;;  
   (cons #x40173d #xe4) ;;  
   (cons #x40173e #x89) ;; mov %eax,%edi 
   (cons #x40173f #xc7) ;;  
   (cons #x401740 #xe8) ;; callq 4016c7 <luby> 
   (cons #x401741 #x82) ;;  
   (cons #x401742 #xff) ;;  
   (cons #x401743 #xff) ;;  
   (cons #x401744 #xff) ;;  
   (cons #x401745 #x89) ;; mov %eax,-0x18(%rbp) 
   (cons #x401746 #x45) ;;  
   (cons #x401747 #xe8) ;;  
   (cons #x401748 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401749 #x8b) ;;  
   (cons #x40174a #x45) ;;  
   (cons #x40174b #xd8) ;;  
   (cons #x40174c #x48) ;; mov 0x80(%rax),%rdx 
   (cons #x40174d #x8b) ;;  
   (cons #x40174e #x90) ;;  
   (cons #x40174f #x80) ;;  
   (cons #x401750 #x00) ;;  
   (cons #x401751 #x00) ;;  
   (cons #x401752 #x00) ;;  
   (cons #x401753 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401754 #x8b) ;;  
   (cons #x401755 #x45) ;;  
   (cons #x401756 #xd8) ;;  
   (cons #x401757 #x48) ;; mov 0x78(%rax),%rax 
   (cons #x401758 #x8b) ;;  
   (cons #x401759 #x40) ;;  
   (cons #x40175a #x78) ;;  
   (cons #x40175b #x48) ;; cmp %rax,%rdx 
   (cons #x40175c #x39) ;;  
   (cons #x40175d #xc2) ;;  
   (cons #x40175e #x76) ;; jbe 40177a <solve+0x53> 
   (cons #x40175f #x1a) ;;  
   (cons #x401760 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401761 #x8b) ;;  
   (cons #x401762 #x45) ;;  
   (cons #x401763 #xd8) ;;  
   (cons #x401764 #x48) ;; mov %rax,%rdi 
   (cons #x401765 #x89) ;;  
   (cons #x401766 #xc7) ;;  
   (cons #x401767 #xe8) ;; callq 40128c <propagate> 
   (cons #x401768 #x20) ;;  
   (cons #x401769 #xfb) ;;  
   (cons #x40176a #xff) ;;  
   (cons #x40176b #xff) ;;  
   (cons #x40176c #x85) ;; test %eax,%eax 
   (cons #x40176d #xc0) ;;  
   (cons #x40176e #x75) ;; jne 40177a <solve+0x53> 
   (cons #x40176f #x0a) ;;  
   (cons #x401770 #xb8) ;; mov $0x0,%eax 
   (cons #x401771 #x00) ;;  
   (cons #x401772 #x00) ;;  
   (cons #x401773 #x00) ;;  
   (cons #x401774 #x00) ;;  
   (cons #x401775 #xe9) ;; jmpq 401a34 <solve+0x30d> 
   (cons #x401776 #xba) ;;  
   (cons #x401777 #x02) ;;  
   (cons #x401778 #x00) ;;  
   (cons #x401779 #x00) ;;  
   (cons #x40177a #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40177b #x8b) ;;  
   (cons #x40177c #x45) ;;  
   (cons #x40177d #xd8) ;;  
   (cons #x40177e #x8b) ;; mov 0x20(%rax),%edx 
   (cons #x40177f #x50) ;;  
   (cons #x401780 #x20) ;;  
   (cons #x401781 #x8b) ;; mov -0x18(%rbp),%eax 
   (cons #x401782 #x45) ;;  
   (cons #x401783 #xe8) ;;  
   (cons #x401784 #xbe) ;; mov $0x64,%esi 
   (cons #x401785 #x64) ;;  
   (cons #x401786 #x00) ;;  
   (cons #x401787 #x00) ;;  
   (cons #x401788 #x00) ;;  
   (cons #x401789 #x89) ;; mov %esi,%ebx 
   (cons #x40178a #xf3) ;;  
   (cons #x40178b #x89) ;; mov %eax,%ecx 
   (cons #x40178c #xc1) ;;  
   (cons #x40178d #xd3) ;; shl %cl,%ebx 
   (cons #x40178e #xe3) ;;  
   (cons #x40178f #x89) ;; mov %ebx,%eax 
   (cons #x401790 #xd8) ;;  
   (cons #x401791 #x39) ;; cmp %eax,%edx 
   (cons #x401792 #xc2) ;;  
   (cons #x401793 #x0f) ;; jg 40187a <solve+0x153> 
   (cons #x401794 #x8f) ;;  
   (cons #x401795 #xe1) ;;  
   (cons #x401796 #x00) ;;  
   (cons #x401797 #x00) ;;  
   (cons #x401798 #x00) ;;  
   (cons #x401799 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40179a #x8b) ;;  
   (cons #x40179b #x45) ;;  
   (cons #x40179c #xd8) ;;  
   (cons #x40179d #x8b) ;; mov 0x1c(%rax),%edx 
   (cons #x40179e #x50) ;;  
   (cons #x40179f #x1c) ;;  
   (cons #x4017a0 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017a1 #x8b) ;;  
   (cons #x4017a2 #x45) ;;  
   (cons #x4017a3 #xd8) ;;  
   (cons #x4017a4 #x8b) ;; mov 0x18(%rax),%eax 
   (cons #x4017a5 #x40) ;;  
   (cons #x4017a6 #x18) ;;  
   (cons #x4017a7 #x39) ;; cmp %eax,%edx 
   (cons #x4017a8 #xc2) ;;  
   (cons #x4017a9 #x0f) ;; jle 4018c3 <solve+0x19c> 
   (cons #x4017aa #x8e) ;;  
   (cons #x4017ab #x14) ;;  
   (cons #x4017ac #x01) ;;  
   (cons #x4017ad #x00) ;;  
   (cons #x4017ae #x00) ;;  
   (cons #x4017af #xe9) ;; jmpq 40187a <solve+0x153> 
   (cons #x4017b0 #xc6) ;;  
   (cons #x4017b1 #x00) ;;  
   (cons #x4017b2 #x00) ;;  
   (cons #x4017b3 #x00) ;;  
   (cons #x4017b4 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017b5 #x8b) ;;  
   (cons #x4017b6 #x45) ;;  
   (cons #x4017b7 #xd8) ;;  
   (cons #x4017b8 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4017b9 #x8b) ;;  
   (cons #x4017ba #x80) ;;  
   (cons #x4017bb #x80) ;;  
   (cons #x4017bc #x00) ;;  
   (cons #x4017bd #x00) ;;  
   (cons #x4017be #x00) ;;  
   (cons #x4017bf #x48) ;; lea -0x4(%rax),%rdx 
   (cons #x4017c0 #x8d) ;;  
   (cons #x4017c1 #x50) ;;  
   (cons #x4017c2 #xfc) ;;  
   (cons #x4017c3 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017c4 #x8b) ;;  
   (cons #x4017c5 #x45) ;;  
   (cons #x4017c6 #xd8) ;;  
   (cons #x4017c7 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x4017c8 #x89) ;;  
   (cons #x4017c9 #x90) ;;  
   (cons #x4017ca #x80) ;;  
   (cons #x4017cb #x00) ;;  
   (cons #x4017cc #x00) ;;  
   (cons #x4017cd #x00) ;;  
   (cons #x4017ce #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017cf #x8b) ;;  
   (cons #x4017d0 #x45) ;;  
   (cons #x4017d1 #xd8) ;;  
   (cons #x4017d2 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4017d3 #x8b) ;;  
   (cons #x4017d4 #x80) ;;  
   (cons #x4017d5 #x80) ;;  
   (cons #x4017d6 #x00) ;;  
   (cons #x4017d7 #x00) ;;  
   (cons #x4017d8 #x00) ;;  
   (cons #x4017d9 #x8b) ;; mov (%rax),%eax 
   (cons #x4017da #x00) ;;  
   (cons #x4017db #x89) ;; mov %eax,-0x14(%rbp) 
   (cons #x4017dc #x45) ;;  
   (cons #x4017dd #xec) ;;  
   (cons #x4017de #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017df #x8b) ;;  
   (cons #x4017e0 #x45) ;;  
   (cons #x4017e1 #xd8) ;;  
   (cons #x4017e2 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4017e3 #x8b) ;;  
   (cons #x4017e4 #x40) ;;  
   (cons #x4017e5 #x40) ;;  
   (cons #x4017e6 #x8b) ;; mov -0x14(%rbp),%edx 
   (cons #x4017e7 #x55) ;;  
   (cons #x4017e8 #xec) ;;  
   (cons #x4017e9 #x48) ;; movslq %edx,%rdx 
   (cons #x4017ea #x63) ;;  
   (cons #x4017eb #xd2) ;;  
   (cons #x4017ec #x48) ;; shl $0x2,%rdx 
   (cons #x4017ed #xc1) ;;  
   (cons #x4017ee #xe2) ;;  
   (cons #x4017ef #x02) ;;  
   (cons #x4017f0 #x48) ;; add %rdx,%rax 
   (cons #x4017f1 #x01) ;;  
   (cons #x4017f2 #xd0) ;;  
   (cons #x4017f3 #xc7) ;; movl $0x0,(%rax) 
   (cons #x4017f4 #x00) ;;  
   (cons #x4017f5 #x00) ;;  
   (cons #x4017f6 #x00) ;;  
   (cons #x4017f7 #x00) ;;  
   (cons #x4017f8 #x00) ;;  
   (cons #x4017f9 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4017fa #x8b) ;;  
   (cons #x4017fb #x45) ;;  
   (cons #x4017fc #xd8) ;;  
   (cons #x4017fd #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x4017fe #x8b) ;;  
   (cons #x4017ff #x48) ;;  
   (cons #x401800 #x60) ;;  
   (cons #x401801 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x401802 #x45) ;;  
   (cons #x401803 #xec) ;;  
   (cons #x401804 #x89) ;; mov %eax,%edx 
   (cons #x401805 #xc2) ;;  
   (cons #x401806 #xc1) ;; sar $0x1f,%edx 
   (cons #x401807 #xfa) ;;  
   (cons #x401808 #x1f) ;;  
   (cons #x401809 #x89) ;; mov %edx,%eax 
   (cons #x40180a #xd0) ;;  
   (cons #x40180b #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x40180c #x45) ;;  
   (cons #x40180d #xec) ;;  
   (cons #x40180e #x29) ;; sub %edx,%eax 
   (cons #x40180f #xd0) ;;  
   (cons #x401810 #x48) ;; cltq 
   (cons #x401811 #x98) ;;  
   (cons #x401812 #x48) ;; shl $0x2,%rax 
   (cons #x401813 #xc1) ;;  
   (cons #x401814 #xe0) ;;  
   (cons #x401815 #x02) ;;  
   (cons #x401816 #x48) ;; add %rcx,%rax 
   (cons #x401817 #x01) ;;  
   (cons #x401818 #xc8) ;;  
   (cons #x401819 #x8b) ;; mov (%rax),%eax 
   (cons #x40181a #x00) ;;  
   (cons #x40181b #x83) ;; cmp $0xfffffff7,%eax 
   (cons #x40181c #xf8) ;;  
   (cons #x40181d #xf7) ;;  
   (cons #x40181e #x75) ;; jne 40187b <solve+0x154> 
   (cons #x40181f #x5b) ;;  
   (cons #x401820 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401821 #x8b) ;;  
   (cons #x401822 #x45) ;;  
   (cons #x401823 #xd8) ;;  
   (cons #x401824 #x48) ;; mov 0x60(%rax),%rcx 
   (cons #x401825 #x8b) ;;  
   (cons #x401826 #x48) ;;  
   (cons #x401827 #x60) ;;  
   (cons #x401828 #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x401829 #x45) ;;  
   (cons #x40182a #xec) ;;  
   (cons #x40182b #x89) ;; mov %eax,%edx 
   (cons #x40182c #xc2) ;;  
   (cons #x40182d #xc1) ;; sar $0x1f,%edx 
   (cons #x40182e #xfa) ;;  
   (cons #x40182f #x1f) ;;  
   (cons #x401830 #x89) ;; mov %edx,%eax 
   (cons #x401831 #xd0) ;;  
   (cons #x401832 #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x401833 #x45) ;;  
   (cons #x401834 #xec) ;;  
   (cons #x401835 #x29) ;; sub %edx,%eax 
   (cons #x401836 #xd0) ;;  
   (cons #x401837 #x48) ;; cltq 
   (cons #x401838 #x98) ;;  
   (cons #x401839 #x48) ;; shl $0x2,%rax 
   (cons #x40183a #xc1) ;;  
   (cons #x40183b #xe0) ;;  
   (cons #x40183c #x02) ;;  
   (cons #x40183d #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40183e #x8d) ;;  
   (cons #x40183f #x14) ;;  
   (cons #x401840 #x01) ;;  
   (cons #x401841 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401842 #x8b) ;;  
   (cons #x401843 #x45) ;;  
   (cons #x401844 #xd8) ;;  
   (cons #x401845 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x401846 #x40) ;;  
   (cons #x401847 #x58) ;;  
   (cons #x401848 #x8d) ;; lea 0x1(%rax),%ecx 
   (cons #x401849 #x48) ;;  
   (cons #x40184a #x01) ;;  
   (cons #x40184b #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40184c #x8b) ;;  
   (cons #x40184d #x45) ;;  
   (cons #x40184e #xd8) ;;  
   (cons #x40184f #x89) ;; mov %ecx,0x58(%rax) 
   (cons #x401850 #x48) ;;  
   (cons #x401851 #x58) ;;  
   (cons #x401852 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401853 #x8b) ;;  
   (cons #x401854 #x45) ;;  
   (cons #x401855 #xd8) ;;  
   (cons #x401856 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x401857 #x40) ;;  
   (cons #x401858 #x58) ;;  
   (cons #x401859 #x89) ;; mov %eax,(%rdx) 
   (cons #x40185a #x02) ;;  
   (cons #x40185b #x8b) ;; mov -0x14(%rbp),%eax 
   (cons #x40185c #x45) ;;  
   (cons #x40185d #xec) ;;  
   (cons #x40185e #x89) ;; mov %eax,%edx 
   (cons #x40185f #xc2) ;;  
   (cons #x401860 #xc1) ;; sar $0x1f,%edx 
   (cons #x401861 #xfa) ;;  
   (cons #x401862 #x1f) ;;  
   (cons #x401863 #x89) ;; mov %edx,%eax 
   (cons #x401864 #xd0) ;;  
   (cons #x401865 #x33) ;; xor -0x14(%rbp),%eax 
   (cons #x401866 #x45) ;;  
   (cons #x401867 #xec) ;;  
   (cons #x401868 #x29) ;; sub %edx,%eax 
   (cons #x401869 #xd0) ;;  
   (cons #x40186a #x48) ;; mov -0x28(%rbp),%rdx 
   (cons #x40186b #x8b) ;;  
   (cons #x40186c #x55) ;;  
   (cons #x40186d #xd8) ;;  
   (cons #x40186e #x89) ;; mov %eax,%esi 
   (cons #x40186f #xc6) ;;  
   (cons #x401870 #x48) ;; mov %rdx,%rdi 
   (cons #x401871 #x89) ;;  
   (cons #x401872 #xd7) ;;  
   (cons #x401873 #xe8) ;; callq 4009cb <heapUp> 
   (cons #x401874 #x53) ;;  
   (cons #x401875 #xf1) ;;  
   (cons #x401876 #xff) ;;  
   (cons #x401877 #xff) ;;  
   (cons #x401878 #xeb) ;; jmp 40187b <solve+0x154> 
   (cons #x401879 #x01) ;;  
   (cons #x40187a #x90) ;; nop 
   (cons #x40187b #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40187c #x8b) ;;  
   (cons #x40187d #x45) ;;  
   (cons #x40187e #xd8) ;;  
   (cons #x40187f #x48) ;; mov 0x80(%rax),%rdx 
   (cons #x401880 #x8b) ;;  
   (cons #x401881 #x90) ;;  
   (cons #x401882 #x80) ;;  
   (cons #x401883 #x00) ;;  
   (cons #x401884 #x00) ;;  
   (cons #x401885 #x00) ;;  
   (cons #x401886 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401887 #x8b) ;;  
   (cons #x401888 #x45) ;;  
   (cons #x401889 #xd8) ;;  
   (cons #x40188a #x48) ;; mov 0x70(%rax),%rax 
   (cons #x40188b #x8b) ;;  
   (cons #x40188c #x40) ;;  
   (cons #x40188d #x70) ;;  
   (cons #x40188e #x48) ;; cmp %rax,%rdx 
   (cons #x40188f #x39) ;;  
   (cons #x401890 #xc2) ;;  
   (cons #x401891 #x0f) ;; ja 4017b4 <solve+0x8d> 
   (cons #x401892 #x87) ;;  
   (cons #x401893 #x1d) ;;  
   (cons #x401894 #xff) ;;  
   (cons #x401895 #xff) ;;  
   (cons #x401896 #xff) ;;  
   (cons #x401897 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401898 #x8b) ;;  
   (cons #x401899 #x45) ;;  
   (cons #x40189a #xd8) ;;  
   (cons #x40189b #x48) ;; mov 0x70(%rax),%rdx 
   (cons #x40189c #x8b) ;;  
   (cons #x40189d #x50) ;;  
   (cons #x40189e #x70) ;;  
   (cons #x40189f #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018a0 #x8b) ;;  
   (cons #x4018a1 #x45) ;;  
   (cons #x4018a2 #xd8) ;;  
   (cons #x4018a3 #x48) ;; mov %rdx,0x78(%rax) 
   (cons #x4018a4 #x89) ;;  
   (cons #x4018a5 #x50) ;;  
   (cons #x4018a6 #x78) ;;  
   (cons #x4018a7 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018a8 #x8b) ;;  
   (cons #x4018a9 #x45) ;;  
   (cons #x4018aa #xd8) ;;  
   (cons #x4018ab #xc7) ;; movl $0x0,0x20(%rax) 
   (cons #x4018ac #x40) ;;  
   (cons #x4018ad #x20) ;;  
   (cons #x4018ae #x00) ;;  
   (cons #x4018af #x00) ;;  
   (cons #x4018b0 #x00) ;;  
   (cons #x4018b1 #x00) ;;  
   (cons #x4018b2 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4018b3 #x45) ;;  
   (cons #x4018b4 #xe4) ;;  
   (cons #x4018b5 #x01) ;;  
   (cons #x4018b6 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4018b7 #x45) ;;  
   (cons #x4018b8 #xe4) ;;  
   (cons #x4018b9 #x89) ;; mov %eax,%edi 
   (cons #x4018ba #xc7) ;;  
   (cons #x4018bb #xe8) ;; callq 4016c7 <luby> 
   (cons #x4018bc #x07) ;;  
   (cons #x4018bd #xfe) ;;  
   (cons #x4018be #xff) ;;  
   (cons #x4018bf #xff) ;;  
   (cons #x4018c0 #x89) ;; mov %eax,-0x18(%rbp) 
   (cons #x4018c1 #x45) ;;  
   (cons #x4018c2 #xe8) ;;  
   (cons #x4018c3 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018c4 #x8b) ;;  
   (cons #x4018c5 #x45) ;;  
   (cons #x4018c6 #xd8) ;;  
   (cons #x4018c7 #x8b) ;; mov 0x1c(%rax),%edx 
   (cons #x4018c8 #x50) ;;  
   (cons #x4018c9 #x1c) ;;  
   (cons #x4018ca #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018cb #x8b) ;;  
   (cons #x4018cc #x45) ;;  
   (cons #x4018cd #xd8) ;;  
   (cons #x4018ce #x8b) ;; mov 0x18(%rax),%eax 
   (cons #x4018cf #x40) ;;  
   (cons #x4018d0 #x18) ;;  
   (cons #x4018d1 #x39) ;; cmp %eax,%edx 
   (cons #x4018d2 #xc2) ;;  
   (cons #x4018d3 #x7e) ;; jle 401935 <solve+0x20e> 
   (cons #x4018d4 #x60) ;;  
   (cons #x4018d5 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018d6 #x8b) ;;  
   (cons #x4018d7 #x45) ;;  
   (cons #x4018d8 #xd8) ;;  
   (cons #x4018d9 #x48) ;; mov %rax,%rdi 
   (cons #x4018da #x89) ;;  
   (cons #x4018db #xc7) ;;  
   (cons #x4018dc #xe8) ;; callq 40062e <reduceDB> 
   (cons #x4018dd #x4d) ;;  
   (cons #x4018de #xed) ;;  
   (cons #x4018df #xff) ;;  
   (cons #x4018e0 #xff) ;;  
   (cons #x4018e1 #xeb) ;; jmp 401935 <solve+0x20e> 
   (cons #x4018e2 #x52) ;;  
   (cons #x4018e3 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018e4 #x8b) ;;  
   (cons #x4018e5 #x45) ;;  
   (cons #x4018e6 #xd8) ;;  
   (cons #x4018e7 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x4018e8 #x8b) ;;  
   (cons #x4018e9 #x50) ;;  
   (cons #x4018ea #x40) ;;  
   (cons #x4018eb #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4018ec #x8b) ;;  
   (cons #x4018ed #x45) ;;  
   (cons #x4018ee #xd8) ;;  
   (cons #x4018ef #x48) ;; mov 0x50(%rax),%rax 
   (cons #x4018f0 #x8b) ;;  
   (cons #x4018f1 #x40) ;;  
   (cons #x4018f2 #x50) ;;  
   (cons #x4018f3 #x8b) ;; mov (%rax),%eax 
   (cons #x4018f4 #x00) ;;  
   (cons #x4018f5 #x48) ;; cltq 
   (cons #x4018f6 #x98) ;;  
   (cons #x4018f7 #x48) ;; shl $0x2,%rax 
   (cons #x4018f8 #xc1) ;;  
   (cons #x4018f9 #xe0) ;;  
   (cons #x4018fa #x02) ;;  
   (cons #x4018fb #x48) ;; add %rdx,%rax 
   (cons #x4018fc #x01) ;;  
   (cons #x4018fd #xd0) ;;  
   (cons #x4018fe #x8b) ;; mov (%rax),%eax 
   (cons #x4018ff #x00) ;;  
   (cons #x401900 #x85) ;; test %eax,%eax 
   (cons #x401901 #xc0) ;;  
   (cons #x401902 #x75) ;; jne 401927 <solve+0x200> 
   (cons #x401903 #x23) ;;  
   (cons #x401904 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401905 #x8b) ;;  
   (cons #x401906 #x45) ;;  
   (cons #x401907 #xd8) ;;  
   (cons #x401908 #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x401909 #x8b) ;;  
   (cons #x40190a #x50) ;;  
   (cons #x40190b #x40) ;;  
   (cons #x40190c #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40190d #x8b) ;;  
   (cons #x40190e #x45) ;;  
   (cons #x40190f #xd8) ;;  
   (cons #x401910 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x401911 #x8b) ;;  
   (cons #x401912 #x40) ;;  
   (cons #x401913 #x50) ;;  
   (cons #x401914 #x8b) ;; mov (%rax),%eax 
   (cons #x401915 #x00) ;;  
   (cons #x401916 #xf7) ;; neg %eax 
   (cons #x401917 #xd8) ;;  
   (cons #x401918 #x48) ;; cltq 
   (cons #x401919 #x98) ;;  
   (cons #x40191a #x48) ;; shl $0x2,%rax 
   (cons #x40191b #xc1) ;;  
   (cons #x40191c #xe0) ;;  
   (cons #x40191d #x02) ;;  
   (cons #x40191e #x48) ;; add %rdx,%rax 
   (cons #x40191f #x01) ;;  
   (cons #x401920 #xd0) ;;  
   (cons #x401921 #x8b) ;; mov (%rax),%eax 
   (cons #x401922 #x00) ;;  
   (cons #x401923 #x85) ;; test %eax,%eax 
   (cons #x401924 #xc0) ;;  
   (cons #x401925 #x74) ;; je 401943 <solve+0x21c> 
   (cons #x401926 #x1c) ;;  
   (cons #x401927 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401928 #x8b) ;;  
   (cons #x401929 #x45) ;;  
   (cons #x40192a #xd8) ;;  
   (cons #x40192b #x48) ;; mov %rax,%rdi 
   (cons #x40192c #x89) ;;  
   (cons #x40192d #xc7) ;;  
   (cons #x40192e #xe8) ;; callq 4007fd <heapRemoveTop> 
   (cons #x40192f #xca) ;;  
   (cons #x401930 #xee) ;;  
   (cons #x401931 #xff) ;;  
   (cons #x401932 #xff) ;;  
   (cons #x401933 #xeb) ;; jmp 401936 <solve+0x20f> 
   (cons #x401934 #x01) ;;  
   (cons #x401935 #x90) ;; nop 
   (cons #x401936 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401937 #x8b) ;;  
   (cons #x401938 #x45) ;;  
   (cons #x401939 #xd8) ;;  
   (cons #x40193a #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x40193b #x40) ;;  
   (cons #x40193c #x58) ;;  
   (cons #x40193d #x85) ;; test %eax,%eax 
   (cons #x40193e #xc0) ;;  
   (cons #x40193f #x75) ;; jne 4018e3 <solve+0x1bc> 
   (cons #x401940 #xa2) ;;  
   (cons #x401941 #xeb) ;; jmp 401944 <solve+0x21d> 
   (cons #x401942 #x01) ;;  
   (cons #x401943 #x90) ;; nop 
   (cons #x401944 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401945 #x8b) ;;  
   (cons #x401946 #x45) ;;  
   (cons #x401947 #xd8) ;;  
   (cons #x401948 #x8b) ;; mov 0x58(%rax),%eax 
   (cons #x401949 #x40) ;;  
   (cons #x40194a #x58) ;;  
   (cons #x40194b #x85) ;; test %eax,%eax 
   (cons #x40194c #xc0) ;;  
   (cons #x40194d #x75) ;; jne 401959 <solve+0x232> 
   (cons #x40194e #x0a) ;;  
   (cons #x40194f #xb8) ;; mov $0x1,%eax 
   (cons #x401950 #x01) ;;  
   (cons #x401951 #x00) ;;  
   (cons #x401952 #x00) ;;  
   (cons #x401953 #x00) ;;  
   (cons #x401954 #xe9) ;; jmpq 401a34 <solve+0x30d> 
   (cons #x401955 #xdb) ;;  
   (cons #x401956 #x00) ;;  
   (cons #x401957 #x00) ;;  
   (cons #x401958 #x00) ;;  
   (cons #x401959 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40195a #x8b) ;;  
   (cons #x40195b #x45) ;;  
   (cons #x40195c #xd8) ;;  
   (cons #x40195d #x48) ;; mov 0x40(%rax),%rdx 
   (cons #x40195e #x8b) ;;  
   (cons #x40195f #x50) ;;  
   (cons #x401960 #x40) ;;  
   (cons #x401961 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401962 #x8b) ;;  
   (cons #x401963 #x45) ;;  
   (cons #x401964 #xd8) ;;  
   (cons #x401965 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x401966 #x8b) ;;  
   (cons #x401967 #x48) ;;  
   (cons #x401968 #x28) ;;  
   (cons #x401969 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x40196a #x8b) ;;  
   (cons #x40196b #x45) ;;  
   (cons #x40196c #xd8) ;;  
   (cons #x40196d #x48) ;; mov 0x50(%rax),%rax 
   (cons #x40196e #x8b) ;;  
   (cons #x40196f #x40) ;;  
   (cons #x401970 #x50) ;;  
   (cons #x401971 #x8b) ;; mov (%rax),%eax 
   (cons #x401972 #x00) ;;  
   (cons #x401973 #x48) ;; cltq 
   (cons #x401974 #x98) ;;  
   (cons #x401975 #x48) ;; shl $0x2,%rax 
   (cons #x401976 #xc1) ;;  
   (cons #x401977 #xe0) ;;  
   (cons #x401978 #x02) ;;  
   (cons #x401979 #x48) ;; add %rcx,%rax 
   (cons #x40197a #x01) ;;  
   (cons #x40197b #xc8) ;;  
   (cons #x40197c #x8b) ;; mov (%rax),%eax 
   (cons #x40197d #x00) ;;  
   (cons #x40197e #x85) ;; test %eax,%eax 
   (cons #x40197f #xc0) ;;  
   (cons #x401980 #x74) ;; je 401996 <solve+0x26f> 
   (cons #x401981 #x14) ;;  
   (cons #x401982 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401983 #x8b) ;;  
   (cons #x401984 #x45) ;;  
   (cons #x401985 #xd8) ;;  
   (cons #x401986 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x401987 #x8b) ;;  
   (cons #x401988 #x40) ;;  
   (cons #x401989 #x50) ;;  
   (cons #x40198a #x8b) ;; mov (%rax),%eax 
   (cons #x40198b #x00) ;;  
   (cons #x40198c #xf7) ;; neg %eax 
   (cons #x40198d #xd8) ;;  
   (cons #x40198e #x48) ;; cltq 
   (cons #x40198f #x98) ;;  
   (cons #x401990 #x48) ;; shl $0x2,%rax 
   (cons #x401991 #xc1) ;;  
   (cons #x401992 #xe0) ;;  
   (cons #x401993 #x02) ;;  
   (cons #x401994 #xeb) ;; jmp 4019a6 <solve+0x27f> 
   (cons #x401995 #x10) ;;  
   (cons #x401996 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401997 #x8b) ;;  
   (cons #x401998 #x45) ;;  
   (cons #x401999 #xd8) ;;  
   (cons #x40199a #x48) ;; mov 0x50(%rax),%rax 
   (cons #x40199b #x8b) ;;  
   (cons #x40199c #x40) ;;  
   (cons #x40199d #x50) ;;  
   (cons #x40199e #x8b) ;; mov (%rax),%eax 
   (cons #x40199f #x00) ;;  
   (cons #x4019a0 #x48) ;; cltq 
   (cons #x4019a1 #x98) ;;  
   (cons #x4019a2 #x48) ;; shl $0x2,%rax 
   (cons #x4019a3 #xc1) ;;  
   (cons #x4019a4 #xe0) ;;  
   (cons #x4019a5 #x02) ;;  
   (cons #x4019a6 #x48) ;; add %rdx,%rax 
   (cons #x4019a7 #x01) ;;  
   (cons #x4019a8 #xd0) ;;  
   (cons #x4019a9 #xc7) ;; movl $0x1,(%rax) 
   (cons #x4019aa #x00) ;;  
   (cons #x4019ab #x01) ;;  
   (cons #x4019ac #x00) ;;  
   (cons #x4019ad #x00) ;;  
   (cons #x4019ae #x00) ;;  
   (cons #x4019af #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4019b0 #x8b) ;;  
   (cons #x4019b1 #x45) ;;  
   (cons #x4019b2 #xd8) ;;  
   (cons #x4019b3 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4019b4 #x8b) ;;  
   (cons #x4019b5 #x80) ;;  
   (cons #x4019b6 #x80) ;;  
   (cons #x4019b7 #x00) ;;  
   (cons #x4019b8 #x00) ;;  
   (cons #x4019b9 #x00) ;;  
   (cons #x4019ba #x48) ;; mov -0x28(%rbp),%rdx 
   (cons #x4019bb #x8b) ;;  
   (cons #x4019bc #x55) ;;  
   (cons #x4019bd #xd8) ;;  
   (cons #x4019be #x48) ;; mov 0x28(%rdx),%rcx 
   (cons #x4019bf #x8b) ;;  
   (cons #x4019c0 #x4a) ;;  
   (cons #x4019c1 #x28) ;;  
   (cons #x4019c2 #x48) ;; mov -0x28(%rbp),%rdx 
   (cons #x4019c3 #x8b) ;;  
   (cons #x4019c4 #x55) ;;  
   (cons #x4019c5 #xd8) ;;  
   (cons #x4019c6 #x48) ;; mov 0x50(%rdx),%rdx 
   (cons #x4019c7 #x8b) ;;  
   (cons #x4019c8 #x52) ;;  
   (cons #x4019c9 #x50) ;;  
   (cons #x4019ca #x8b) ;; mov (%rdx),%edx 
   (cons #x4019cb #x12) ;;  
   (cons #x4019cc #x48) ;; movslq %edx,%rdx 
   (cons #x4019cd #x63) ;;  
   (cons #x4019ce #xd2) ;;  
   (cons #x4019cf #x48) ;; shl $0x2,%rdx 
   (cons #x4019d0 #xc1) ;;  
   (cons #x4019d1 #xe2) ;;  
   (cons #x4019d2 #x02) ;;  
   (cons #x4019d3 #x48) ;; add %rcx,%rdx 
   (cons #x4019d4 #x01) ;;  
   (cons #x4019d5 #xca) ;;  
   (cons #x4019d6 #x8b) ;; mov (%rdx),%edx 
   (cons #x4019d7 #x12) ;;  
   (cons #x4019d8 #x85) ;; test %edx,%edx 
   (cons #x4019d9 #xd2) ;;  
   (cons #x4019da #x74) ;; je 4019ea <solve+0x2c3> 
   (cons #x4019db #x0e) ;;  
   (cons #x4019dc #x48) ;; mov -0x28(%rbp),%rdx 
   (cons #x4019dd #x8b) ;;  
   (cons #x4019de #x55) ;;  
   (cons #x4019df #xd8) ;;  
   (cons #x4019e0 #x48) ;; mov 0x50(%rdx),%rdx 
   (cons #x4019e1 #x8b) ;;  
   (cons #x4019e2 #x52) ;;  
   (cons #x4019e3 #x50) ;;  
   (cons #x4019e4 #x8b) ;; mov (%rdx),%edx 
   (cons #x4019e5 #x12) ;;  
   (cons #x4019e6 #xf7) ;; neg %edx 
   (cons #x4019e7 #xda) ;;  
   (cons #x4019e8 #xeb) ;; jmp 4019f4 <solve+0x2cd> 
   (cons #x4019e9 #x0a) ;;  
   (cons #x4019ea #x48) ;; mov -0x28(%rbp),%rdx 
   (cons #x4019eb #x8b) ;;  
   (cons #x4019ec #x55) ;;  
   (cons #x4019ed #xd8) ;;  
   (cons #x4019ee #x48) ;; mov 0x50(%rdx),%rdx 
   (cons #x4019ef #x8b) ;;  
   (cons #x4019f0 #x52) ;;  
   (cons #x4019f1 #x50) ;;  
   (cons #x4019f2 #x8b) ;; mov (%rdx),%edx 
   (cons #x4019f3 #x12) ;;  
   (cons #x4019f4 #x89) ;; mov %edx,(%rax) 
   (cons #x4019f5 #x10) ;;  
   (cons #x4019f6 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4019f7 #x8d) ;;  
   (cons #x4019f8 #x50) ;;  
   (cons #x4019f9 #x04) ;;  
   (cons #x4019fa #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x4019fb #x8b) ;;  
   (cons #x4019fc #x45) ;;  
   (cons #x4019fd #xd8) ;;  
   (cons #x4019fe #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x4019ff #x89) ;;  
   (cons #x401a00 #x90) ;;  
   (cons #x401a01 #x80) ;;  
   (cons #x401a02 #x00) ;;  
   (cons #x401a03 #x00) ;;  
   (cons #x401a04 #x00) ;;  
   (cons #x401a05 #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401a06 #x8b) ;;  
   (cons #x401a07 #x45) ;;  
   (cons #x401a08 #xd8) ;;  
   (cons #x401a09 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x401a0a #x8b) ;;  
   (cons #x401a0b #x48) ;;  
   (cons #x401a0c #x30) ;;  
   (cons #x401a0d #x48) ;; mov -0x28(%rbp),%rax 
   (cons #x401a0e #x8b) ;;  
   (cons #x401a0f #x45) ;;  
   (cons #x401a10 #xd8) ;;  
   (cons #x401a11 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x401a12 #x8b) ;;  
   (cons #x401a13 #x40) ;;  
   (cons #x401a14 #x50) ;;  
   (cons #x401a15 #x8b) ;; mov (%rax),%eax 
   (cons #x401a16 #x00) ;;  
   (cons #x401a17 #x89) ;; mov %eax,%edx 
   (cons #x401a18 #xc2) ;;  
   (cons #x401a19 #xc1) ;; sar $0x1f,%edx 
   (cons #x401a1a #xfa) ;;  
   (cons #x401a1b #x1f) ;;  
   (cons #x401a1c #x31) ;; xor %edx,%eax 
   (cons #x401a1d #xd0) ;;  
   (cons #x401a1e #x29) ;; sub %edx,%eax 
   (cons #x401a1f #xd0) ;;  
   (cons #x401a20 #x48) ;; cltq 
   (cons #x401a21 #x98) ;;  
   (cons #x401a22 #x48) ;; shl $0x2,%rax 
   (cons #x401a23 #xc1) ;;  
   (cons #x401a24 #xe0) ;;  
   (cons #x401a25 #x02) ;;  
   (cons #x401a26 #x48) ;; add %rcx,%rax 
   (cons #x401a27 #x01) ;;  
   (cons #x401a28 #xc8) ;;  
   (cons #x401a29 #xc7) ;; movl $0x0,(%rax) 
   (cons #x401a2a #x00) ;;  
   (cons #x401a2b #x00) ;;  
   (cons #x401a2c #x00) ;;  
   (cons #x401a2d #x00) ;;  
   (cons #x401a2e #x00) ;;  
   (cons #x401a2f #xe9) ;; jmpq 401748 <solve+0x21> 
   (cons #x401a30 #x14) ;;  
   (cons #x401a31 #xfd) ;;  
   (cons #x401a32 #xff) ;;  
   (cons #x401a33 #xff) ;;  
   (cons #x401a34 #x48) ;; add $0x28,%rsp 
   (cons #x401a35 #x83) ;;  
   (cons #x401a36 #xc4) ;;  
   (cons #x401a37 #x28) ;;  
   (cons #x401a38 #x5b) ;; pop %rbx 
   (cons #x401a39 #x5d) ;; pop %rbp 
   (cons #x401a3a #xc3) ;; retq 
   
;; Section: <parse>:


   (cons #x401a3b #x55) ;; push %rbp 
   (cons #x401a3c #x48) ;; mov %rsp,%rbp 
   (cons #x401a3d #x89) ;;  
   (cons #x401a3e #xe5) ;;  
   (cons #x401a3f #x53) ;; push %rbx 
   (cons #x401a40 #x48) ;; sub $0x40,%rsp 
   (cons #x401a41 #x83) ;;  
   (cons #x401a42 #xec) ;;  
   (cons #x401a43 #x40) ;;  
   (cons #x401a44 #x48) ;; mov %rdi,-0x40(%rbp) 
   (cons #x401a45 #x89) ;;  
   (cons #x401a46 #x7d) ;;  
   (cons #x401a47 #xc0) ;;  
   (cons #x401a48 #x48) ;; mov %rsi,-0x48(%rbp) 
   (cons #x401a49 #x89) ;;  
   (cons #x401a4a #x75) ;;  
   (cons #x401a4b #xb8) ;;  
   (cons #x401a4c #xc7) ;; movl $0x1,-0x18(%rbp) 
   (cons #x401a4d #x45) ;;  
   (cons #x401a4e #xe8) ;;  
   (cons #x401a4f #x01) ;;  
   (cons #x401a50 #x00) ;;  
   (cons #x401a51 #x00) ;;  
   (cons #x401a52 #x00) ;;  
   (cons #x401a53 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a54 #x8b) ;;  
   (cons #x401a55 #x45) ;;  
   (cons #x401a56 #xc0) ;;  
   (cons #x401a57 #xc7) ;; movl $0x4,0x8(%rax) 
   (cons #x401a58 #x40) ;;  
   (cons #x401a59 #x08) ;;  
   (cons #x401a5a #x04) ;;  
   (cons #x401a5b #x00) ;;  
   (cons #x401a5c #x00) ;;  
   (cons #x401a5d #x00) ;;  
   (cons #x401a5e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a5f #x8b) ;;  
   (cons #x401a60 #x45) ;;  
   (cons #x401a61 #xc0) ;;  
   (cons #x401a62 #xc7) ;; movl $0x8,0xc(%rax) 
   (cons #x401a63 #x40) ;;  
   (cons #x401a64 #x0c) ;;  
   (cons #x401a65 #x08) ;;  
   (cons #x401a66 #x00) ;;  
   (cons #x401a67 #x00) ;;  
   (cons #x401a68 #x00) ;;  
   (cons #x401a69 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a6a #x8b) ;;  
   (cons #x401a6b #x45) ;;  
   (cons #x401a6c #xc0) ;;  
   (cons #x401a6d #x8b) ;; mov 0xc(%rax),%eax 
   (cons #x401a6e #x40) ;;  
   (cons #x401a6f #x0c) ;;  
   (cons #x401a70 #x89) ;; mov %eax,-0x14(%rbp) 
   (cons #x401a71 #x45) ;;  
   (cons #x401a72 #xec) ;;  
   (cons #x401a73 #xc7) ;; movl $0x0,-0x10(%rbp) 
   (cons #x401a74 #x45) ;;  
   (cons #x401a75 #xf0) ;;  
   (cons #x401a76 #x00) ;;  
   (cons #x401a77 #x00) ;;  
   (cons #x401a78 #x00) ;;  
   (cons #x401a79 #x00) ;;  
   (cons #x401a7a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a7b #x8b) ;;  
   (cons #x401a7c #x45) ;;  
   (cons #x401a7d #xc0) ;;  
   (cons #x401a7e #x8b) ;; mov 0x8(%rax),%eax 
   (cons #x401a7f #x40) ;;  
   (cons #x401a80 #x08) ;;  
   (cons #x401a81 #x89) ;; mov %eax,-0xc(%rbp) 
   (cons #x401a82 #x45) ;;  
   (cons #x401a83 #xf4) ;;  
   (cons #x401a84 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a85 #x8b) ;;  
   (cons #x401a86 #x45) ;;  
   (cons #x401a87 #xc0) ;;  
   (cons #x401a88 #xc7) ;; movl $0x0,0x10(%rax) 
   (cons #x401a89 #x40) ;;  
   (cons #x401a8a #x10) ;;  
   (cons #x401a8b #x00) ;;  
   (cons #x401a8c #x00) ;;  
   (cons #x401a8d #x00) ;;  
   (cons #x401a8e #x00) ;;  
   (cons #x401a8f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a90 #x8b) ;;  
   (cons #x401a91 #x45) ;;  
   (cons #x401a92 #xc0) ;;  
   (cons #x401a93 #xc7) ;; movl $0x0,0x1c(%rax) 
   (cons #x401a94 #x40) ;;  
   (cons #x401a95 #x1c) ;;  
   (cons #x401a96 #x00) ;;  
   (cons #x401a97 #x00) ;;  
   (cons #x401a98 #x00) ;;  
   (cons #x401a99 #x00) ;;  
   (cons #x401a9a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401a9b #x8b) ;;  
   (cons #x401a9c #x45) ;;  
   (cons #x401a9d #xc0) ;;  
   (cons #x401a9e #xc7) ;; movl $0x0,0x24(%rax) 
   (cons #x401a9f #x40) ;;  
   (cons #x401aa0 #x24) ;;  
   (cons #x401aa1 #x00) ;;  
   (cons #x401aa2 #x00) ;;  
   (cons #x401aa3 #x00) ;;  
   (cons #x401aa4 #x00) ;;  
   (cons #x401aa5 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401aa6 #x8b) ;;  
   (cons #x401aa7 #x45) ;;  
   (cons #x401aa8 #xc0) ;;  
   (cons #x401aa9 #xc7) ;; movl $0x0,0x20(%rax) 
   (cons #x401aaa #x40) ;;  
   (cons #x401aab #x20) ;;  
   (cons #x401aac #x00) ;;  
   (cons #x401aad #x00) ;;  
   (cons #x401aae #x00) ;;  
   (cons #x401aaf #x00) ;;  
   (cons #x401ab0 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ab1 #x8b) ;;  
   (cons #x401ab2 #x45) ;;  
   (cons #x401ab3 #xc0) ;;  
   (cons #x401ab4 #x8b) ;; mov 0xc(%rax),%eax 
   (cons #x401ab5 #x40) ;;  
   (cons #x401ab6 #x0c) ;;  
   (cons #x401ab7 #x83) ;; add $0x2,%eax 
   (cons #x401ab8 #xc0) ;;  
   (cons #x401ab9 #x02) ;;  
   (cons #x401aba #x89) ;; mov %eax,%edx 
   (cons #x401abb #xc2) ;;  
   (cons #x401abc #xc1) ;; sar $0x2,%edx 
   (cons #x401abd #xfa) ;;  
   (cons #x401abe #x02) ;;  
   (cons #x401abf #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ac0 #x8b) ;;  
   (cons #x401ac1 #x45) ;;  
   (cons #x401ac2 #xc0) ;;  
   (cons #x401ac3 #x89) ;; mov %edx,0x18(%rax) 
   (cons #x401ac4 #x50) ;;  
   (cons #x401ac5 #x18) ;;  
   (cons #x401ac6 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401ac7 #x45) ;;  
   (cons #x401ac8 #xf4) ;;  
   (cons #x401ac9 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401aca #x50) ;;  
   (cons #x401acb #x01) ;;  
   (cons #x401acc #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401acd #x8b) ;;  
   (cons #x401ace #x45) ;;  
   (cons #x401acf #xc0) ;;  
   (cons #x401ad0 #x89) ;; mov %edx,%esi 
   (cons #x401ad1 #xd6) ;;  
   (cons #x401ad2 #x48) ;; mov %rax,%rdi 
   (cons #x401ad3 #x89) ;;  
   (cons #x401ad4 #xc7) ;;  
   (cons #x401ad5 #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401ad6 #xda) ;;  
   (cons #x401ad7 #xe9) ;;  
   (cons #x401ad8 #xff) ;;  
   (cons #x401ad9 #xff) ;;  
   (cons #x401ada #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401adb #x8b) ;;  
   (cons #x401adc #x55) ;;  
   (cons #x401add #xc0) ;;  
   (cons #x401ade #x48) ;; mov %rax,0x28(%rdx) 
   (cons #x401adf #x89) ;;  
   (cons #x401ae0 #x42) ;;  
   (cons #x401ae1 #x28) ;;  
   (cons #x401ae2 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401ae3 #x45) ;;  
   (cons #x401ae4 #xf4) ;;  
   (cons #x401ae5 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401ae6 #x50) ;;  
   (cons #x401ae7 #x01) ;;  
   (cons #x401ae8 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ae9 #x8b) ;;  
   (cons #x401aea #x45) ;;  
   (cons #x401aeb #xc0) ;;  
   (cons #x401aec #x89) ;; mov %edx,%esi 
   (cons #x401aed #xd6) ;;  
   (cons #x401aee #x48) ;; mov %rax,%rdi 
   (cons #x401aef #x89) ;;  
   (cons #x401af0 #xc7) ;;  
   (cons #x401af1 #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401af2 #xbe) ;;  
   (cons #x401af3 #xe9) ;;  
   (cons #x401af4 #xff) ;;  
   (cons #x401af5 #xff) ;;  
   (cons #x401af6 #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401af7 #x8b) ;;  
   (cons #x401af8 #x55) ;;  
   (cons #x401af9 #xc0) ;;  
   (cons #x401afa #x48) ;; mov %rax,0x68(%rdx) 
   (cons #x401afb #x89) ;;  
   (cons #x401afc #x42) ;;  
   (cons #x401afd #x68) ;;  
   (cons #x401afe #x8b) ;; mov -0xc(%rbp),%edx 
   (cons #x401aff #x55) ;;  
   (cons #x401b00 #xf4) ;;  
   (cons #x401b01 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b02 #x8b) ;;  
   (cons #x401b03 #x45) ;;  
   (cons #x401b04 #xc0) ;;  
   (cons #x401b05 #x89) ;; mov %edx,%esi 
   (cons #x401b06 #xd6) ;;  
   (cons #x401b07 #x48) ;; mov %rax,%rdi 
   (cons #x401b08 #x89) ;;  
   (cons #x401b09 #xc7) ;;  
   (cons #x401b0a #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401b0b #xa5) ;;  
   (cons #x401b0c #xe9) ;;  
   (cons #x401b0d #xff) ;;  
   (cons #x401b0e #xff) ;;  
   (cons #x401b0f #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401b10 #x8b) ;;  
   (cons #x401b11 #x55) ;;  
   (cons #x401b12 #xc0) ;;  
   (cons #x401b13 #x48) ;; mov %rax,0x50(%rdx) 
   (cons #x401b14 #x89) ;;  
   (cons #x401b15 #x42) ;;  
   (cons #x401b16 #x50) ;;  
   (cons #x401b17 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401b18 #x45) ;;  
   (cons #x401b19 #xf4) ;;  
   (cons #x401b1a #x8d) ;; lea -0x1(%rax),%edx 
   (cons #x401b1b #x50) ;;  
   (cons #x401b1c #xff) ;;  
   (cons #x401b1d #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b1e #x8b) ;;  
   (cons #x401b1f #x45) ;;  
   (cons #x401b20 #xc0) ;;  
   (cons #x401b21 #x89) ;; mov %edx,0x58(%rax) 
   (cons #x401b22 #x50) ;;  
   (cons #x401b23 #x58) ;;  
   (cons #x401b24 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401b25 #x45) ;;  
   (cons #x401b26 #xf4) ;;  
   (cons #x401b27 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401b28 #x50) ;;  
   (cons #x401b29 #x01) ;;  
   (cons #x401b2a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b2b #x8b) ;;  
   (cons #x401b2c #x45) ;;  
   (cons #x401b2d #xc0) ;;  
   (cons #x401b2e #x89) ;; mov %edx,%esi 
   (cons #x401b2f #xd6) ;;  
   (cons #x401b30 #x48) ;; mov %rax,%rdi 
   (cons #x401b31 #x89) ;;  
   (cons #x401b32 #xc7) ;;  
   (cons #x401b33 #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401b34 #x7c) ;;  
   (cons #x401b35 #xe9) ;;  
   (cons #x401b36 #xff) ;;  
   (cons #x401b37 #xff) ;;  
   (cons #x401b38 #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401b39 #x8b) ;;  
   (cons #x401b3a #x55) ;;  
   (cons #x401b3b #xc0) ;;  
   (cons #x401b3c #x48) ;; mov %rax,0x60(%rdx) 
   (cons #x401b3d #x89) ;;  
   (cons #x401b3e #x42) ;;  
   (cons #x401b3f #x60) ;;  
   (cons #x401b40 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401b41 #x45) ;;  
   (cons #x401b42 #xf4) ;;  
   (cons #x401b43 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401b44 #x50) ;;  
   (cons #x401b45 #x01) ;;  
   (cons #x401b46 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b47 #x8b) ;;  
   (cons #x401b48 #x45) ;;  
   (cons #x401b49 #xc0) ;;  
   (cons #x401b4a #x89) ;; mov %edx,%esi 
   (cons #x401b4b #xd6) ;;  
   (cons #x401b4c #x48) ;; mov %rax,%rdi 
   (cons #x401b4d #x89) ;;  
   (cons #x401b4e #xc7) ;;  
   (cons #x401b4f #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401b50 #x60) ;;  
   (cons #x401b51 #xe9) ;;  
   (cons #x401b52 #xff) ;;  
   (cons #x401b53 #xff) ;;  
   (cons #x401b54 #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401b55 #x8b) ;;  
   (cons #x401b56 #x55) ;;  
   (cons #x401b57 #xc0) ;;  
   (cons #x401b58 #x48) ;; mov %rax,0x30(%rdx) 
   (cons #x401b59 #x89) ;;  
   (cons #x401b5a #x42) ;;  
   (cons #x401b5b #x30) ;;  
   (cons #x401b5c #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401b5d #x45) ;;  
   (cons #x401b5e #xf4) ;;  
   (cons #x401b5f #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401b60 #x50) ;;  
   (cons #x401b61 #x01) ;;  
   (cons #x401b62 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b63 #x8b) ;;  
   (cons #x401b64 #x45) ;;  
   (cons #x401b65 #xc0) ;;  
   (cons #x401b66 #x89) ;; mov %edx,%esi 
   (cons #x401b67 #xd6) ;;  
   (cons #x401b68 #x48) ;; mov %rax,%rdi 
   (cons #x401b69 #x89) ;;  
   (cons #x401b6a #xc7) ;;  
   (cons #x401b6b #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401b6c #x44) ;;  
   (cons #x401b6d #xe9) ;;  
   (cons #x401b6e #xff) ;;  
   (cons #x401b6f #xff) ;;  
   (cons #x401b70 #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401b71 #x8b) ;;  
   (cons #x401b72 #x55) ;;  
   (cons #x401b73 #xc0) ;;  
   (cons #x401b74 #x48) ;; mov %rax,0x38(%rdx) 
   (cons #x401b75 #x89) ;;  
   (cons #x401b76 #x42) ;;  
   (cons #x401b77 #x38) ;;  
   (cons #x401b78 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b79 #x8b) ;;  
   (cons #x401b7a #x45) ;;  
   (cons #x401b7b #xc0) ;;  
   (cons #x401b7c #x48) ;; mov 0x38(%rax),%rdx 
   (cons #x401b7d #x8b) ;;  
   (cons #x401b7e #x50) ;;  
   (cons #x401b7f #x38) ;;  
   (cons #x401b80 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b81 #x8b) ;;  
   (cons #x401b82 #x45) ;;  
   (cons #x401b83 #xc0) ;;  
   (cons #x401b84 #x48) ;; mov %rdx,0x70(%rax) 
   (cons #x401b85 #x89) ;;  
   (cons #x401b86 #x50) ;;  
   (cons #x401b87 #x70) ;;  
   (cons #x401b88 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b89 #x8b) ;;  
   (cons #x401b8a #x45) ;;  
   (cons #x401b8b #xc0) ;;  
   (cons #x401b8c #x48) ;; mov 0x38(%rax),%rdx 
   (cons #x401b8d #x8b) ;;  
   (cons #x401b8e #x50) ;;  
   (cons #x401b8f #x38) ;;  
   (cons #x401b90 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b91 #x8b) ;;  
   (cons #x401b92 #x45) ;;  
   (cons #x401b93 #xc0) ;;  
   (cons #x401b94 #x48) ;; mov %rdx,0x78(%rax) 
   (cons #x401b95 #x89) ;;  
   (cons #x401b96 #x50) ;;  
   (cons #x401b97 #x78) ;;  
   (cons #x401b98 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401b99 #x8b) ;;  
   (cons #x401b9a #x45) ;;  
   (cons #x401b9b #xc0) ;;  
   (cons #x401b9c #x48) ;; mov 0x38(%rax),%rdx 
   (cons #x401b9d #x8b) ;;  
   (cons #x401b9e #x50) ;;  
   (cons #x401b9f #x38) ;;  
   (cons #x401ba0 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ba1 #x8b) ;;  
   (cons #x401ba2 #x45) ;;  
   (cons #x401ba3 #xc0) ;;  
   (cons #x401ba4 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x401ba5 #x89) ;;  
   (cons #x401ba6 #x90) ;;  
   (cons #x401ba7 #x80) ;;  
   (cons #x401ba8 #x00) ;;  
   (cons #x401ba9 #x00) ;;  
   (cons #x401baa #x00) ;;  
   (cons #x401bab #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401bac #x45) ;;  
   (cons #x401bad #xf4) ;;  
   (cons #x401bae #x01) ;; add %eax,%eax 
   (cons #x401baf #xc0) ;;  
   (cons #x401bb0 #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401bb1 #x50) ;;  
   (cons #x401bb2 #x01) ;;  
   (cons #x401bb3 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401bb4 #x8b) ;;  
   (cons #x401bb5 #x45) ;;  
   (cons #x401bb6 #xc0) ;;  
   (cons #x401bb7 #x89) ;; mov %edx,%esi 
   (cons #x401bb8 #xd6) ;;  
   (cons #x401bb9 #x48) ;; mov %rax,%rdi 
   (cons #x401bba #x89) ;;  
   (cons #x401bbb #xc7) ;;  
   (cons #x401bbc #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401bbd #xf3) ;;  
   (cons #x401bbe #xe8) ;;  
   (cons #x401bbf #xff) ;;  
   (cons #x401bc0 #xff) ;;  
   (cons #x401bc1 #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401bc2 #x8b) ;;  
   (cons #x401bc3 #x55) ;;  
   (cons #x401bc4 #xc0) ;;  
   (cons #x401bc5 #x48) ;; mov %rax,0x40(%rdx) 
   (cons #x401bc6 #x89) ;;  
   (cons #x401bc7 #x42) ;;  
   (cons #x401bc8 #x40) ;;  
   (cons #x401bc9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401bca #x8b) ;;  
   (cons #x401bcb #x45) ;;  
   (cons #x401bcc #xc0) ;;  
   (cons #x401bcd #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401bce #x8b) ;;  
   (cons #x401bcf #x40) ;;  
   (cons #x401bd0 #x40) ;;  
   (cons #x401bd1 #x8b) ;; mov -0xc(%rbp),%edx 
   (cons #x401bd2 #x55) ;;  
   (cons #x401bd3 #xf4) ;;  
   (cons #x401bd4 #x48) ;; movslq %edx,%rdx 
   (cons #x401bd5 #x63) ;;  
   (cons #x401bd6 #xd2) ;;  
   (cons #x401bd7 #x48) ;; shl $0x2,%rdx 
   (cons #x401bd8 #xc1) ;;  
   (cons #x401bd9 #xe2) ;;  
   (cons #x401bda #x02) ;;  
   (cons #x401bdb #x48) ;; add %rax,%rdx 
   (cons #x401bdc #x01) ;;  
   (cons #x401bdd #xc2) ;;  
   (cons #x401bde #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401bdf #x8b) ;;  
   (cons #x401be0 #x45) ;;  
   (cons #x401be1 #xc0) ;;  
   (cons #x401be2 #x48) ;; mov %rdx,0x40(%rax) 
   (cons #x401be3 #x89) ;;  
   (cons #x401be4 #x50) ;;  
   (cons #x401be5 #x40) ;;  
   (cons #x401be6 #x8b) ;; mov -0xc(%rbp),%eax 
   (cons #x401be7 #x45) ;;  
   (cons #x401be8 #xf4) ;;  
   (cons #x401be9 #x01) ;; add %eax,%eax 
   (cons #x401bea #xc0) ;;  
   (cons #x401beb #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401bec #x50) ;;  
   (cons #x401bed #x01) ;;  
   (cons #x401bee #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401bef #x8b) ;;  
   (cons #x401bf0 #x45) ;;  
   (cons #x401bf1 #xc0) ;;  
   (cons #x401bf2 #x89) ;; mov %edx,%esi 
   (cons #x401bf3 #xd6) ;;  
   (cons #x401bf4 #x48) ;; mov %rax,%rdi 
   (cons #x401bf5 #x89) ;;  
   (cons #x401bf6 #xc7) ;;  
   (cons #x401bf7 #xe8) ;; callq 4004b4 <getMemory> 
   (cons #x401bf8 #xb8) ;;  
   (cons #x401bf9 #xe8) ;;  
   (cons #x401bfa #xff) ;;  
   (cons #x401bfb #xff) ;;  
   (cons #x401bfc #x48) ;; mov -0x40(%rbp),%rdx 
   (cons #x401bfd #x8b) ;;  
   (cons #x401bfe #x55) ;;  
   (cons #x401bff #xc0) ;;  
   (cons #x401c00 #x48) ;; mov %rax,0x48(%rdx) 
   (cons #x401c01 #x89) ;;  
   (cons #x401c02 #x42) ;;  
   (cons #x401c03 #x48) ;;  
   (cons #x401c04 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c05 #x8b) ;;  
   (cons #x401c06 #x45) ;;  
   (cons #x401c07 #xc0) ;;  
   (cons #x401c08 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x401c09 #x8b) ;;  
   (cons #x401c0a #x40) ;;  
   (cons #x401c0b #x48) ;;  
   (cons #x401c0c #x8b) ;; mov -0xc(%rbp),%edx 
   (cons #x401c0d #x55) ;;  
   (cons #x401c0e #xf4) ;;  
   (cons #x401c0f #x48) ;; movslq %edx,%rdx 
   (cons #x401c10 #x63) ;;  
   (cons #x401c11 #xd2) ;;  
   (cons #x401c12 #x48) ;; shl $0x2,%rdx 
   (cons #x401c13 #xc1) ;;  
   (cons #x401c14 #xe2) ;;  
   (cons #x401c15 #x02) ;;  
   (cons #x401c16 #x48) ;; add %rax,%rdx 
   (cons #x401c17 #x01) ;;  
   (cons #x401c18 #xc2) ;;  
   (cons #x401c19 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c1a #x8b) ;;  
   (cons #x401c1b #x45) ;;  
   (cons #x401c1c #xc0) ;;  
   (cons #x401c1d #x48) ;; mov %rdx,0x48(%rax) 
   (cons #x401c1e #x89) ;;  
   (cons #x401c1f #x50) ;;  
   (cons #x401c20 #x48) ;;  
   (cons #x401c21 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c22 #x8b) ;;  
   (cons #x401c23 #x45) ;;  
   (cons #x401c24 #xc0) ;;  
   (cons #x401c25 #x48) ;; mov (%rax),%rdx 
   (cons #x401c26 #x8b) ;;  
   (cons #x401c27 #x10) ;;  
   (cons #x401c28 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c29 #x8b) ;;  
   (cons #x401c2a #x45) ;;  
   (cons #x401c2b #xc0) ;;  
   (cons #x401c2c #x8b) ;; mov 0x10(%rax),%eax 
   (cons #x401c2d #x40) ;;  
   (cons #x401c2e #x10) ;;  
   (cons #x401c2f #x48) ;; movslq %eax,%rcx 
   (cons #x401c30 #x63) ;;  
   (cons #x401c31 #xc8) ;;  
   (cons #x401c32 #x48) ;; shl $0x2,%rcx 
   (cons #x401c33 #xc1) ;;  
   (cons #x401c34 #xe1) ;;  
   (cons #x401c35 #x02) ;;  
   (cons #x401c36 #x48) ;; add %rcx,%rdx 
   (cons #x401c37 #x01) ;;  
   (cons #x401c38 #xca) ;;  
   (cons #x401c39 #xc7) ;; movl $0x0,(%rdx) 
   (cons #x401c3a #x02) ;;  
   (cons #x401c3b #x00) ;;  
   (cons #x401c3c #x00) ;;  
   (cons #x401c3d #x00) ;;  
   (cons #x401c3e #x00) ;;  
   (cons #x401c3f #x8d) ;; lea 0x1(%rax),%edx 
   (cons #x401c40 #x50) ;;  
   (cons #x401c41 #x01) ;;  
   (cons #x401c42 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c43 #x8b) ;;  
   (cons #x401c44 #x45) ;;  
   (cons #x401c45 #xc0) ;;  
   (cons #x401c46 #x89) ;; mov %edx,0x10(%rax) 
   (cons #x401c47 #x50) ;;  
   (cons #x401c48 #x10) ;;  
   (cons #x401c49 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c4a #x8b) ;;  
   (cons #x401c4b #x45) ;;  
   (cons #x401c4c #xc0) ;;  
   (cons #x401c4d #x48) ;; mov 0x30(%rax),%rax 
   (cons #x401c4e #x8b) ;;  
   (cons #x401c4f #x40) ;;  
   (cons #x401c50 #x30) ;;  
   (cons #x401c51 #xc7) ;; movl $0x0,(%rax) 
   (cons #x401c52 #x00) ;;  
   (cons #x401c53 #x00) ;;  
   (cons #x401c54 #x00) ;;  
   (cons #x401c55 #x00) ;;  
   (cons #x401c56 #x00) ;;  
   (cons #x401c57 #xc7) ;; movl $0x1,-0x1c(%rbp) 
   (cons #x401c58 #x45) ;;  
   (cons #x401c59 #xe4) ;;  
   (cons #x401c5a #x01) ;;  
   (cons #x401c5b #x00) ;;  
   (cons #x401c5c #x00) ;;  
   (cons #x401c5d #x00) ;;  
   (cons #x401c5e #xe9) ;; jmpq 401d7e <parse+0x343> 
   (cons #x401c5f #x1b) ;;  
   (cons #x401c60 #x01) ;;  
   (cons #x401c61 #x00) ;;  
   (cons #x401c62 #x00) ;;  
   (cons #x401c63 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c64 #x8b) ;;  
   (cons #x401c65 #x45) ;;  
   (cons #x401c66 #xc0) ;;  
   (cons #x401c67 #x48) ;; mov 0x50(%rax),%rax 
   (cons #x401c68 #x8b) ;;  
   (cons #x401c69 #x40) ;;  
   (cons #x401c6a #x50) ;;  
   (cons #x401c6b #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401c6c #x55) ;;  
   (cons #x401c6d #xe4) ;;  
   (cons #x401c6e #x48) ;; movslq %edx,%rdx 
   (cons #x401c6f #x63) ;;  
   (cons #x401c70 #xd2) ;;  
   (cons #x401c71 #x48) ;; sub $0x1,%rdx 
   (cons #x401c72 #x83) ;;  
   (cons #x401c73 #xea) ;;  
   (cons #x401c74 #x01) ;;  
   (cons #x401c75 #x48) ;; shl $0x2,%rdx 
   (cons #x401c76 #xc1) ;;  
   (cons #x401c77 #xe2) ;;  
   (cons #x401c78 #x02) ;;  
   (cons #x401c79 #x48) ;; add %rax,%rdx 
   (cons #x401c7a #x01) ;;  
   (cons #x401c7b #xc2) ;;  
   (cons #x401c7c #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401c7d #x45) ;;  
   (cons #x401c7e #xe4) ;;  
   (cons #x401c7f #x89) ;; mov %eax,(%rdx) 
   (cons #x401c80 #x02) ;;  
   (cons #x401c81 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c82 #x8b) ;;  
   (cons #x401c83 #x45) ;;  
   (cons #x401c84 #xc0) ;;  
   (cons #x401c85 #x48) ;; mov 0x60(%rax),%rax 
   (cons #x401c86 #x8b) ;;  
   (cons #x401c87 #x40) ;;  
   (cons #x401c88 #x60) ;;  
   (cons #x401c89 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401c8a #x55) ;;  
   (cons #x401c8b #xe4) ;;  
   (cons #x401c8c #x48) ;; movslq %edx,%rdx 
   (cons #x401c8d #x63) ;;  
   (cons #x401c8e #xd2) ;;  
   (cons #x401c8f #x48) ;; shl $0x2,%rdx 
   (cons #x401c90 #xc1) ;;  
   (cons #x401c91 #xe2) ;;  
   (cons #x401c92 #x02) ;;  
   (cons #x401c93 #x48) ;; add %rdx,%rax 
   (cons #x401c94 #x01) ;;  
   (cons #x401c95 #xd0) ;;  
   (cons #x401c96 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401c97 #x55) ;;  
   (cons #x401c98 #xe4) ;;  
   (cons #x401c99 #x83) ;; sub $0x1,%edx 
   (cons #x401c9a #xea) ;;  
   (cons #x401c9b #x01) ;;  
   (cons #x401c9c #x89) ;; mov %edx,(%rax) 
   (cons #x401c9d #x10) ;;  
   (cons #x401c9e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401c9f #x8b) ;;  
   (cons #x401ca0 #x45) ;;  
   (cons #x401ca1 #xc0) ;;  
   (cons #x401ca2 #x48) ;; mov 0x28(%rax),%rax 
   (cons #x401ca3 #x8b) ;;  
   (cons #x401ca4 #x40) ;;  
   (cons #x401ca5 #x28) ;;  
   (cons #x401ca6 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401ca7 #x55) ;;  
   (cons #x401ca8 #xe4) ;;  
   (cons #x401ca9 #x48) ;; movslq %edx,%rdx 
   (cons #x401caa #x63) ;;  
   (cons #x401cab #xd2) ;;  
   (cons #x401cac #x48) ;; shl $0x2,%rdx 
   (cons #x401cad #xc1) ;;  
   (cons #x401cae #xe2) ;;  
   (cons #x401caf #x02) ;;  
   (cons #x401cb0 #x48) ;; add %rdx,%rax 
   (cons #x401cb1 #x01) ;;  
   (cons #x401cb2 #xd0) ;;  
   (cons #x401cb3 #xc7) ;; movl $0x0,(%rax) 
   (cons #x401cb4 #x00) ;;  
   (cons #x401cb5 #x00) ;;  
   (cons #x401cb6 #x00) ;;  
   (cons #x401cb7 #x00) ;;  
   (cons #x401cb8 #x00) ;;  
   (cons #x401cb9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401cba #x8b) ;;  
   (cons #x401cbb #x45) ;;  
   (cons #x401cbc #xc0) ;;  
   (cons #x401cbd #x48) ;; mov 0x68(%rax),%rax 
   (cons #x401cbe #x8b) ;;  
   (cons #x401cbf #x40) ;;  
   (cons #x401cc0 #x68) ;;  
   (cons #x401cc1 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401cc2 #x55) ;;  
   (cons #x401cc3 #xe4) ;;  
   (cons #x401cc4 #x48) ;; movslq %edx,%rdx 
   (cons #x401cc5 #x63) ;;  
   (cons #x401cc6 #xd2) ;;  
   (cons #x401cc7 #x48) ;; shl $0x2,%rdx 
   (cons #x401cc8 #xc1) ;;  
   (cons #x401cc9 #xe2) ;;  
   (cons #x401cca #x02) ;;  
   (cons #x401ccb #x48) ;; add %rdx,%rax 
   (cons #x401ccc #x01) ;;  
   (cons #x401ccd #xd0) ;;  
   (cons #x401cce #xc7) ;; movl $0x1,(%rax) 
   (cons #x401ccf #x00) ;;  
   (cons #x401cd0 #x01) ;;  
   (cons #x401cd1 #x00) ;;  
   (cons #x401cd2 #x00) ;;  
   (cons #x401cd3 #x00) ;;  
   (cons #x401cd4 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401cd5 #x8b) ;;  
   (cons #x401cd6 #x45) ;;  
   (cons #x401cd7 #xc0) ;;  
   (cons #x401cd8 #x48) ;; mov 0x38(%rax),%rax 
   (cons #x401cd9 #x8b) ;;  
   (cons #x401cda #x40) ;;  
   (cons #x401cdb #x38) ;;  
   (cons #x401cdc #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401cdd #x55) ;;  
   (cons #x401cde #xe4) ;;  
   (cons #x401cdf #x48) ;; movslq %edx,%rdx 
   (cons #x401ce0 #x63) ;;  
   (cons #x401ce1 #xd2) ;;  
   (cons #x401ce2 #x48) ;; sub $0x1,%rdx 
   (cons #x401ce3 #x83) ;;  
   (cons #x401ce4 #xea) ;;  
   (cons #x401ce5 #x01) ;;  
   (cons #x401ce6 #x48) ;; shl $0x2,%rdx 
   (cons #x401ce7 #xc1) ;;  
   (cons #x401ce8 #xe2) ;;  
   (cons #x401ce9 #x02) ;;  
   (cons #x401cea #x48) ;; add %rdx,%rax 
   (cons #x401ceb #x01) ;;  
   (cons #x401cec #xd0) ;;  
   (cons #x401ced #xc7) ;; movl $0x0,(%rax) 
   (cons #x401cee #x00) ;;  
   (cons #x401cef #x00) ;;  
   (cons #x401cf0 #x00) ;;  
   (cons #x401cf1 #x00) ;;  
   (cons #x401cf2 #x00) ;;  
   (cons #x401cf3 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401cf4 #x8b) ;;  
   (cons #x401cf5 #x45) ;;  
   (cons #x401cf6 #xc0) ;;  
   (cons #x401cf7 #x48) ;; mov 0x30(%rax),%rax 
   (cons #x401cf8 #x8b) ;;  
   (cons #x401cf9 #x40) ;;  
   (cons #x401cfa #x30) ;;  
   (cons #x401cfb #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401cfc #x55) ;;  
   (cons #x401cfd #xe4) ;;  
   (cons #x401cfe #x48) ;; movslq %edx,%rdx 
   (cons #x401cff #x63) ;;  
   (cons #x401d00 #xd2) ;;  
   (cons #x401d01 #x48) ;; shl $0x2,%rdx 
   (cons #x401d02 #xc1) ;;  
   (cons #x401d03 #xe2) ;;  
   (cons #x401d04 #x02) ;;  
   (cons #x401d05 #x48) ;; add %rdx,%rax 
   (cons #x401d06 #x01) ;;  
   (cons #x401d07 #xd0) ;;  
   (cons #x401d08 #xc7) ;; movl $0x0,(%rax) 
   (cons #x401d09 #x00) ;;  
   (cons #x401d0a #x00) ;;  
   (cons #x401d0b #x00) ;;  
   (cons #x401d0c #x00) ;;  
   (cons #x401d0d #x00) ;;  
   (cons #x401d0e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401d0f #x8b) ;;  
   (cons #x401d10 #x45) ;;  
   (cons #x401d11 #xc0) ;;  
   (cons #x401d12 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401d13 #x8b) ;;  
   (cons #x401d14 #x40) ;;  
   (cons #x401d15 #x40) ;;  
   (cons #x401d16 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401d17 #x55) ;;  
   (cons #x401d18 #xe4) ;;  
   (cons #x401d19 #x48) ;; movslq %edx,%rdx 
   (cons #x401d1a #x63) ;;  
   (cons #x401d1b #xd2) ;;  
   (cons #x401d1c #x48) ;; shl $0x2,%rdx 
   (cons #x401d1d #xc1) ;;  
   (cons #x401d1e #xe2) ;;  
   (cons #x401d1f #x02) ;;  
   (cons #x401d20 #x48) ;; add %rax,%rdx 
   (cons #x401d21 #x01) ;;  
   (cons #x401d22 #xc2) ;;  
   (cons #x401d23 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401d24 #x8b) ;;  
   (cons #x401d25 #x45) ;;  
   (cons #x401d26 #xc0) ;;  
   (cons #x401d27 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401d28 #x8b) ;;  
   (cons #x401d29 #x40) ;;  
   (cons #x401d2a #x40) ;;  
   (cons #x401d2b #x8b) ;; mov -0x1c(%rbp),%ecx 
   (cons #x401d2c #x4d) ;;  
   (cons #x401d2d #xe4) ;;  
   (cons #x401d2e #xf7) ;; neg %ecx 
   (cons #x401d2f #xd9) ;;  
   (cons #x401d30 #x48) ;; movslq %ecx,%rcx 
   (cons #x401d31 #x63) ;;  
   (cons #x401d32 #xc9) ;;  
   (cons #x401d33 #x48) ;; shl $0x2,%rcx 
   (cons #x401d34 #xc1) ;;  
   (cons #x401d35 #xe1) ;;  
   (cons #x401d36 #x02) ;;  
   (cons #x401d37 #x48) ;; add %rcx,%rax 
   (cons #x401d38 #x01) ;;  
   (cons #x401d39 #xc8) ;;  
   (cons #x401d3a #xc7) ;; movl $0x0,(%rax) 
   (cons #x401d3b #x00) ;;  
   (cons #x401d3c #x00) ;;  
   (cons #x401d3d #x00) ;;  
   (cons #x401d3e #x00) ;;  
   (cons #x401d3f #x00) ;;  
   (cons #x401d40 #x8b) ;; mov (%rax),%eax 
   (cons #x401d41 #x00) ;;  
   (cons #x401d42 #x89) ;; mov %eax,(%rdx) 
   (cons #x401d43 #x02) ;;  
   (cons #x401d44 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401d45 #x8b) ;;  
   (cons #x401d46 #x45) ;;  
   (cons #x401d47 #xc0) ;;  
   (cons #x401d48 #x48) ;; mov 0x48(%rax),%rax 
   (cons #x401d49 #x8b) ;;  
   (cons #x401d4a #x40) ;;  
   (cons #x401d4b #x48) ;;  
   (cons #x401d4c #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401d4d #x55) ;;  
   (cons #x401d4e #xe4) ;;  
   (cons #x401d4f #x48) ;; movslq %edx,%rdx 
   (cons #x401d50 #x63) ;;  
   (cons #x401d51 #xd2) ;;  
   (cons #x401d52 #x48) ;; shl $0x2,%rdx 
   (cons #x401d53 #xc1) ;;  
   (cons #x401d54 #xe2) ;;  
   (cons #x401d55 #x02) ;;  
   (cons #x401d56 #x48) ;; add %rax,%rdx 
   (cons #x401d57 #x01) ;;  
   (cons #x401d58 #xc2) ;;  
   (cons #x401d59 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401d5a #x8b) ;;  
   (cons #x401d5b #x45) ;;  
   (cons #x401d5c #xc0) ;;  
   (cons #x401d5d #x48) ;; mov 0x48(%rax),%rax 
   (cons #x401d5e #x8b) ;;  
   (cons #x401d5f #x40) ;;  
   (cons #x401d60 #x48) ;;  
   (cons #x401d61 #x8b) ;; mov -0x1c(%rbp),%ecx 
   (cons #x401d62 #x4d) ;;  
   (cons #x401d63 #xe4) ;;  
   (cons #x401d64 #xf7) ;; neg %ecx 
   (cons #x401d65 #xd9) ;;  
   (cons #x401d66 #x48) ;; movslq %ecx,%rcx 
   (cons #x401d67 #x63) ;;  
   (cons #x401d68 #xc9) ;;  
   (cons #x401d69 #x48) ;; shl $0x2,%rcx 
   (cons #x401d6a #xc1) ;;  
   (cons #x401d6b #xe1) ;;  
   (cons #x401d6c #x02) ;;  
   (cons #x401d6d #x48) ;; add %rcx,%rax 
   (cons #x401d6e #x01) ;;  
   (cons #x401d6f #xc8) ;;  
   (cons #x401d70 #xc7) ;; movl $0xfffffff7,(%rax) 
   (cons #x401d71 #x00) ;;  
   (cons #x401d72 #xf7) ;;  
   (cons #x401d73 #xff) ;;  
   (cons #x401d74 #xff) ;;  
   (cons #x401d75 #xff) ;;  
   (cons #x401d76 #x8b) ;; mov (%rax),%eax 
   (cons #x401d77 #x00) ;;  
   (cons #x401d78 #x89) ;; mov %eax,(%rdx) 
   (cons #x401d79 #x02) ;;  
   (cons #x401d7a #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401d7b #x45) ;;  
   (cons #x401d7c #xe4) ;;  
   (cons #x401d7d #x01) ;;  
   (cons #x401d7e #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401d7f #x45) ;;  
   (cons #x401d80 #xe4) ;;  
   (cons #x401d81 #x3b) ;; cmp -0xc(%rbp),%eax 
   (cons #x401d82 #x45) ;;  
   (cons #x401d83 #xf4) ;;  
   (cons #x401d84 #x0f) ;; jle 401c63 <parse+0x228> 
   (cons #x401d85 #x8e) ;;  
   (cons #x401d86 #xd9) ;;  
   (cons #x401d87 #xfe) ;;  
   (cons #x401d88 #xff) ;;  
   (cons #x401d89 #xff) ;;  
   (cons #x401d8a #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x401d8b #x45) ;;  
   (cons #x401d8c #xe4) ;;  
   (cons #x401d8d #x00) ;;  
   (cons #x401d8e #x00) ;;  
   (cons #x401d8f #x00) ;;  
   (cons #x401d90 #x00) ;;  
   (cons #x401d91 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401d92 #x45) ;;  
   (cons #x401d93 #xe4) ;;  
   (cons #x401d94 #x48) ;; cltq 
   (cons #x401d95 #x98) ;;  
   (cons #x401d96 #xc7) ;; movl $0x1,-0x38(%rbp,%rax,4) 
   (cons #x401d97 #x44) ;;  
   (cons #x401d98 #x85) ;;  
   (cons #x401d99 #xc8) ;;  
   (cons #x401d9a #x01) ;;  
   (cons #x401d9b #x00) ;;  
   (cons #x401d9c #x00) ;;  
   (cons #x401d9d #x00) ;;  
   (cons #x401d9e #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401d9f #x45) ;;  
   (cons #x401da0 #xe4) ;;  
   (cons #x401da1 #x01) ;;  
   (cons #x401da2 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401da3 #x45) ;;  
   (cons #x401da4 #xe4) ;;  
   (cons #x401da5 #x48) ;; cltq 
   (cons #x401da6 #x98) ;;  
   (cons #x401da7 #xc7) ;; movl $0x2,-0x38(%rbp,%rax,4) 
   (cons #x401da8 #x44) ;;  
   (cons #x401da9 #x85) ;;  
   (cons #x401daa #xc8) ;;  
   (cons #x401dab #x02) ;;  
   (cons #x401dac #x00) ;;  
   (cons #x401dad #x00) ;;  
   (cons #x401dae #x00) ;;  
   (cons #x401daf #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401db0 #x45) ;;  
   (cons #x401db1 #xe4) ;;  
   (cons #x401db2 #x01) ;;  
   (cons #x401db3 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401db4 #x45) ;;  
   (cons #x401db5 #xe4) ;;  
   (cons #x401db6 #x48) ;; cltq 
   (cons #x401db7 #x98) ;;  
   (cons #x401db8 #xc7) ;; movl $0xfffffffd,-0x38(%rbp,%rax,4) 
   (cons #x401db9 #x44) ;;  
   (cons #x401dba #x85) ;;  
   (cons #x401dbb #xc8) ;;  
   (cons #x401dbc #xfd) ;;  
   (cons #x401dbd #xff) ;;  
   (cons #x401dbe #xff) ;;  
   (cons #x401dbf #xff) ;;  
   (cons #x401dc0 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401dc1 #x45) ;;  
   (cons #x401dc2 #xe4) ;;  
   (cons #x401dc3 #x01) ;;  
   (cons #x401dc4 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401dc5 #x55) ;;  
   (cons #x401dc6 #xe4) ;;  
   (cons #x401dc7 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x401dc8 #x8d) ;;  
   (cons #x401dc9 #x4d) ;;  
   (cons #x401dca #xc8) ;;  
   (cons #x401dcb #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401dcc #x8b) ;;  
   (cons #x401dcd #x45) ;;  
   (cons #x401dce #xc0) ;;  
   (cons #x401dcf #x48) ;; mov %rcx,%rsi 
   (cons #x401dd0 #x89) ;;  
   (cons #x401dd1 #xce) ;;  
   (cons #x401dd2 #x48) ;; mov %rax,%rdi 
   (cons #x401dd3 #x89) ;;  
   (cons #x401dd4 #xc7) ;;  
   (cons #x401dd5 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x401dd6 #x19) ;;  
   (cons #x401dd7 #xe7) ;;  
   (cons #x401dd8 #xff) ;;  
   (cons #x401dd9 #xff) ;;  
   (cons #x401dda #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x401ddb #x7d) ;;  
   (cons #x401ddc #xe4) ;;  
   (cons #x401ddd #x00) ;;  
   (cons #x401dde #x74) ;; je 401e01 <parse+0x3c6> 
   (cons #x401ddf #x21) ;;  
   (cons #x401de0 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x401de1 #x7d) ;;  
   (cons #x401de2 #xe4) ;;  
   (cons #x401de3 #x01) ;;  
   (cons #x401de4 #x75) ;; jne 401e0b <parse+0x3d0> 
   (cons #x401de5 #x25) ;;  
   (cons #x401de6 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401de7 #x8b) ;;  
   (cons #x401de8 #x45) ;;  
   (cons #x401de9 #xc0) ;;  
   (cons #x401dea #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401deb #x8b) ;;  
   (cons #x401dec #x40) ;;  
   (cons #x401ded #x40) ;;  
   (cons #x401dee #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401def #x55) ;;  
   (cons #x401df0 #xc8) ;;  
   (cons #x401df1 #x48) ;; movslq %edx,%rdx 
   (cons #x401df2 #x63) ;;  
   (cons #x401df3 #xd2) ;;  
   (cons #x401df4 #x48) ;; shl $0x2,%rdx 
   (cons #x401df5 #xc1) ;;  
   (cons #x401df6 #xe2) ;;  
   (cons #x401df7 #x02) ;;  
   (cons #x401df8 #x48) ;; add %rdx,%rax 
   (cons #x401df9 #x01) ;;  
   (cons #x401dfa #xd0) ;;  
   (cons #x401dfb #x8b) ;; mov (%rax),%eax 
   (cons #x401dfc #x00) ;;  
   (cons #x401dfd #x85) ;; test %eax,%eax 
   (cons #x401dfe #xc0) ;;  
   (cons #x401dff #x74) ;; je 401e0b <parse+0x3d0> 
   (cons #x401e00 #x0a) ;;  
   (cons #x401e01 #xb8) ;; mov $0x0,%eax 
   (cons #x401e02 #x00) ;;  
   (cons #x401e03 #x00) ;;  
   (cons #x401e04 #x00) ;;  
   (cons #x401e05 #x00) ;;  
   (cons #x401e06 #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x401e07 #x62) ;;  
   (cons #x401e08 #x0a) ;;  
   (cons #x401e09 #x00) ;;  
   (cons #x401e0a #x00) ;;  
   (cons #x401e0b #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x401e0c #x7d) ;;  
   (cons #x401e0d #xe4) ;;  
   (cons #x401e0e #x01) ;;  
   (cons #x401e0f #x0f) ;; jne 401ee4 <parse+0x4a9> 
   (cons #x401e10 #x85) ;;  
   (cons #x401e11 #xcf) ;;  
   (cons #x401e12 #x00) ;;  
   (cons #x401e13 #x00) ;;  
   (cons #x401e14 #x00) ;;  
   (cons #x401e15 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401e16 #x8b) ;;  
   (cons #x401e17 #x45) ;;  
   (cons #x401e18 #xc0) ;;  
   (cons #x401e19 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401e1a #x8b) ;;  
   (cons #x401e1b #x40) ;;  
   (cons #x401e1c #x40) ;;  
   (cons #x401e1d #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401e1e #x55) ;;  
   (cons #x401e1f #xc8) ;;  
   (cons #x401e20 #xf7) ;; neg %edx 
   (cons #x401e21 #xda) ;;  
   (cons #x401e22 #x48) ;; movslq %edx,%rdx 
   (cons #x401e23 #x63) ;;  
   (cons #x401e24 #xd2) ;;  
   (cons #x401e25 #x48) ;; shl $0x2,%rdx 
   (cons #x401e26 #xc1) ;;  
   (cons #x401e27 #xe2) ;;  
   (cons #x401e28 #x02) ;;  
   (cons #x401e29 #x48) ;; add %rdx,%rax 
   (cons #x401e2a #x01) ;;  
   (cons #x401e2b #xd0) ;;  
   (cons #x401e2c #x8b) ;; mov (%rax),%eax 
   (cons #x401e2d #x00) ;;  
   (cons #x401e2e #x85) ;; test %eax,%eax 
   (cons #x401e2f #xc0) ;;  
   (cons #x401e30 #x0f) ;; jne 401ee4 <parse+0x4a9> 
   (cons #x401e31 #x85) ;;  
   (cons #x401e32 #xae) ;;  
   (cons #x401e33 #x00) ;;  
   (cons #x401e34 #x00) ;;  
   (cons #x401e35 #x00) ;;  
   (cons #x401e36 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401e37 #x8b) ;;  
   (cons #x401e38 #x45) ;;  
   (cons #x401e39 #xc0) ;;  
   (cons #x401e3a #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401e3b #x8b) ;;  
   (cons #x401e3c #x40) ;;  
   (cons #x401e3d #x40) ;;  
   (cons #x401e3e #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401e3f #x55) ;;  
   (cons #x401e40 #xc8) ;;  
   (cons #x401e41 #xf7) ;; neg %edx 
   (cons #x401e42 #xda) ;;  
   (cons #x401e43 #x48) ;; movslq %edx,%rdx 
   (cons #x401e44 #x63) ;;  
   (cons #x401e45 #xd2) ;;  
   (cons #x401e46 #x48) ;; shl $0x2,%rdx 
   (cons #x401e47 #xc1) ;;  
   (cons #x401e48 #xe2) ;;  
   (cons #x401e49 #x02) ;;  
   (cons #x401e4a #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x401e4b #x8d) ;;  
   (cons #x401e4c #x0c) ;;  
   (cons #x401e4d #x10) ;;  
   (cons #x401e4e #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x401e4f #x55) ;;  
   (cons #x401e50 #xe8) ;;  
   (cons #x401e51 #x89) ;; mov %edx,%eax 
   (cons #x401e52 #xd0) ;;  
   (cons #x401e53 #xc1) ;; shl $0x2,%eax 
   (cons #x401e54 #xe0) ;;  
   (cons #x401e55 #x02) ;;  
   (cons #x401e56 #x01) ;; add %edx,%eax 
   (cons #x401e57 #xd0) ;;  
   (cons #x401e58 #x83) ;; add $0x1,%eax 
   (cons #x401e59 #xc0) ;;  
   (cons #x401e5a #x01) ;;  
   (cons #x401e5b #x89) ;; mov %eax,(%rcx) 
   (cons #x401e5c #x01) ;;  
   (cons #x401e5d #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401e5e #x8b) ;;  
   (cons #x401e5f #x45) ;;  
   (cons #x401e60 #xc0) ;;  
   (cons #x401e61 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x401e62 #x8b) ;;  
   (cons #x401e63 #x80) ;;  
   (cons #x401e64 #x80) ;;  
   (cons #x401e65 #x00) ;;  
   (cons #x401e66 #x00) ;;  
   (cons #x401e67 #x00) ;;  
   (cons #x401e68 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401e69 #x55) ;;  
   (cons #x401e6a #xc8) ;;  
   (cons #x401e6b #xf7) ;; neg %edx 
   (cons #x401e6c #xda) ;;  
   (cons #x401e6d #x89) ;; mov %edx,(%rax) 
   (cons #x401e6e #x10) ;;  
   (cons #x401e6f #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x401e70 #x8d) ;;  
   (cons #x401e71 #x50) ;;  
   (cons #x401e72 #x04) ;;  
   (cons #x401e73 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401e74 #x8b) ;;  
   (cons #x401e75 #x45) ;;  
   (cons #x401e76 #xc0) ;;  
   (cons #x401e77 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x401e78 #x89) ;;  
   (cons #x401e79 #x90) ;;  
   (cons #x401e7a #x80) ;;  
   (cons #x401e7b #x00) ;;  
   (cons #x401e7c #x00) ;;  
   (cons #x401e7d #x00) ;;  
   (cons #x401e7e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401e7f #x8b) ;;  
   (cons #x401e80 #x45) ;;  
   (cons #x401e81 #xc0) ;;  
   (cons #x401e82 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x401e83 #x8b) ;;  
   (cons #x401e84 #x48) ;;  
   (cons #x401e85 #x30) ;;  
   (cons #x401e86 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x401e87 #x45) ;;  
   (cons #x401e88 #xc8) ;;  
   (cons #x401e89 #x89) ;; mov %eax,%edx 
   (cons #x401e8a #xc2) ;;  
   (cons #x401e8b #xc1) ;; sar $0x1f,%edx 
   (cons #x401e8c #xfa) ;;  
   (cons #x401e8d #x1f) ;;  
   (cons #x401e8e #x31) ;; xor %edx,%eax 
   (cons #x401e8f #xd0) ;;  
   (cons #x401e90 #x29) ;; sub %edx,%eax 
   (cons #x401e91 #xd0) ;;  
   (cons #x401e92 #x48) ;; cltq 
   (cons #x401e93 #x98) ;;  
   (cons #x401e94 #x48) ;; shl $0x2,%rax 
   (cons #x401e95 #xc1) ;;  
   (cons #x401e96 #xe0) ;;  
   (cons #x401e97 #x02) ;;  
   (cons #x401e98 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401e99 #x8d) ;;  
   (cons #x401e9a #x14) ;;  
   (cons #x401e9b #x01) ;;  
   (cons #x401e9c #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x401e9d #x8d) ;;  
   (cons #x401e9e #x4d) ;;  
   (cons #x401e9f #xc8) ;;  
   (cons #x401ea0 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ea1 #x8b) ;;  
   (cons #x401ea2 #x45) ;;  
   (cons #x401ea3 #xc0) ;;  
   (cons #x401ea4 #x48) ;; mov (%rax),%rax 
   (cons #x401ea5 #x8b) ;;  
   (cons #x401ea6 #x00) ;;  
   (cons #x401ea7 #x48) ;; mov %rcx,%rbx 
   (cons #x401ea8 #x89) ;;  
   (cons #x401ea9 #xcb) ;;  
   (cons #x401eaa #x48) ;; sub %rax,%rbx 
   (cons #x401eab #x29) ;;  
   (cons #x401eac #xc3) ;;  
   (cons #x401ead #x48) ;; mov %rbx,%rax 
   (cons #x401eae #x89) ;;  
   (cons #x401eaf #xd8) ;;  
   (cons #x401eb0 #x48) ;; sar $0x2,%rax 
   (cons #x401eb1 #xc1) ;;  
   (cons #x401eb2 #xf8) ;;  
   (cons #x401eb3 #x02) ;;  
   (cons #x401eb4 #x83) ;; add $0x1,%eax 
   (cons #x401eb5 #xc0) ;;  
   (cons #x401eb6 #x01) ;;  
   (cons #x401eb7 #x89) ;; mov %eax,(%rdx) 
   (cons #x401eb8 #x02) ;;  
   (cons #x401eb9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401eba #x8b) ;;  
   (cons #x401ebb #x45) ;;  
   (cons #x401ebc #xc0) ;;  
   (cons #x401ebd #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x401ebe #x8b) ;;  
   (cons #x401ebf #x48) ;;  
   (cons #x401ec0 #x28) ;;  
   (cons #x401ec1 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x401ec2 #x45) ;;  
   (cons #x401ec3 #xc8) ;;  
   (cons #x401ec4 #x89) ;; mov %eax,%edx 
   (cons #x401ec5 #xc2) ;;  
   (cons #x401ec6 #xc1) ;; sar $0x1f,%edx 
   (cons #x401ec7 #xfa) ;;  
   (cons #x401ec8 #x1f) ;;  
   (cons #x401ec9 #x31) ;; xor %edx,%eax 
   (cons #x401eca #xd0) ;;  
   (cons #x401ecb #x29) ;; sub %edx,%eax 
   (cons #x401ecc #xd0) ;;  
   (cons #x401ecd #x48) ;; cltq 
   (cons #x401ece #x98) ;;  
   (cons #x401ecf #x48) ;; shl $0x2,%rax 
   (cons #x401ed0 #xc1) ;;  
   (cons #x401ed1 #xe0) ;;  
   (cons #x401ed2 #x02) ;;  
   (cons #x401ed3 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401ed4 #x8d) ;;  
   (cons #x401ed5 #x14) ;;  
   (cons #x401ed6 #x01) ;;  
   (cons #x401ed7 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x401ed8 #x45) ;;  
   (cons #x401ed9 #xc8) ;;  
   (cons #x401eda #x85) ;; test %eax,%eax 
   (cons #x401edb #xc0) ;;  
   (cons #x401edc #x0f) ;; setg %al 
   (cons #x401edd #x9f) ;;  
   (cons #x401ede #xc0) ;;  
   (cons #x401edf #x0f) ;; movzbl %al,%eax 
   (cons #x401ee0 #xb6) ;;  
   (cons #x401ee1 #xc0) ;;  
   (cons #x401ee2 #x89) ;; mov %eax,(%rdx) 
   (cons #x401ee3 #x02) ;;  
   (cons #x401ee4 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x401ee5 #x45) ;;  
   (cons #x401ee6 #xe4) ;;  
   (cons #x401ee7 #x00) ;;  
   (cons #x401ee8 #x00) ;;  
   (cons #x401ee9 #x00) ;;  
   (cons #x401eea #x00) ;;  
   (cons #x401eeb #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401eec #x45) ;;  
   (cons #x401eed #xe4) ;;  
   (cons #x401eee #x48) ;; cltq 
   (cons #x401eef #x98) ;;  
   (cons #x401ef0 #xc7) ;; movl $0xffffffff,-0x38(%rbp,%rax,4) 
   (cons #x401ef1 #x44) ;;  
   (cons #x401ef2 #x85) ;;  
   (cons #x401ef3 #xc8) ;;  
   (cons #x401ef4 #xff) ;;  
   (cons #x401ef5 #xff) ;;  
   (cons #x401ef6 #xff) ;;  
   (cons #x401ef7 #xff) ;;  
   (cons #x401ef8 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401ef9 #x45) ;;  
   (cons #x401efa #xe4) ;;  
   (cons #x401efb #x01) ;;  
   (cons #x401efc #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401efd #x45) ;;  
   (cons #x401efe #xe4) ;;  
   (cons #x401eff #x48) ;; cltq 
   (cons #x401f00 #x98) ;;  
   (cons #x401f01 #xc7) ;; movl $0xfffffffe,-0x38(%rbp,%rax,4) 
   (cons #x401f02 #x44) ;;  
   (cons #x401f03 #x85) ;;  
   (cons #x401f04 #xc8) ;;  
   (cons #x401f05 #xfe) ;;  
   (cons #x401f06 #xff) ;;  
   (cons #x401f07 #xff) ;;  
   (cons #x401f08 #xff) ;;  
   (cons #x401f09 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401f0a #x45) ;;  
   (cons #x401f0b #xe4) ;;  
   (cons #x401f0c #x01) ;;  
   (cons #x401f0d #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x401f0e #x45) ;;  
   (cons #x401f0f #xe4) ;;  
   (cons #x401f10 #x48) ;; cltq 
   (cons #x401f11 #x98) ;;  
   (cons #x401f12 #xc7) ;; movl $0x3,-0x38(%rbp,%rax,4) 
   (cons #x401f13 #x44) ;;  
   (cons #x401f14 #x85) ;;  
   (cons #x401f15 #xc8) ;;  
   (cons #x401f16 #x03) ;;  
   (cons #x401f17 #x00) ;;  
   (cons #x401f18 #x00) ;;  
   (cons #x401f19 #x00) ;;  
   (cons #x401f1a #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x401f1b #x45) ;;  
   (cons #x401f1c #xe4) ;;  
   (cons #x401f1d #x01) ;;  
   (cons #x401f1e #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x401f1f #x55) ;;  
   (cons #x401f20 #xe4) ;;  
   (cons #x401f21 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x401f22 #x8d) ;;  
   (cons #x401f23 #x4d) ;;  
   (cons #x401f24 #xc8) ;;  
   (cons #x401f25 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401f26 #x8b) ;;  
   (cons #x401f27 #x45) ;;  
   (cons #x401f28 #xc0) ;;  
   (cons #x401f29 #x48) ;; mov %rcx,%rsi 
   (cons #x401f2a #x89) ;;  
   (cons #x401f2b #xce) ;;  
   (cons #x401f2c #x48) ;; mov %rax,%rdi 
   (cons #x401f2d #x89) ;;  
   (cons #x401f2e #xc7) ;;  
   (cons #x401f2f #xe8) ;; callq 4004f3 <addClause> 
   (cons #x401f30 #xbf) ;;  
   (cons #x401f31 #xe5) ;;  
   (cons #x401f32 #xff) ;;  
   (cons #x401f33 #xff) ;;  
   (cons #x401f34 #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x401f35 #x7d) ;;  
   (cons #x401f36 #xe4) ;;  
   (cons #x401f37 #x00) ;;  
   (cons #x401f38 #x74) ;; je 401f5b <parse+0x520> 
   (cons #x401f39 #x21) ;;  
   (cons #x401f3a #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x401f3b #x7d) ;;  
   (cons #x401f3c #xe4) ;;  
   (cons #x401f3d #x01) ;;  
   (cons #x401f3e #x75) ;; jne 401f65 <parse+0x52a> 
   (cons #x401f3f #x25) ;;  
   (cons #x401f40 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401f41 #x8b) ;;  
   (cons #x401f42 #x45) ;;  
   (cons #x401f43 #xc0) ;;  
   (cons #x401f44 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401f45 #x8b) ;;  
   (cons #x401f46 #x40) ;;  
   (cons #x401f47 #x40) ;;  
   (cons #x401f48 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401f49 #x55) ;;  
   (cons #x401f4a #xc8) ;;  
   (cons #x401f4b #x48) ;; movslq %edx,%rdx 
   (cons #x401f4c #x63) ;;  
   (cons #x401f4d #xd2) ;;  
   (cons #x401f4e #x48) ;; shl $0x2,%rdx 
   (cons #x401f4f #xc1) ;;  
   (cons #x401f50 #xe2) ;;  
   (cons #x401f51 #x02) ;;  
   (cons #x401f52 #x48) ;; add %rdx,%rax 
   (cons #x401f53 #x01) ;;  
   (cons #x401f54 #xd0) ;;  
   (cons #x401f55 #x8b) ;; mov (%rax),%eax 
   (cons #x401f56 #x00) ;;  
   (cons #x401f57 #x85) ;; test %eax,%eax 
   (cons #x401f58 #xc0) ;;  
   (cons #x401f59 #x74) ;; je 401f65 <parse+0x52a> 
   (cons #x401f5a #x0a) ;;  
   (cons #x401f5b #xb8) ;; mov $0x0,%eax 
   (cons #x401f5c #x00) ;;  
   (cons #x401f5d #x00) ;;  
   (cons #x401f5e #x00) ;;  
   (cons #x401f5f #x00) ;;  
   (cons #x401f60 #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x401f61 #x08) ;;  
   (cons #x401f62 #x09) ;;  
   (cons #x401f63 #x00) ;;  
   (cons #x401f64 #x00) ;;  
   (cons #x401f65 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x401f66 #x7d) ;;  
   (cons #x401f67 #xe4) ;;  
   (cons #x401f68 #x01) ;;  
   (cons #x401f69 #x0f) ;; jne 40203e <parse+0x603> 
   (cons #x401f6a #x85) ;;  
   (cons #x401f6b #xcf) ;;  
   (cons #x401f6c #x00) ;;  
   (cons #x401f6d #x00) ;;  
   (cons #x401f6e #x00) ;;  
   (cons #x401f6f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401f70 #x8b) ;;  
   (cons #x401f71 #x45) ;;  
   (cons #x401f72 #xc0) ;;  
   (cons #x401f73 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401f74 #x8b) ;;  
   (cons #x401f75 #x40) ;;  
   (cons #x401f76 #x40) ;;  
   (cons #x401f77 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401f78 #x55) ;;  
   (cons #x401f79 #xc8) ;;  
   (cons #x401f7a #xf7) ;; neg %edx 
   (cons #x401f7b #xda) ;;  
   (cons #x401f7c #x48) ;; movslq %edx,%rdx 
   (cons #x401f7d #x63) ;;  
   (cons #x401f7e #xd2) ;;  
   (cons #x401f7f #x48) ;; shl $0x2,%rdx 
   (cons #x401f80 #xc1) ;;  
   (cons #x401f81 #xe2) ;;  
   (cons #x401f82 #x02) ;;  
   (cons #x401f83 #x48) ;; add %rdx,%rax 
   (cons #x401f84 #x01) ;;  
   (cons #x401f85 #xd0) ;;  
   (cons #x401f86 #x8b) ;; mov (%rax),%eax 
   (cons #x401f87 #x00) ;;  
   (cons #x401f88 #x85) ;; test %eax,%eax 
   (cons #x401f89 #xc0) ;;  
   (cons #x401f8a #x0f) ;; jne 40203e <parse+0x603> 
   (cons #x401f8b #x85) ;;  
   (cons #x401f8c #xae) ;;  
   (cons #x401f8d #x00) ;;  
   (cons #x401f8e #x00) ;;  
   (cons #x401f8f #x00) ;;  
   (cons #x401f90 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401f91 #x8b) ;;  
   (cons #x401f92 #x45) ;;  
   (cons #x401f93 #xc0) ;;  
   (cons #x401f94 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x401f95 #x8b) ;;  
   (cons #x401f96 #x40) ;;  
   (cons #x401f97 #x40) ;;  
   (cons #x401f98 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401f99 #x55) ;;  
   (cons #x401f9a #xc8) ;;  
   (cons #x401f9b #xf7) ;; neg %edx 
   (cons #x401f9c #xda) ;;  
   (cons #x401f9d #x48) ;; movslq %edx,%rdx 
   (cons #x401f9e #x63) ;;  
   (cons #x401f9f #xd2) ;;  
   (cons #x401fa0 #x48) ;; shl $0x2,%rdx 
   (cons #x401fa1 #xc1) ;;  
   (cons #x401fa2 #xe2) ;;  
   (cons #x401fa3 #x02) ;;  
   (cons #x401fa4 #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x401fa5 #x8d) ;;  
   (cons #x401fa6 #x0c) ;;  
   (cons #x401fa7 #x10) ;;  
   (cons #x401fa8 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x401fa9 #x55) ;;  
   (cons #x401faa #xe8) ;;  
   (cons #x401fab #x89) ;; mov %edx,%eax 
   (cons #x401fac #xd0) ;;  
   (cons #x401fad #xc1) ;; shl $0x2,%eax 
   (cons #x401fae #xe0) ;;  
   (cons #x401faf #x02) ;;  
   (cons #x401fb0 #x01) ;; add %edx,%eax 
   (cons #x401fb1 #xd0) ;;  
   (cons #x401fb2 #x83) ;; add $0x1,%eax 
   (cons #x401fb3 #xc0) ;;  
   (cons #x401fb4 #x01) ;;  
   (cons #x401fb5 #x89) ;; mov %eax,(%rcx) 
   (cons #x401fb6 #x01) ;;  
   (cons #x401fb7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401fb8 #x8b) ;;  
   (cons #x401fb9 #x45) ;;  
   (cons #x401fba #xc0) ;;  
   (cons #x401fbb #x48) ;; mov 0x80(%rax),%rax 
   (cons #x401fbc #x8b) ;;  
   (cons #x401fbd #x80) ;;  
   (cons #x401fbe #x80) ;;  
   (cons #x401fbf #x00) ;;  
   (cons #x401fc0 #x00) ;;  
   (cons #x401fc1 #x00) ;;  
   (cons #x401fc2 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x401fc3 #x55) ;;  
   (cons #x401fc4 #xc8) ;;  
   (cons #x401fc5 #xf7) ;; neg %edx 
   (cons #x401fc6 #xda) ;;  
   (cons #x401fc7 #x89) ;; mov %edx,(%rax) 
   (cons #x401fc8 #x10) ;;  
   (cons #x401fc9 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x401fca #x8d) ;;  
   (cons #x401fcb #x50) ;;  
   (cons #x401fcc #x04) ;;  
   (cons #x401fcd #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401fce #x8b) ;;  
   (cons #x401fcf #x45) ;;  
   (cons #x401fd0 #xc0) ;;  
   (cons #x401fd1 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x401fd2 #x89) ;;  
   (cons #x401fd3 #x90) ;;  
   (cons #x401fd4 #x80) ;;  
   (cons #x401fd5 #x00) ;;  
   (cons #x401fd6 #x00) ;;  
   (cons #x401fd7 #x00) ;;  
   (cons #x401fd8 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401fd9 #x8b) ;;  
   (cons #x401fda #x45) ;;  
   (cons #x401fdb #xc0) ;;  
   (cons #x401fdc #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x401fdd #x8b) ;;  
   (cons #x401fde #x48) ;;  
   (cons #x401fdf #x30) ;;  
   (cons #x401fe0 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x401fe1 #x45) ;;  
   (cons #x401fe2 #xc8) ;;  
   (cons #x401fe3 #x89) ;; mov %eax,%edx 
   (cons #x401fe4 #xc2) ;;  
   (cons #x401fe5 #xc1) ;; sar $0x1f,%edx 
   (cons #x401fe6 #xfa) ;;  
   (cons #x401fe7 #x1f) ;;  
   (cons #x401fe8 #x31) ;; xor %edx,%eax 
   (cons #x401fe9 #xd0) ;;  
   (cons #x401fea #x29) ;; sub %edx,%eax 
   (cons #x401feb #xd0) ;;  
   (cons #x401fec #x48) ;; cltq 
   (cons #x401fed #x98) ;;  
   (cons #x401fee #x48) ;; shl $0x2,%rax 
   (cons #x401fef #xc1) ;;  
   (cons #x401ff0 #xe0) ;;  
   (cons #x401ff1 #x02) ;;  
   (cons #x401ff2 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x401ff3 #x8d) ;;  
   (cons #x401ff4 #x14) ;;  
   (cons #x401ff5 #x01) ;;  
   (cons #x401ff6 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x401ff7 #x8d) ;;  
   (cons #x401ff8 #x4d) ;;  
   (cons #x401ff9 #xc8) ;;  
   (cons #x401ffa #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x401ffb #x8b) ;;  
   (cons #x401ffc #x45) ;;  
   (cons #x401ffd #xc0) ;;  
   (cons #x401ffe #x48) ;; mov (%rax),%rax 
   (cons #x401fff #x8b) ;;  
   (cons #x402000 #x00) ;;  
   (cons #x402001 #x48) ;; mov %rcx,%rbx 
   (cons #x402002 #x89) ;;  
   (cons #x402003 #xcb) ;;  
   (cons #x402004 #x48) ;; sub %rax,%rbx 
   (cons #x402005 #x29) ;;  
   (cons #x402006 #xc3) ;;  
   (cons #x402007 #x48) ;; mov %rbx,%rax 
   (cons #x402008 #x89) ;;  
   (cons #x402009 #xd8) ;;  
   (cons #x40200a #x48) ;; sar $0x2,%rax 
   (cons #x40200b #xc1) ;;  
   (cons #x40200c #xf8) ;;  
   (cons #x40200d #x02) ;;  
   (cons #x40200e #x83) ;; add $0x1,%eax 
   (cons #x40200f #xc0) ;;  
   (cons #x402010 #x01) ;;  
   (cons #x402011 #x89) ;; mov %eax,(%rdx) 
   (cons #x402012 #x02) ;;  
   (cons #x402013 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402014 #x8b) ;;  
   (cons #x402015 #x45) ;;  
   (cons #x402016 #xc0) ;;  
   (cons #x402017 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x402018 #x8b) ;;  
   (cons #x402019 #x48) ;;  
   (cons #x40201a #x28) ;;  
   (cons #x40201b #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40201c #x45) ;;  
   (cons #x40201d #xc8) ;;  
   (cons #x40201e #x89) ;; mov %eax,%edx 
   (cons #x40201f #xc2) ;;  
   (cons #x402020 #xc1) ;; sar $0x1f,%edx 
   (cons #x402021 #xfa) ;;  
   (cons #x402022 #x1f) ;;  
   (cons #x402023 #x31) ;; xor %edx,%eax 
   (cons #x402024 #xd0) ;;  
   (cons #x402025 #x29) ;; sub %edx,%eax 
   (cons #x402026 #xd0) ;;  
   (cons #x402027 #x48) ;; cltq 
   (cons #x402028 #x98) ;;  
   (cons #x402029 #x48) ;; shl $0x2,%rax 
   (cons #x40202a #xc1) ;;  
   (cons #x40202b #xe0) ;;  
   (cons #x40202c #x02) ;;  
   (cons #x40202d #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40202e #x8d) ;;  
   (cons #x40202f #x14) ;;  
   (cons #x402030 #x01) ;;  
   (cons #x402031 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402032 #x45) ;;  
   (cons #x402033 #xc8) ;;  
   (cons #x402034 #x85) ;; test %eax,%eax 
   (cons #x402035 #xc0) ;;  
   (cons #x402036 #x0f) ;; setg %al 
   (cons #x402037 #x9f) ;;  
   (cons #x402038 #xc0) ;;  
   (cons #x402039 #x0f) ;; movzbl %al,%eax 
   (cons #x40203a #xb6) ;;  
   (cons #x40203b #xc0) ;;  
   (cons #x40203c #x89) ;; mov %eax,(%rdx) 
   (cons #x40203d #x02) ;;  
   (cons #x40203e #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x40203f #x45) ;;  
   (cons #x402040 #xe4) ;;  
   (cons #x402041 #x00) ;;  
   (cons #x402042 #x00) ;;  
   (cons #x402043 #x00) ;;  
   (cons #x402044 #x00) ;;  
   (cons #x402045 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402046 #x45) ;;  
   (cons #x402047 #xe4) ;;  
   (cons #x402048 #x48) ;; cltq 
   (cons #x402049 #x98) ;;  
   (cons #x40204a #xc7) ;; movl $0x2,-0x38(%rbp,%rax,4) 
   (cons #x40204b #x44) ;;  
   (cons #x40204c #x85) ;;  
   (cons #x40204d #xc8) ;;  
   (cons #x40204e #x02) ;;  
   (cons #x40204f #x00) ;;  
   (cons #x402050 #x00) ;;  
   (cons #x402051 #x00) ;;  
   (cons #x402052 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402053 #x45) ;;  
   (cons #x402054 #xe4) ;;  
   (cons #x402055 #x01) ;;  
   (cons #x402056 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402057 #x45) ;;  
   (cons #x402058 #xe4) ;;  
   (cons #x402059 #x48) ;; cltq 
   (cons #x40205a #x98) ;;  
   (cons #x40205b #xc7) ;; movl $0x3,-0x38(%rbp,%rax,4) 
   (cons #x40205c #x44) ;;  
   (cons #x40205d #x85) ;;  
   (cons #x40205e #xc8) ;;  
   (cons #x40205f #x03) ;;  
   (cons #x402060 #x00) ;;  
   (cons #x402061 #x00) ;;  
   (cons #x402062 #x00) ;;  
   (cons #x402063 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402064 #x45) ;;  
   (cons #x402065 #xe4) ;;  
   (cons #x402066 #x01) ;;  
   (cons #x402067 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402068 #x45) ;;  
   (cons #x402069 #xe4) ;;  
   (cons #x40206a #x48) ;; cltq 
   (cons #x40206b #x98) ;;  
   (cons #x40206c #xc7) ;; movl $0xfffffffc,-0x38(%rbp,%rax,4) 
   (cons #x40206d #x44) ;;  
   (cons #x40206e #x85) ;;  
   (cons #x40206f #xc8) ;;  
   (cons #x402070 #xfc) ;;  
   (cons #x402071 #xff) ;;  
   (cons #x402072 #xff) ;;  
   (cons #x402073 #xff) ;;  
   (cons #x402074 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402075 #x45) ;;  
   (cons #x402076 #xe4) ;;  
   (cons #x402077 #x01) ;;  
   (cons #x402078 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x402079 #x55) ;;  
   (cons #x40207a #xe4) ;;  
   (cons #x40207b #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x40207c #x8d) ;;  
   (cons #x40207d #x4d) ;;  
   (cons #x40207e #xc8) ;;  
   (cons #x40207f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402080 #x8b) ;;  
   (cons #x402081 #x45) ;;  
   (cons #x402082 #xc0) ;;  
   (cons #x402083 #x48) ;; mov %rcx,%rsi 
   (cons #x402084 #x89) ;;  
   (cons #x402085 #xce) ;;  
   (cons #x402086 #x48) ;; mov %rax,%rdi 
   (cons #x402087 #x89) ;;  
   (cons #x402088 #xc7) ;;  
   (cons #x402089 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x40208a #x65) ;;  
   (cons #x40208b #xe4) ;;  
   (cons #x40208c #xff) ;;  
   (cons #x40208d #xff) ;;  
   (cons #x40208e #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x40208f #x7d) ;;  
   (cons #x402090 #xe4) ;;  
   (cons #x402091 #x00) ;;  
   (cons #x402092 #x74) ;; je 4020b5 <parse+0x67a> 
   (cons #x402093 #x21) ;;  
   (cons #x402094 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402095 #x7d) ;;  
   (cons #x402096 #xe4) ;;  
   (cons #x402097 #x01) ;;  
   (cons #x402098 #x75) ;; jne 4020bf <parse+0x684> 
   (cons #x402099 #x25) ;;  
   (cons #x40209a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40209b #x8b) ;;  
   (cons #x40209c #x45) ;;  
   (cons #x40209d #xc0) ;;  
   (cons #x40209e #x48) ;; mov 0x40(%rax),%rax 
   (cons #x40209f #x8b) ;;  
   (cons #x4020a0 #x40) ;;  
   (cons #x4020a1 #x40) ;;  
   (cons #x4020a2 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4020a3 #x55) ;;  
   (cons #x4020a4 #xc8) ;;  
   (cons #x4020a5 #x48) ;; movslq %edx,%rdx 
   (cons #x4020a6 #x63) ;;  
   (cons #x4020a7 #xd2) ;;  
   (cons #x4020a8 #x48) ;; shl $0x2,%rdx 
   (cons #x4020a9 #xc1) ;;  
   (cons #x4020aa #xe2) ;;  
   (cons #x4020ab #x02) ;;  
   (cons #x4020ac #x48) ;; add %rdx,%rax 
   (cons #x4020ad #x01) ;;  
   (cons #x4020ae #xd0) ;;  
   (cons #x4020af #x8b) ;; mov (%rax),%eax 
   (cons #x4020b0 #x00) ;;  
   (cons #x4020b1 #x85) ;; test %eax,%eax 
   (cons #x4020b2 #xc0) ;;  
   (cons #x4020b3 #x74) ;; je 4020bf <parse+0x684> 
   (cons #x4020b4 #x0a) ;;  
   (cons #x4020b5 #xb8) ;; mov $0x0,%eax 
   (cons #x4020b6 #x00) ;;  
   (cons #x4020b7 #x00) ;;  
   (cons #x4020b8 #x00) ;;  
   (cons #x4020b9 #x00) ;;  
   (cons #x4020ba #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x4020bb #xae) ;;  
   (cons #x4020bc #x07) ;;  
   (cons #x4020bd #x00) ;;  
   (cons #x4020be #x00) ;;  
   (cons #x4020bf #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x4020c0 #x7d) ;;  
   (cons #x4020c1 #xe4) ;;  
   (cons #x4020c2 #x01) ;;  
   (cons #x4020c3 #x0f) ;; jne 402198 <parse+0x75d> 
   (cons #x4020c4 #x85) ;;  
   (cons #x4020c5 #xcf) ;;  
   (cons #x4020c6 #x00) ;;  
   (cons #x4020c7 #x00) ;;  
   (cons #x4020c8 #x00) ;;  
   (cons #x4020c9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4020ca #x8b) ;;  
   (cons #x4020cb #x45) ;;  
   (cons #x4020cc #xc0) ;;  
   (cons #x4020cd #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4020ce #x8b) ;;  
   (cons #x4020cf #x40) ;;  
   (cons #x4020d0 #x40) ;;  
   (cons #x4020d1 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4020d2 #x55) ;;  
   (cons #x4020d3 #xc8) ;;  
   (cons #x4020d4 #xf7) ;; neg %edx 
   (cons #x4020d5 #xda) ;;  
   (cons #x4020d6 #x48) ;; movslq %edx,%rdx 
   (cons #x4020d7 #x63) ;;  
   (cons #x4020d8 #xd2) ;;  
   (cons #x4020d9 #x48) ;; shl $0x2,%rdx 
   (cons #x4020da #xc1) ;;  
   (cons #x4020db #xe2) ;;  
   (cons #x4020dc #x02) ;;  
   (cons #x4020dd #x48) ;; add %rdx,%rax 
   (cons #x4020de #x01) ;;  
   (cons #x4020df #xd0) ;;  
   (cons #x4020e0 #x8b) ;; mov (%rax),%eax 
   (cons #x4020e1 #x00) ;;  
   (cons #x4020e2 #x85) ;; test %eax,%eax 
   (cons #x4020e3 #xc0) ;;  
   (cons #x4020e4 #x0f) ;; jne 402198 <parse+0x75d> 
   (cons #x4020e5 #x85) ;;  
   (cons #x4020e6 #xae) ;;  
   (cons #x4020e7 #x00) ;;  
   (cons #x4020e8 #x00) ;;  
   (cons #x4020e9 #x00) ;;  
   (cons #x4020ea #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4020eb #x8b) ;;  
   (cons #x4020ec #x45) ;;  
   (cons #x4020ed #xc0) ;;  
   (cons #x4020ee #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4020ef #x8b) ;;  
   (cons #x4020f0 #x40) ;;  
   (cons #x4020f1 #x40) ;;  
   (cons #x4020f2 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4020f3 #x55) ;;  
   (cons #x4020f4 #xc8) ;;  
   (cons #x4020f5 #xf7) ;; neg %edx 
   (cons #x4020f6 #xda) ;;  
   (cons #x4020f7 #x48) ;; movslq %edx,%rdx 
   (cons #x4020f8 #x63) ;;  
   (cons #x4020f9 #xd2) ;;  
   (cons #x4020fa #x48) ;; shl $0x2,%rdx 
   (cons #x4020fb #xc1) ;;  
   (cons #x4020fc #xe2) ;;  
   (cons #x4020fd #x02) ;;  
   (cons #x4020fe #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x4020ff #x8d) ;;  
   (cons #x402100 #x0c) ;;  
   (cons #x402101 #x10) ;;  
   (cons #x402102 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x402103 #x55) ;;  
   (cons #x402104 #xe8) ;;  
   (cons #x402105 #x89) ;; mov %edx,%eax 
   (cons #x402106 #xd0) ;;  
   (cons #x402107 #xc1) ;; shl $0x2,%eax 
   (cons #x402108 #xe0) ;;  
   (cons #x402109 #x02) ;;  
   (cons #x40210a #x01) ;; add %edx,%eax 
   (cons #x40210b #xd0) ;;  
   (cons #x40210c #x83) ;; add $0x1,%eax 
   (cons #x40210d #xc0) ;;  
   (cons #x40210e #x01) ;;  
   (cons #x40210f #x89) ;; mov %eax,(%rcx) 
   (cons #x402110 #x01) ;;  
   (cons #x402111 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402112 #x8b) ;;  
   (cons #x402113 #x45) ;;  
   (cons #x402114 #xc0) ;;  
   (cons #x402115 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x402116 #x8b) ;;  
   (cons #x402117 #x80) ;;  
   (cons #x402118 #x80) ;;  
   (cons #x402119 #x00) ;;  
   (cons #x40211a #x00) ;;  
   (cons #x40211b #x00) ;;  
   (cons #x40211c #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40211d #x55) ;;  
   (cons #x40211e #xc8) ;;  
   (cons #x40211f #xf7) ;; neg %edx 
   (cons #x402120 #xda) ;;  
   (cons #x402121 #x89) ;; mov %edx,(%rax) 
   (cons #x402122 #x10) ;;  
   (cons #x402123 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x402124 #x8d) ;;  
   (cons #x402125 #x50) ;;  
   (cons #x402126 #x04) ;;  
   (cons #x402127 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402128 #x8b) ;;  
   (cons #x402129 #x45) ;;  
   (cons #x40212a #xc0) ;;  
   (cons #x40212b #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x40212c #x89) ;;  
   (cons #x40212d #x90) ;;  
   (cons #x40212e #x80) ;;  
   (cons #x40212f #x00) ;;  
   (cons #x402130 #x00) ;;  
   (cons #x402131 #x00) ;;  
   (cons #x402132 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402133 #x8b) ;;  
   (cons #x402134 #x45) ;;  
   (cons #x402135 #xc0) ;;  
   (cons #x402136 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x402137 #x8b) ;;  
   (cons #x402138 #x48) ;;  
   (cons #x402139 #x30) ;;  
   (cons #x40213a #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40213b #x45) ;;  
   (cons #x40213c #xc8) ;;  
   (cons #x40213d #x89) ;; mov %eax,%edx 
   (cons #x40213e #xc2) ;;  
   (cons #x40213f #xc1) ;; sar $0x1f,%edx 
   (cons #x402140 #xfa) ;;  
   (cons #x402141 #x1f) ;;  
   (cons #x402142 #x31) ;; xor %edx,%eax 
   (cons #x402143 #xd0) ;;  
   (cons #x402144 #x29) ;; sub %edx,%eax 
   (cons #x402145 #xd0) ;;  
   (cons #x402146 #x48) ;; cltq 
   (cons #x402147 #x98) ;;  
   (cons #x402148 #x48) ;; shl $0x2,%rax 
   (cons #x402149 #xc1) ;;  
   (cons #x40214a #xe0) ;;  
   (cons #x40214b #x02) ;;  
   (cons #x40214c #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40214d #x8d) ;;  
   (cons #x40214e #x14) ;;  
   (cons #x40214f #x01) ;;  
   (cons #x402150 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x402151 #x8d) ;;  
   (cons #x402152 #x4d) ;;  
   (cons #x402153 #xc8) ;;  
   (cons #x402154 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402155 #x8b) ;;  
   (cons #x402156 #x45) ;;  
   (cons #x402157 #xc0) ;;  
   (cons #x402158 #x48) ;; mov (%rax),%rax 
   (cons #x402159 #x8b) ;;  
   (cons #x40215a #x00) ;;  
   (cons #x40215b #x48) ;; mov %rcx,%rbx 
   (cons #x40215c #x89) ;;  
   (cons #x40215d #xcb) ;;  
   (cons #x40215e #x48) ;; sub %rax,%rbx 
   (cons #x40215f #x29) ;;  
   (cons #x402160 #xc3) ;;  
   (cons #x402161 #x48) ;; mov %rbx,%rax 
   (cons #x402162 #x89) ;;  
   (cons #x402163 #xd8) ;;  
   (cons #x402164 #x48) ;; sar $0x2,%rax 
   (cons #x402165 #xc1) ;;  
   (cons #x402166 #xf8) ;;  
   (cons #x402167 #x02) ;;  
   (cons #x402168 #x83) ;; add $0x1,%eax 
   (cons #x402169 #xc0) ;;  
   (cons #x40216a #x01) ;;  
   (cons #x40216b #x89) ;; mov %eax,(%rdx) 
   (cons #x40216c #x02) ;;  
   (cons #x40216d #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40216e #x8b) ;;  
   (cons #x40216f #x45) ;;  
   (cons #x402170 #xc0) ;;  
   (cons #x402171 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x402172 #x8b) ;;  
   (cons #x402173 #x48) ;;  
   (cons #x402174 #x28) ;;  
   (cons #x402175 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402176 #x45) ;;  
   (cons #x402177 #xc8) ;;  
   (cons #x402178 #x89) ;; mov %eax,%edx 
   (cons #x402179 #xc2) ;;  
   (cons #x40217a #xc1) ;; sar $0x1f,%edx 
   (cons #x40217b #xfa) ;;  
   (cons #x40217c #x1f) ;;  
   (cons #x40217d #x31) ;; xor %edx,%eax 
   (cons #x40217e #xd0) ;;  
   (cons #x40217f #x29) ;; sub %edx,%eax 
   (cons #x402180 #xd0) ;;  
   (cons #x402181 #x48) ;; cltq 
   (cons #x402182 #x98) ;;  
   (cons #x402183 #x48) ;; shl $0x2,%rax 
   (cons #x402184 #xc1) ;;  
   (cons #x402185 #xe0) ;;  
   (cons #x402186 #x02) ;;  
   (cons #x402187 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x402188 #x8d) ;;  
   (cons #x402189 #x14) ;;  
   (cons #x40218a #x01) ;;  
   (cons #x40218b #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40218c #x45) ;;  
   (cons #x40218d #xc8) ;;  
   (cons #x40218e #x85) ;; test %eax,%eax 
   (cons #x40218f #xc0) ;;  
   (cons #x402190 #x0f) ;; setg %al 
   (cons #x402191 #x9f) ;;  
   (cons #x402192 #xc0) ;;  
   (cons #x402193 #x0f) ;; movzbl %al,%eax 
   (cons #x402194 #xb6) ;;  
   (cons #x402195 #xc0) ;;  
   (cons #x402196 #x89) ;; mov %eax,(%rdx) 
   (cons #x402197 #x02) ;;  
   (cons #x402198 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x402199 #x45) ;;  
   (cons #x40219a #xe4) ;;  
   (cons #x40219b #x00) ;;  
   (cons #x40219c #x00) ;;  
   (cons #x40219d #x00) ;;  
   (cons #x40219e #x00) ;;  
   (cons #x40219f #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4021a0 #x45) ;;  
   (cons #x4021a1 #xe4) ;;  
   (cons #x4021a2 #x48) ;; cltq 
   (cons #x4021a3 #x98) ;;  
   (cons #x4021a4 #xc7) ;; movl $0xfffffffe,-0x38(%rbp,%rax,4) 
   (cons #x4021a5 #x44) ;;  
   (cons #x4021a6 #x85) ;;  
   (cons #x4021a7 #xc8) ;;  
   (cons #x4021a8 #xfe) ;;  
   (cons #x4021a9 #xff) ;;  
   (cons #x4021aa #xff) ;;  
   (cons #x4021ab #xff) ;;  
   (cons #x4021ac #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4021ad #x45) ;;  
   (cons #x4021ae #xe4) ;;  
   (cons #x4021af #x01) ;;  
   (cons #x4021b0 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4021b1 #x45) ;;  
   (cons #x4021b2 #xe4) ;;  
   (cons #x4021b3 #x48) ;; cltq 
   (cons #x4021b4 #x98) ;;  
   (cons #x4021b5 #xc7) ;; movl $0xfffffffd,-0x38(%rbp,%rax,4) 
   (cons #x4021b6 #x44) ;;  
   (cons #x4021b7 #x85) ;;  
   (cons #x4021b8 #xc8) ;;  
   (cons #x4021b9 #xfd) ;;  
   (cons #x4021ba #xff) ;;  
   (cons #x4021bb #xff) ;;  
   (cons #x4021bc #xff) ;;  
   (cons #x4021bd #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4021be #x45) ;;  
   (cons #x4021bf #xe4) ;;  
   (cons #x4021c0 #x01) ;;  
   (cons #x4021c1 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4021c2 #x45) ;;  
   (cons #x4021c3 #xe4) ;;  
   (cons #x4021c4 #x48) ;; cltq 
   (cons #x4021c5 #x98) ;;  
   (cons #x4021c6 #xc7) ;; movl $0x4,-0x38(%rbp,%rax,4) 
   (cons #x4021c7 #x44) ;;  
   (cons #x4021c8 #x85) ;;  
   (cons #x4021c9 #xc8) ;;  
   (cons #x4021ca #x04) ;;  
   (cons #x4021cb #x00) ;;  
   (cons #x4021cc #x00) ;;  
   (cons #x4021cd #x00) ;;  
   (cons #x4021ce #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4021cf #x45) ;;  
   (cons #x4021d0 #xe4) ;;  
   (cons #x4021d1 #x01) ;;  
   (cons #x4021d2 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x4021d3 #x55) ;;  
   (cons #x4021d4 #xe4) ;;  
   (cons #x4021d5 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x4021d6 #x8d) ;;  
   (cons #x4021d7 #x4d) ;;  
   (cons #x4021d8 #xc8) ;;  
   (cons #x4021d9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4021da #x8b) ;;  
   (cons #x4021db #x45) ;;  
   (cons #x4021dc #xc0) ;;  
   (cons #x4021dd #x48) ;; mov %rcx,%rsi 
   (cons #x4021de #x89) ;;  
   (cons #x4021df #xce) ;;  
   (cons #x4021e0 #x48) ;; mov %rax,%rdi 
   (cons #x4021e1 #x89) ;;  
   (cons #x4021e2 #xc7) ;;  
   (cons #x4021e3 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x4021e4 #x0b) ;;  
   (cons #x4021e5 #xe3) ;;  
   (cons #x4021e6 #xff) ;;  
   (cons #x4021e7 #xff) ;;  
   (cons #x4021e8 #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x4021e9 #x7d) ;;  
   (cons #x4021ea #xe4) ;;  
   (cons #x4021eb #x00) ;;  
   (cons #x4021ec #x74) ;; je 40220f <parse+0x7d4> 
   (cons #x4021ed #x21) ;;  
   (cons #x4021ee #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x4021ef #x7d) ;;  
   (cons #x4021f0 #xe4) ;;  
   (cons #x4021f1 #x01) ;;  
   (cons #x4021f2 #x75) ;; jne 402219 <parse+0x7de> 
   (cons #x4021f3 #x25) ;;  
   (cons #x4021f4 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4021f5 #x8b) ;;  
   (cons #x4021f6 #x45) ;;  
   (cons #x4021f7 #xc0) ;;  
   (cons #x4021f8 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4021f9 #x8b) ;;  
   (cons #x4021fa #x40) ;;  
   (cons #x4021fb #x40) ;;  
   (cons #x4021fc #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4021fd #x55) ;;  
   (cons #x4021fe #xc8) ;;  
   (cons #x4021ff #x48) ;; movslq %edx,%rdx 
   (cons #x402200 #x63) ;;  
   (cons #x402201 #xd2) ;;  
   (cons #x402202 #x48) ;; shl $0x2,%rdx 
   (cons #x402203 #xc1) ;;  
   (cons #x402204 #xe2) ;;  
   (cons #x402205 #x02) ;;  
   (cons #x402206 #x48) ;; add %rdx,%rax 
   (cons #x402207 #x01) ;;  
   (cons #x402208 #xd0) ;;  
   (cons #x402209 #x8b) ;; mov (%rax),%eax 
   (cons #x40220a #x00) ;;  
   (cons #x40220b #x85) ;; test %eax,%eax 
   (cons #x40220c #xc0) ;;  
   (cons #x40220d #x74) ;; je 402219 <parse+0x7de> 
   (cons #x40220e #x0a) ;;  
   (cons #x40220f #xb8) ;; mov $0x0,%eax 
   (cons #x402210 #x00) ;;  
   (cons #x402211 #x00) ;;  
   (cons #x402212 #x00) ;;  
   (cons #x402213 #x00) ;;  
   (cons #x402214 #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x402215 #x54) ;;  
   (cons #x402216 #x06) ;;  
   (cons #x402217 #x00) ;;  
   (cons #x402218 #x00) ;;  
   (cons #x402219 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x40221a #x7d) ;;  
   (cons #x40221b #xe4) ;;  
   (cons #x40221c #x01) ;;  
   (cons #x40221d #x0f) ;; jne 4022f2 <parse+0x8b7> 
   (cons #x40221e #x85) ;;  
   (cons #x40221f #xcf) ;;  
   (cons #x402220 #x00) ;;  
   (cons #x402221 #x00) ;;  
   (cons #x402222 #x00) ;;  
   (cons #x402223 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402224 #x8b) ;;  
   (cons #x402225 #x45) ;;  
   (cons #x402226 #xc0) ;;  
   (cons #x402227 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402228 #x8b) ;;  
   (cons #x402229 #x40) ;;  
   (cons #x40222a #x40) ;;  
   (cons #x40222b #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40222c #x55) ;;  
   (cons #x40222d #xc8) ;;  
   (cons #x40222e #xf7) ;; neg %edx 
   (cons #x40222f #xda) ;;  
   (cons #x402230 #x48) ;; movslq %edx,%rdx 
   (cons #x402231 #x63) ;;  
   (cons #x402232 #xd2) ;;  
   (cons #x402233 #x48) ;; shl $0x2,%rdx 
   (cons #x402234 #xc1) ;;  
   (cons #x402235 #xe2) ;;  
   (cons #x402236 #x02) ;;  
   (cons #x402237 #x48) ;; add %rdx,%rax 
   (cons #x402238 #x01) ;;  
   (cons #x402239 #xd0) ;;  
   (cons #x40223a #x8b) ;; mov (%rax),%eax 
   (cons #x40223b #x00) ;;  
   (cons #x40223c #x85) ;; test %eax,%eax 
   (cons #x40223d #xc0) ;;  
   (cons #x40223e #x0f) ;; jne 4022f2 <parse+0x8b7> 
   (cons #x40223f #x85) ;;  
   (cons #x402240 #xae) ;;  
   (cons #x402241 #x00) ;;  
   (cons #x402242 #x00) ;;  
   (cons #x402243 #x00) ;;  
   (cons #x402244 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402245 #x8b) ;;  
   (cons #x402246 #x45) ;;  
   (cons #x402247 #xc0) ;;  
   (cons #x402248 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402249 #x8b) ;;  
   (cons #x40224a #x40) ;;  
   (cons #x40224b #x40) ;;  
   (cons #x40224c #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40224d #x55) ;;  
   (cons #x40224e #xc8) ;;  
   (cons #x40224f #xf7) ;; neg %edx 
   (cons #x402250 #xda) ;;  
   (cons #x402251 #x48) ;; movslq %edx,%rdx 
   (cons #x402252 #x63) ;;  
   (cons #x402253 #xd2) ;;  
   (cons #x402254 #x48) ;; shl $0x2,%rdx 
   (cons #x402255 #xc1) ;;  
   (cons #x402256 #xe2) ;;  
   (cons #x402257 #x02) ;;  
   (cons #x402258 #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x402259 #x8d) ;;  
   (cons #x40225a #x0c) ;;  
   (cons #x40225b #x10) ;;  
   (cons #x40225c #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x40225d #x55) ;;  
   (cons #x40225e #xe8) ;;  
   (cons #x40225f #x89) ;; mov %edx,%eax 
   (cons #x402260 #xd0) ;;  
   (cons #x402261 #xc1) ;; shl $0x2,%eax 
   (cons #x402262 #xe0) ;;  
   (cons #x402263 #x02) ;;  
   (cons #x402264 #x01) ;; add %edx,%eax 
   (cons #x402265 #xd0) ;;  
   (cons #x402266 #x83) ;; add $0x1,%eax 
   (cons #x402267 #xc0) ;;  
   (cons #x402268 #x01) ;;  
   (cons #x402269 #x89) ;; mov %eax,(%rcx) 
   (cons #x40226a #x01) ;;  
   (cons #x40226b #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40226c #x8b) ;;  
   (cons #x40226d #x45) ;;  
   (cons #x40226e #xc0) ;;  
   (cons #x40226f #x48) ;; mov 0x80(%rax),%rax 
   (cons #x402270 #x8b) ;;  
   (cons #x402271 #x80) ;;  
   (cons #x402272 #x80) ;;  
   (cons #x402273 #x00) ;;  
   (cons #x402274 #x00) ;;  
   (cons #x402275 #x00) ;;  
   (cons #x402276 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402277 #x55) ;;  
   (cons #x402278 #xc8) ;;  
   (cons #x402279 #xf7) ;; neg %edx 
   (cons #x40227a #xda) ;;  
   (cons #x40227b #x89) ;; mov %edx,(%rax) 
   (cons #x40227c #x10) ;;  
   (cons #x40227d #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x40227e #x8d) ;;  
   (cons #x40227f #x50) ;;  
   (cons #x402280 #x04) ;;  
   (cons #x402281 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402282 #x8b) ;;  
   (cons #x402283 #x45) ;;  
   (cons #x402284 #xc0) ;;  
   (cons #x402285 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x402286 #x89) ;;  
   (cons #x402287 #x90) ;;  
   (cons #x402288 #x80) ;;  
   (cons #x402289 #x00) ;;  
   (cons #x40228a #x00) ;;  
   (cons #x40228b #x00) ;;  
   (cons #x40228c #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40228d #x8b) ;;  
   (cons #x40228e #x45) ;;  
   (cons #x40228f #xc0) ;;  
   (cons #x402290 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x402291 #x8b) ;;  
   (cons #x402292 #x48) ;;  
   (cons #x402293 #x30) ;;  
   (cons #x402294 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402295 #x45) ;;  
   (cons #x402296 #xc8) ;;  
   (cons #x402297 #x89) ;; mov %eax,%edx 
   (cons #x402298 #xc2) ;;  
   (cons #x402299 #xc1) ;; sar $0x1f,%edx 
   (cons #x40229a #xfa) ;;  
   (cons #x40229b #x1f) ;;  
   (cons #x40229c #x31) ;; xor %edx,%eax 
   (cons #x40229d #xd0) ;;  
   (cons #x40229e #x29) ;; sub %edx,%eax 
   (cons #x40229f #xd0) ;;  
   (cons #x4022a0 #x48) ;; cltq 
   (cons #x4022a1 #x98) ;;  
   (cons #x4022a2 #x48) ;; shl $0x2,%rax 
   (cons #x4022a3 #xc1) ;;  
   (cons #x4022a4 #xe0) ;;  
   (cons #x4022a5 #x02) ;;  
   (cons #x4022a6 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x4022a7 #x8d) ;;  
   (cons #x4022a8 #x14) ;;  
   (cons #x4022a9 #x01) ;;  
   (cons #x4022aa #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x4022ab #x8d) ;;  
   (cons #x4022ac #x4d) ;;  
   (cons #x4022ad #xc8) ;;  
   (cons #x4022ae #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4022af #x8b) ;;  
   (cons #x4022b0 #x45) ;;  
   (cons #x4022b1 #xc0) ;;  
   (cons #x4022b2 #x48) ;; mov (%rax),%rax 
   (cons #x4022b3 #x8b) ;;  
   (cons #x4022b4 #x00) ;;  
   (cons #x4022b5 #x48) ;; mov %rcx,%rbx 
   (cons #x4022b6 #x89) ;;  
   (cons #x4022b7 #xcb) ;;  
   (cons #x4022b8 #x48) ;; sub %rax,%rbx 
   (cons #x4022b9 #x29) ;;  
   (cons #x4022ba #xc3) ;;  
   (cons #x4022bb #x48) ;; mov %rbx,%rax 
   (cons #x4022bc #x89) ;;  
   (cons #x4022bd #xd8) ;;  
   (cons #x4022be #x48) ;; sar $0x2,%rax 
   (cons #x4022bf #xc1) ;;  
   (cons #x4022c0 #xf8) ;;  
   (cons #x4022c1 #x02) ;;  
   (cons #x4022c2 #x83) ;; add $0x1,%eax 
   (cons #x4022c3 #xc0) ;;  
   (cons #x4022c4 #x01) ;;  
   (cons #x4022c5 #x89) ;; mov %eax,(%rdx) 
   (cons #x4022c6 #x02) ;;  
   (cons #x4022c7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4022c8 #x8b) ;;  
   (cons #x4022c9 #x45) ;;  
   (cons #x4022ca #xc0) ;;  
   (cons #x4022cb #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x4022cc #x8b) ;;  
   (cons #x4022cd #x48) ;;  
   (cons #x4022ce #x28) ;;  
   (cons #x4022cf #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4022d0 #x45) ;;  
   (cons #x4022d1 #xc8) ;;  
   (cons #x4022d2 #x89) ;; mov %eax,%edx 
   (cons #x4022d3 #xc2) ;;  
   (cons #x4022d4 #xc1) ;; sar $0x1f,%edx 
   (cons #x4022d5 #xfa) ;;  
   (cons #x4022d6 #x1f) ;;  
   (cons #x4022d7 #x31) ;; xor %edx,%eax 
   (cons #x4022d8 #xd0) ;;  
   (cons #x4022d9 #x29) ;; sub %edx,%eax 
   (cons #x4022da #xd0) ;;  
   (cons #x4022db #x48) ;; cltq 
   (cons #x4022dc #x98) ;;  
   (cons #x4022dd #x48) ;; shl $0x2,%rax 
   (cons #x4022de #xc1) ;;  
   (cons #x4022df #xe0) ;;  
   (cons #x4022e0 #x02) ;;  
   (cons #x4022e1 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x4022e2 #x8d) ;;  
   (cons #x4022e3 #x14) ;;  
   (cons #x4022e4 #x01) ;;  
   (cons #x4022e5 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4022e6 #x45) ;;  
   (cons #x4022e7 #xc8) ;;  
   (cons #x4022e8 #x85) ;; test %eax,%eax 
   (cons #x4022e9 #xc0) ;;  
   (cons #x4022ea #x0f) ;; setg %al 
   (cons #x4022eb #x9f) ;;  
   (cons #x4022ec #xc0) ;;  
   (cons #x4022ed #x0f) ;; movzbl %al,%eax 
   (cons #x4022ee #xb6) ;;  
   (cons #x4022ef #xc0) ;;  
   (cons #x4022f0 #x89) ;; mov %eax,(%rdx) 
   (cons #x4022f1 #x02) ;;  
   (cons #x4022f2 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x4022f3 #x45) ;;  
   (cons #x4022f4 #xe4) ;;  
   (cons #x4022f5 #x00) ;;  
   (cons #x4022f6 #x00) ;;  
   (cons #x4022f7 #x00) ;;  
   (cons #x4022f8 #x00) ;;  
   (cons #x4022f9 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4022fa #x45) ;;  
   (cons #x4022fb #xe4) ;;  
   (cons #x4022fc #x48) ;; cltq 
   (cons #x4022fd #x98) ;;  
   (cons #x4022fe #xc7) ;; movl $0xffffffff,-0x38(%rbp,%rax,4) 
   (cons #x4022ff #x44) ;;  
   (cons #x402300 #x85) ;;  
   (cons #x402301 #xc8) ;;  
   (cons #x402302 #xff) ;;  
   (cons #x402303 #xff) ;;  
   (cons #x402304 #xff) ;;  
   (cons #x402305 #xff) ;;  
   (cons #x402306 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402307 #x45) ;;  
   (cons #x402308 #xe4) ;;  
   (cons #x402309 #x01) ;;  
   (cons #x40230a #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x40230b #x45) ;;  
   (cons #x40230c #xe4) ;;  
   (cons #x40230d #x48) ;; cltq 
   (cons #x40230e #x98) ;;  
   (cons #x40230f #xc7) ;; movl $0xfffffffd,-0x38(%rbp,%rax,4) 
   (cons #x402310 #x44) ;;  
   (cons #x402311 #x85) ;;  
   (cons #x402312 #xc8) ;;  
   (cons #x402313 #xfd) ;;  
   (cons #x402314 #xff) ;;  
   (cons #x402315 #xff) ;;  
   (cons #x402316 #xff) ;;  
   (cons #x402317 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402318 #x45) ;;  
   (cons #x402319 #xe4) ;;  
   (cons #x40231a #x01) ;;  
   (cons #x40231b #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x40231c #x45) ;;  
   (cons #x40231d #xe4) ;;  
   (cons #x40231e #x48) ;; cltq 
   (cons #x40231f #x98) ;;  
   (cons #x402320 #xc7) ;; movl $0xfffffffc,-0x38(%rbp,%rax,4) 
   (cons #x402321 #x44) ;;  
   (cons #x402322 #x85) ;;  
   (cons #x402323 #xc8) ;;  
   (cons #x402324 #xfc) ;;  
   (cons #x402325 #xff) ;;  
   (cons #x402326 #xff) ;;  
   (cons #x402327 #xff) ;;  
   (cons #x402328 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402329 #x45) ;;  
   (cons #x40232a #xe4) ;;  
   (cons #x40232b #x01) ;;  
   (cons #x40232c #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x40232d #x55) ;;  
   (cons #x40232e #xe4) ;;  
   (cons #x40232f #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x402330 #x8d) ;;  
   (cons #x402331 #x4d) ;;  
   (cons #x402332 #xc8) ;;  
   (cons #x402333 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402334 #x8b) ;;  
   (cons #x402335 #x45) ;;  
   (cons #x402336 #xc0) ;;  
   (cons #x402337 #x48) ;; mov %rcx,%rsi 
   (cons #x402338 #x89) ;;  
   (cons #x402339 #xce) ;;  
   (cons #x40233a #x48) ;; mov %rax,%rdi 
   (cons #x40233b #x89) ;;  
   (cons #x40233c #xc7) ;;  
   (cons #x40233d #xe8) ;; callq 4004f3 <addClause> 
   (cons #x40233e #xb1) ;;  
   (cons #x40233f #xe1) ;;  
   (cons #x402340 #xff) ;;  
   (cons #x402341 #xff) ;;  
   (cons #x402342 #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x402343 #x7d) ;;  
   (cons #x402344 #xe4) ;;  
   (cons #x402345 #x00) ;;  
   (cons #x402346 #x74) ;; je 402369 <parse+0x92e> 
   (cons #x402347 #x21) ;;  
   (cons #x402348 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402349 #x7d) ;;  
   (cons #x40234a #xe4) ;;  
   (cons #x40234b #x01) ;;  
   (cons #x40234c #x75) ;; jne 402373 <parse+0x938> 
   (cons #x40234d #x25) ;;  
   (cons #x40234e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40234f #x8b) ;;  
   (cons #x402350 #x45) ;;  
   (cons #x402351 #xc0) ;;  
   (cons #x402352 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402353 #x8b) ;;  
   (cons #x402354 #x40) ;;  
   (cons #x402355 #x40) ;;  
   (cons #x402356 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402357 #x55) ;;  
   (cons #x402358 #xc8) ;;  
   (cons #x402359 #x48) ;; movslq %edx,%rdx 
   (cons #x40235a #x63) ;;  
   (cons #x40235b #xd2) ;;  
   (cons #x40235c #x48) ;; shl $0x2,%rdx 
   (cons #x40235d #xc1) ;;  
   (cons #x40235e #xe2) ;;  
   (cons #x40235f #x02) ;;  
   (cons #x402360 #x48) ;; add %rdx,%rax 
   (cons #x402361 #x01) ;;  
   (cons #x402362 #xd0) ;;  
   (cons #x402363 #x8b) ;; mov (%rax),%eax 
   (cons #x402364 #x00) ;;  
   (cons #x402365 #x85) ;; test %eax,%eax 
   (cons #x402366 #xc0) ;;  
   (cons #x402367 #x74) ;; je 402373 <parse+0x938> 
   (cons #x402368 #x0a) ;;  
   (cons #x402369 #xb8) ;; mov $0x0,%eax 
   (cons #x40236a #x00) ;;  
   (cons #x40236b #x00) ;;  
   (cons #x40236c #x00) ;;  
   (cons #x40236d #x00) ;;  
   (cons #x40236e #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x40236f #xfa) ;;  
   (cons #x402370 #x04) ;;  
   (cons #x402371 #x00) ;;  
   (cons #x402372 #x00) ;;  
   (cons #x402373 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402374 #x7d) ;;  
   (cons #x402375 #xe4) ;;  
   (cons #x402376 #x01) ;;  
   (cons #x402377 #x0f) ;; jne 40244c <parse+0xa11> 
   (cons #x402378 #x85) ;;  
   (cons #x402379 #xcf) ;;  
   (cons #x40237a #x00) ;;  
   (cons #x40237b #x00) ;;  
   (cons #x40237c #x00) ;;  
   (cons #x40237d #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40237e #x8b) ;;  
   (cons #x40237f #x45) ;;  
   (cons #x402380 #xc0) ;;  
   (cons #x402381 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402382 #x8b) ;;  
   (cons #x402383 #x40) ;;  
   (cons #x402384 #x40) ;;  
   (cons #x402385 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402386 #x55) ;;  
   (cons #x402387 #xc8) ;;  
   (cons #x402388 #xf7) ;; neg %edx 
   (cons #x402389 #xda) ;;  
   (cons #x40238a #x48) ;; movslq %edx,%rdx 
   (cons #x40238b #x63) ;;  
   (cons #x40238c #xd2) ;;  
   (cons #x40238d #x48) ;; shl $0x2,%rdx 
   (cons #x40238e #xc1) ;;  
   (cons #x40238f #xe2) ;;  
   (cons #x402390 #x02) ;;  
   (cons #x402391 #x48) ;; add %rdx,%rax 
   (cons #x402392 #x01) ;;  
   (cons #x402393 #xd0) ;;  
   (cons #x402394 #x8b) ;; mov (%rax),%eax 
   (cons #x402395 #x00) ;;  
   (cons #x402396 #x85) ;; test %eax,%eax 
   (cons #x402397 #xc0) ;;  
   (cons #x402398 #x0f) ;; jne 40244c <parse+0xa11> 
   (cons #x402399 #x85) ;;  
   (cons #x40239a #xae) ;;  
   (cons #x40239b #x00) ;;  
   (cons #x40239c #x00) ;;  
   (cons #x40239d #x00) ;;  
   (cons #x40239e #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40239f #x8b) ;;  
   (cons #x4023a0 #x45) ;;  
   (cons #x4023a1 #xc0) ;;  
   (cons #x4023a2 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4023a3 #x8b) ;;  
   (cons #x4023a4 #x40) ;;  
   (cons #x4023a5 #x40) ;;  
   (cons #x4023a6 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4023a7 #x55) ;;  
   (cons #x4023a8 #xc8) ;;  
   (cons #x4023a9 #xf7) ;; neg %edx 
   (cons #x4023aa #xda) ;;  
   (cons #x4023ab #x48) ;; movslq %edx,%rdx 
   (cons #x4023ac #x63) ;;  
   (cons #x4023ad #xd2) ;;  
   (cons #x4023ae #x48) ;; shl $0x2,%rdx 
   (cons #x4023af #xc1) ;;  
   (cons #x4023b0 #xe2) ;;  
   (cons #x4023b1 #x02) ;;  
   (cons #x4023b2 #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x4023b3 #x8d) ;;  
   (cons #x4023b4 #x0c) ;;  
   (cons #x4023b5 #x10) ;;  
   (cons #x4023b6 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x4023b7 #x55) ;;  
   (cons #x4023b8 #xe8) ;;  
   (cons #x4023b9 #x89) ;; mov %edx,%eax 
   (cons #x4023ba #xd0) ;;  
   (cons #x4023bb #xc1) ;; shl $0x2,%eax 
   (cons #x4023bc #xe0) ;;  
   (cons #x4023bd #x02) ;;  
   (cons #x4023be #x01) ;; add %edx,%eax 
   (cons #x4023bf #xd0) ;;  
   (cons #x4023c0 #x83) ;; add $0x1,%eax 
   (cons #x4023c1 #xc0) ;;  
   (cons #x4023c2 #x01) ;;  
   (cons #x4023c3 #x89) ;; mov %eax,(%rcx) 
   (cons #x4023c4 #x01) ;;  
   (cons #x4023c5 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4023c6 #x8b) ;;  
   (cons #x4023c7 #x45) ;;  
   (cons #x4023c8 #xc0) ;;  
   (cons #x4023c9 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4023ca #x8b) ;;  
   (cons #x4023cb #x80) ;;  
   (cons #x4023cc #x80) ;;  
   (cons #x4023cd #x00) ;;  
   (cons #x4023ce #x00) ;;  
   (cons #x4023cf #x00) ;;  
   (cons #x4023d0 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4023d1 #x55) ;;  
   (cons #x4023d2 #xc8) ;;  
   (cons #x4023d3 #xf7) ;; neg %edx 
   (cons #x4023d4 #xda) ;;  
   (cons #x4023d5 #x89) ;; mov %edx,(%rax) 
   (cons #x4023d6 #x10) ;;  
   (cons #x4023d7 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4023d8 #x8d) ;;  
   (cons #x4023d9 #x50) ;;  
   (cons #x4023da #x04) ;;  
   (cons #x4023db #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4023dc #x8b) ;;  
   (cons #x4023dd #x45) ;;  
   (cons #x4023de #xc0) ;;  
   (cons #x4023df #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x4023e0 #x89) ;;  
   (cons #x4023e1 #x90) ;;  
   (cons #x4023e2 #x80) ;;  
   (cons #x4023e3 #x00) ;;  
   (cons #x4023e4 #x00) ;;  
   (cons #x4023e5 #x00) ;;  
   (cons #x4023e6 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4023e7 #x8b) ;;  
   (cons #x4023e8 #x45) ;;  
   (cons #x4023e9 #xc0) ;;  
   (cons #x4023ea #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x4023eb #x8b) ;;  
   (cons #x4023ec #x48) ;;  
   (cons #x4023ed #x30) ;;  
   (cons #x4023ee #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4023ef #x45) ;;  
   (cons #x4023f0 #xc8) ;;  
   (cons #x4023f1 #x89) ;; mov %eax,%edx 
   (cons #x4023f2 #xc2) ;;  
   (cons #x4023f3 #xc1) ;; sar $0x1f,%edx 
   (cons #x4023f4 #xfa) ;;  
   (cons #x4023f5 #x1f) ;;  
   (cons #x4023f6 #x31) ;; xor %edx,%eax 
   (cons #x4023f7 #xd0) ;;  
   (cons #x4023f8 #x29) ;; sub %edx,%eax 
   (cons #x4023f9 #xd0) ;;  
   (cons #x4023fa #x48) ;; cltq 
   (cons #x4023fb #x98) ;;  
   (cons #x4023fc #x48) ;; shl $0x2,%rax 
   (cons #x4023fd #xc1) ;;  
   (cons #x4023fe #xe0) ;;  
   (cons #x4023ff #x02) ;;  
   (cons #x402400 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x402401 #x8d) ;;  
   (cons #x402402 #x14) ;;  
   (cons #x402403 #x01) ;;  
   (cons #x402404 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x402405 #x8d) ;;  
   (cons #x402406 #x4d) ;;  
   (cons #x402407 #xc8) ;;  
   (cons #x402408 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402409 #x8b) ;;  
   (cons #x40240a #x45) ;;  
   (cons #x40240b #xc0) ;;  
   (cons #x40240c #x48) ;; mov (%rax),%rax 
   (cons #x40240d #x8b) ;;  
   (cons #x40240e #x00) ;;  
   (cons #x40240f #x48) ;; mov %rcx,%rbx 
   (cons #x402410 #x89) ;;  
   (cons #x402411 #xcb) ;;  
   (cons #x402412 #x48) ;; sub %rax,%rbx 
   (cons #x402413 #x29) ;;  
   (cons #x402414 #xc3) ;;  
   (cons #x402415 #x48) ;; mov %rbx,%rax 
   (cons #x402416 #x89) ;;  
   (cons #x402417 #xd8) ;;  
   (cons #x402418 #x48) ;; sar $0x2,%rax 
   (cons #x402419 #xc1) ;;  
   (cons #x40241a #xf8) ;;  
   (cons #x40241b #x02) ;;  
   (cons #x40241c #x83) ;; add $0x1,%eax 
   (cons #x40241d #xc0) ;;  
   (cons #x40241e #x01) ;;  
   (cons #x40241f #x89) ;; mov %eax,(%rdx) 
   (cons #x402420 #x02) ;;  
   (cons #x402421 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402422 #x8b) ;;  
   (cons #x402423 #x45) ;;  
   (cons #x402424 #xc0) ;;  
   (cons #x402425 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x402426 #x8b) ;;  
   (cons #x402427 #x48) ;;  
   (cons #x402428 #x28) ;;  
   (cons #x402429 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40242a #x45) ;;  
   (cons #x40242b #xc8) ;;  
   (cons #x40242c #x89) ;; mov %eax,%edx 
   (cons #x40242d #xc2) ;;  
   (cons #x40242e #xc1) ;; sar $0x1f,%edx 
   (cons #x40242f #xfa) ;;  
   (cons #x402430 #x1f) ;;  
   (cons #x402431 #x31) ;; xor %edx,%eax 
   (cons #x402432 #xd0) ;;  
   (cons #x402433 #x29) ;; sub %edx,%eax 
   (cons #x402434 #xd0) ;;  
   (cons #x402435 #x48) ;; cltq 
   (cons #x402436 #x98) ;;  
   (cons #x402437 #x48) ;; shl $0x2,%rax 
   (cons #x402438 #xc1) ;;  
   (cons #x402439 #xe0) ;;  
   (cons #x40243a #x02) ;;  
   (cons #x40243b #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40243c #x8d) ;;  
   (cons #x40243d #x14) ;;  
   (cons #x40243e #x01) ;;  
   (cons #x40243f #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402440 #x45) ;;  
   (cons #x402441 #xc8) ;;  
   (cons #x402442 #x85) ;; test %eax,%eax 
   (cons #x402443 #xc0) ;;  
   (cons #x402444 #x0f) ;; setg %al 
   (cons #x402445 #x9f) ;;  
   (cons #x402446 #xc0) ;;  
   (cons #x402447 #x0f) ;; movzbl %al,%eax 
   (cons #x402448 #xb6) ;;  
   (cons #x402449 #xc0) ;;  
   (cons #x40244a #x89) ;; mov %eax,(%rdx) 
   (cons #x40244b #x02) ;;  
   (cons #x40244c #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x40244d #x45) ;;  
   (cons #x40244e #xe4) ;;  
   (cons #x40244f #x00) ;;  
   (cons #x402450 #x00) ;;  
   (cons #x402451 #x00) ;;  
   (cons #x402452 #x00) ;;  
   (cons #x402453 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402454 #x45) ;;  
   (cons #x402455 #xe4) ;;  
   (cons #x402456 #x48) ;; cltq 
   (cons #x402457 #x98) ;;  
   (cons #x402458 #xc7) ;; movl $0x1,-0x38(%rbp,%rax,4) 
   (cons #x402459 #x44) ;;  
   (cons #x40245a #x85) ;;  
   (cons #x40245b #xc8) ;;  
   (cons #x40245c #x01) ;;  
   (cons #x40245d #x00) ;;  
   (cons #x40245e #x00) ;;  
   (cons #x40245f #x00) ;;  
   (cons #x402460 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402461 #x45) ;;  
   (cons #x402462 #xe4) ;;  
   (cons #x402463 #x01) ;;  
   (cons #x402464 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402465 #x45) ;;  
   (cons #x402466 #xe4) ;;  
   (cons #x402467 #x48) ;; cltq 
   (cons #x402468 #x98) ;;  
   (cons #x402469 #xc7) ;; movl $0x3,-0x38(%rbp,%rax,4) 
   (cons #x40246a #x44) ;;  
   (cons #x40246b #x85) ;;  
   (cons #x40246c #xc8) ;;  
   (cons #x40246d #x03) ;;  
   (cons #x40246e #x00) ;;  
   (cons #x40246f #x00) ;;  
   (cons #x402470 #x00) ;;  
   (cons #x402471 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402472 #x45) ;;  
   (cons #x402473 #xe4) ;;  
   (cons #x402474 #x01) ;;  
   (cons #x402475 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402476 #x45) ;;  
   (cons #x402477 #xe4) ;;  
   (cons #x402478 #x48) ;; cltq 
   (cons #x402479 #x98) ;;  
   (cons #x40247a #xc7) ;; movl $0x4,-0x38(%rbp,%rax,4) 
   (cons #x40247b #x44) ;;  
   (cons #x40247c #x85) ;;  
   (cons #x40247d #xc8) ;;  
   (cons #x40247e #x04) ;;  
   (cons #x40247f #x00) ;;  
   (cons #x402480 #x00) ;;  
   (cons #x402481 #x00) ;;  
   (cons #x402482 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402483 #x45) ;;  
   (cons #x402484 #xe4) ;;  
   (cons #x402485 #x01) ;;  
   (cons #x402486 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x402487 #x55) ;;  
   (cons #x402488 #xe4) ;;  
   (cons #x402489 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x40248a #x8d) ;;  
   (cons #x40248b #x4d) ;;  
   (cons #x40248c #xc8) ;;  
   (cons #x40248d #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40248e #x8b) ;;  
   (cons #x40248f #x45) ;;  
   (cons #x402490 #xc0) ;;  
   (cons #x402491 #x48) ;; mov %rcx,%rsi 
   (cons #x402492 #x89) ;;  
   (cons #x402493 #xce) ;;  
   (cons #x402494 #x48) ;; mov %rax,%rdi 
   (cons #x402495 #x89) ;;  
   (cons #x402496 #xc7) ;;  
   (cons #x402497 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x402498 #x57) ;;  
   (cons #x402499 #xe0) ;;  
   (cons #x40249a #xff) ;;  
   (cons #x40249b #xff) ;;  
   (cons #x40249c #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x40249d #x7d) ;;  
   (cons #x40249e #xe4) ;;  
   (cons #x40249f #x00) ;;  
   (cons #x4024a0 #x74) ;; je 4024c3 <parse+0xa88> 
   (cons #x4024a1 #x21) ;;  
   (cons #x4024a2 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x4024a3 #x7d) ;;  
   (cons #x4024a4 #xe4) ;;  
   (cons #x4024a5 #x01) ;;  
   (cons #x4024a6 #x75) ;; jne 4024cd <parse+0xa92> 
   (cons #x4024a7 #x25) ;;  
   (cons #x4024a8 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4024a9 #x8b) ;;  
   (cons #x4024aa #x45) ;;  
   (cons #x4024ab #xc0) ;;  
   (cons #x4024ac #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4024ad #x8b) ;;  
   (cons #x4024ae #x40) ;;  
   (cons #x4024af #x40) ;;  
   (cons #x4024b0 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4024b1 #x55) ;;  
   (cons #x4024b2 #xc8) ;;  
   (cons #x4024b3 #x48) ;; movslq %edx,%rdx 
   (cons #x4024b4 #x63) ;;  
   (cons #x4024b5 #xd2) ;;  
   (cons #x4024b6 #x48) ;; shl $0x2,%rdx 
   (cons #x4024b7 #xc1) ;;  
   (cons #x4024b8 #xe2) ;;  
   (cons #x4024b9 #x02) ;;  
   (cons #x4024ba #x48) ;; add %rdx,%rax 
   (cons #x4024bb #x01) ;;  
   (cons #x4024bc #xd0) ;;  
   (cons #x4024bd #x8b) ;; mov (%rax),%eax 
   (cons #x4024be #x00) ;;  
   (cons #x4024bf #x85) ;; test %eax,%eax 
   (cons #x4024c0 #xc0) ;;  
   (cons #x4024c1 #x74) ;; je 4024cd <parse+0xa92> 
   (cons #x4024c2 #x0a) ;;  
   (cons #x4024c3 #xb8) ;; mov $0x0,%eax 
   (cons #x4024c4 #x00) ;;  
   (cons #x4024c5 #x00) ;;  
   (cons #x4024c6 #x00) ;;  
   (cons #x4024c7 #x00) ;;  
   (cons #x4024c8 #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x4024c9 #xa0) ;;  
   (cons #x4024ca #x03) ;;  
   (cons #x4024cb #x00) ;;  
   (cons #x4024cc #x00) ;;  
   (cons #x4024cd #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x4024ce #x7d) ;;  
   (cons #x4024cf #xe4) ;;  
   (cons #x4024d0 #x01) ;;  
   (cons #x4024d1 #x0f) ;; jne 4025a6 <parse+0xb6b> 
   (cons #x4024d2 #x85) ;;  
   (cons #x4024d3 #xcf) ;;  
   (cons #x4024d4 #x00) ;;  
   (cons #x4024d5 #x00) ;;  
   (cons #x4024d6 #x00) ;;  
   (cons #x4024d7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4024d8 #x8b) ;;  
   (cons #x4024d9 #x45) ;;  
   (cons #x4024da #xc0) ;;  
   (cons #x4024db #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4024dc #x8b) ;;  
   (cons #x4024dd #x40) ;;  
   (cons #x4024de #x40) ;;  
   (cons #x4024df #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4024e0 #x55) ;;  
   (cons #x4024e1 #xc8) ;;  
   (cons #x4024e2 #xf7) ;; neg %edx 
   (cons #x4024e3 #xda) ;;  
   (cons #x4024e4 #x48) ;; movslq %edx,%rdx 
   (cons #x4024e5 #x63) ;;  
   (cons #x4024e6 #xd2) ;;  
   (cons #x4024e7 #x48) ;; shl $0x2,%rdx 
   (cons #x4024e8 #xc1) ;;  
   (cons #x4024e9 #xe2) ;;  
   (cons #x4024ea #x02) ;;  
   (cons #x4024eb #x48) ;; add %rdx,%rax 
   (cons #x4024ec #x01) ;;  
   (cons #x4024ed #xd0) ;;  
   (cons #x4024ee #x8b) ;; mov (%rax),%eax 
   (cons #x4024ef #x00) ;;  
   (cons #x4024f0 #x85) ;; test %eax,%eax 
   (cons #x4024f1 #xc0) ;;  
   (cons #x4024f2 #x0f) ;; jne 4025a6 <parse+0xb6b> 
   (cons #x4024f3 #x85) ;;  
   (cons #x4024f4 #xae) ;;  
   (cons #x4024f5 #x00) ;;  
   (cons #x4024f6 #x00) ;;  
   (cons #x4024f7 #x00) ;;  
   (cons #x4024f8 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4024f9 #x8b) ;;  
   (cons #x4024fa #x45) ;;  
   (cons #x4024fb #xc0) ;;  
   (cons #x4024fc #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4024fd #x8b) ;;  
   (cons #x4024fe #x40) ;;  
   (cons #x4024ff #x40) ;;  
   (cons #x402500 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402501 #x55) ;;  
   (cons #x402502 #xc8) ;;  
   (cons #x402503 #xf7) ;; neg %edx 
   (cons #x402504 #xda) ;;  
   (cons #x402505 #x48) ;; movslq %edx,%rdx 
   (cons #x402506 #x63) ;;  
   (cons #x402507 #xd2) ;;  
   (cons #x402508 #x48) ;; shl $0x2,%rdx 
   (cons #x402509 #xc1) ;;  
   (cons #x40250a #xe2) ;;  
   (cons #x40250b #x02) ;;  
   (cons #x40250c #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x40250d #x8d) ;;  
   (cons #x40250e #x0c) ;;  
   (cons #x40250f #x10) ;;  
   (cons #x402510 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x402511 #x55) ;;  
   (cons #x402512 #xe8) ;;  
   (cons #x402513 #x89) ;; mov %edx,%eax 
   (cons #x402514 #xd0) ;;  
   (cons #x402515 #xc1) ;; shl $0x2,%eax 
   (cons #x402516 #xe0) ;;  
   (cons #x402517 #x02) ;;  
   (cons #x402518 #x01) ;; add %edx,%eax 
   (cons #x402519 #xd0) ;;  
   (cons #x40251a #x83) ;; add $0x1,%eax 
   (cons #x40251b #xc0) ;;  
   (cons #x40251c #x01) ;;  
   (cons #x40251d #x89) ;; mov %eax,(%rcx) 
   (cons #x40251e #x01) ;;  
   (cons #x40251f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402520 #x8b) ;;  
   (cons #x402521 #x45) ;;  
   (cons #x402522 #xc0) ;;  
   (cons #x402523 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x402524 #x8b) ;;  
   (cons #x402525 #x80) ;;  
   (cons #x402526 #x80) ;;  
   (cons #x402527 #x00) ;;  
   (cons #x402528 #x00) ;;  
   (cons #x402529 #x00) ;;  
   (cons #x40252a #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40252b #x55) ;;  
   (cons #x40252c #xc8) ;;  
   (cons #x40252d #xf7) ;; neg %edx 
   (cons #x40252e #xda) ;;  
   (cons #x40252f #x89) ;; mov %edx,(%rax) 
   (cons #x402530 #x10) ;;  
   (cons #x402531 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x402532 #x8d) ;;  
   (cons #x402533 #x50) ;;  
   (cons #x402534 #x04) ;;  
   (cons #x402535 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402536 #x8b) ;;  
   (cons #x402537 #x45) ;;  
   (cons #x402538 #xc0) ;;  
   (cons #x402539 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x40253a #x89) ;;  
   (cons #x40253b #x90) ;;  
   (cons #x40253c #x80) ;;  
   (cons #x40253d #x00) ;;  
   (cons #x40253e #x00) ;;  
   (cons #x40253f #x00) ;;  
   (cons #x402540 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402541 #x8b) ;;  
   (cons #x402542 #x45) ;;  
   (cons #x402543 #xc0) ;;  
   (cons #x402544 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x402545 #x8b) ;;  
   (cons #x402546 #x48) ;;  
   (cons #x402547 #x30) ;;  
   (cons #x402548 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402549 #x45) ;;  
   (cons #x40254a #xc8) ;;  
   (cons #x40254b #x89) ;; mov %eax,%edx 
   (cons #x40254c #xc2) ;;  
   (cons #x40254d #xc1) ;; sar $0x1f,%edx 
   (cons #x40254e #xfa) ;;  
   (cons #x40254f #x1f) ;;  
   (cons #x402550 #x31) ;; xor %edx,%eax 
   (cons #x402551 #xd0) ;;  
   (cons #x402552 #x29) ;; sub %edx,%eax 
   (cons #x402553 #xd0) ;;  
   (cons #x402554 #x48) ;; cltq 
   (cons #x402555 #x98) ;;  
   (cons #x402556 #x48) ;; shl $0x2,%rax 
   (cons #x402557 #xc1) ;;  
   (cons #x402558 #xe0) ;;  
   (cons #x402559 #x02) ;;  
   (cons #x40255a #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40255b #x8d) ;;  
   (cons #x40255c #x14) ;;  
   (cons #x40255d #x01) ;;  
   (cons #x40255e #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x40255f #x8d) ;;  
   (cons #x402560 #x4d) ;;  
   (cons #x402561 #xc8) ;;  
   (cons #x402562 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402563 #x8b) ;;  
   (cons #x402564 #x45) ;;  
   (cons #x402565 #xc0) ;;  
   (cons #x402566 #x48) ;; mov (%rax),%rax 
   (cons #x402567 #x8b) ;;  
   (cons #x402568 #x00) ;;  
   (cons #x402569 #x48) ;; mov %rcx,%rbx 
   (cons #x40256a #x89) ;;  
   (cons #x40256b #xcb) ;;  
   (cons #x40256c #x48) ;; sub %rax,%rbx 
   (cons #x40256d #x29) ;;  
   (cons #x40256e #xc3) ;;  
   (cons #x40256f #x48) ;; mov %rbx,%rax 
   (cons #x402570 #x89) ;;  
   (cons #x402571 #xd8) ;;  
   (cons #x402572 #x48) ;; sar $0x2,%rax 
   (cons #x402573 #xc1) ;;  
   (cons #x402574 #xf8) ;;  
   (cons #x402575 #x02) ;;  
   (cons #x402576 #x83) ;; add $0x1,%eax 
   (cons #x402577 #xc0) ;;  
   (cons #x402578 #x01) ;;  
   (cons #x402579 #x89) ;; mov %eax,(%rdx) 
   (cons #x40257a #x02) ;;  
   (cons #x40257b #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40257c #x8b) ;;  
   (cons #x40257d #x45) ;;  
   (cons #x40257e #xc0) ;;  
   (cons #x40257f #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x402580 #x8b) ;;  
   (cons #x402581 #x48) ;;  
   (cons #x402582 #x28) ;;  
   (cons #x402583 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402584 #x45) ;;  
   (cons #x402585 #xc8) ;;  
   (cons #x402586 #x89) ;; mov %eax,%edx 
   (cons #x402587 #xc2) ;;  
   (cons #x402588 #xc1) ;; sar $0x1f,%edx 
   (cons #x402589 #xfa) ;;  
   (cons #x40258a #x1f) ;;  
   (cons #x40258b #x31) ;; xor %edx,%eax 
   (cons #x40258c #xd0) ;;  
   (cons #x40258d #x29) ;; sub %edx,%eax 
   (cons #x40258e #xd0) ;;  
   (cons #x40258f #x48) ;; cltq 
   (cons #x402590 #x98) ;;  
   (cons #x402591 #x48) ;; shl $0x2,%rax 
   (cons #x402592 #xc1) ;;  
   (cons #x402593 #xe0) ;;  
   (cons #x402594 #x02) ;;  
   (cons #x402595 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x402596 #x8d) ;;  
   (cons #x402597 #x14) ;;  
   (cons #x402598 #x01) ;;  
   (cons #x402599 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40259a #x45) ;;  
   (cons #x40259b #xc8) ;;  
   (cons #x40259c #x85) ;; test %eax,%eax 
   (cons #x40259d #xc0) ;;  
   (cons #x40259e #x0f) ;; setg %al 
   (cons #x40259f #x9f) ;;  
   (cons #x4025a0 #xc0) ;;  
   (cons #x4025a1 #x0f) ;; movzbl %al,%eax 
   (cons #x4025a2 #xb6) ;;  
   (cons #x4025a3 #xc0) ;;  
   (cons #x4025a4 #x89) ;; mov %eax,(%rdx) 
   (cons #x4025a5 #x02) ;;  
   (cons #x4025a6 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x4025a7 #x45) ;;  
   (cons #x4025a8 #xe4) ;;  
   (cons #x4025a9 #x00) ;;  
   (cons #x4025aa #x00) ;;  
   (cons #x4025ab #x00) ;;  
   (cons #x4025ac #x00) ;;  
   (cons #x4025ad #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4025ae #x45) ;;  
   (cons #x4025af #xe4) ;;  
   (cons #x4025b0 #x48) ;; cltq 
   (cons #x4025b1 #x98) ;;  
   (cons #x4025b2 #xc7) ;; movl $0xffffffff,-0x38(%rbp,%rax,4) 
   (cons #x4025b3 #x44) ;;  
   (cons #x4025b4 #x85) ;;  
   (cons #x4025b5 #xc8) ;;  
   (cons #x4025b6 #xff) ;;  
   (cons #x4025b7 #xff) ;;  
   (cons #x4025b8 #xff) ;;  
   (cons #x4025b9 #xff) ;;  
   (cons #x4025ba #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4025bb #x45) ;;  
   (cons #x4025bc #xe4) ;;  
   (cons #x4025bd #x01) ;;  
   (cons #x4025be #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4025bf #x45) ;;  
   (cons #x4025c0 #xe4) ;;  
   (cons #x4025c1 #x48) ;; cltq 
   (cons #x4025c2 #x98) ;;  
   (cons #x4025c3 #xc7) ;; movl $0x2,-0x38(%rbp,%rax,4) 
   (cons #x4025c4 #x44) ;;  
   (cons #x4025c5 #x85) ;;  
   (cons #x4025c6 #xc8) ;;  
   (cons #x4025c7 #x02) ;;  
   (cons #x4025c8 #x00) ;;  
   (cons #x4025c9 #x00) ;;  
   (cons #x4025ca #x00) ;;  
   (cons #x4025cb #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4025cc #x45) ;;  
   (cons #x4025cd #xe4) ;;  
   (cons #x4025ce #x01) ;;  
   (cons #x4025cf #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x4025d0 #x45) ;;  
   (cons #x4025d1 #xe4) ;;  
   (cons #x4025d2 #x48) ;; cltq 
   (cons #x4025d3 #x98) ;;  
   (cons #x4025d4 #xc7) ;; movl $0x4,-0x38(%rbp,%rax,4) 
   (cons #x4025d5 #x44) ;;  
   (cons #x4025d6 #x85) ;;  
   (cons #x4025d7 #xc8) ;;  
   (cons #x4025d8 #x04) ;;  
   (cons #x4025d9 #x00) ;;  
   (cons #x4025da #x00) ;;  
   (cons #x4025db #x00) ;;  
   (cons #x4025dc #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x4025dd #x45) ;;  
   (cons #x4025de #xe4) ;;  
   (cons #x4025df #x01) ;;  
   (cons #x4025e0 #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x4025e1 #x55) ;;  
   (cons #x4025e2 #xe4) ;;  
   (cons #x4025e3 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x4025e4 #x8d) ;;  
   (cons #x4025e5 #x4d) ;;  
   (cons #x4025e6 #xc8) ;;  
   (cons #x4025e7 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4025e8 #x8b) ;;  
   (cons #x4025e9 #x45) ;;  
   (cons #x4025ea #xc0) ;;  
   (cons #x4025eb #x48) ;; mov %rcx,%rsi 
   (cons #x4025ec #x89) ;;  
   (cons #x4025ed #xce) ;;  
   (cons #x4025ee #x48) ;; mov %rax,%rdi 
   (cons #x4025ef #x89) ;;  
   (cons #x4025f0 #xc7) ;;  
   (cons #x4025f1 #xe8) ;; callq 4004f3 <addClause> 
   (cons #x4025f2 #xfd) ;;  
   (cons #x4025f3 #xde) ;;  
   (cons #x4025f4 #xff) ;;  
   (cons #x4025f5 #xff) ;;  
   (cons #x4025f6 #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x4025f7 #x7d) ;;  
   (cons #x4025f8 #xe4) ;;  
   (cons #x4025f9 #x00) ;;  
   (cons #x4025fa #x74) ;; je 40261d <parse+0xbe2> 
   (cons #x4025fb #x21) ;;  
   (cons #x4025fc #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x4025fd #x7d) ;;  
   (cons #x4025fe #xe4) ;;  
   (cons #x4025ff #x01) ;;  
   (cons #x402600 #x75) ;; jne 402627 <parse+0xbec> 
   (cons #x402601 #x25) ;;  
   (cons #x402602 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402603 #x8b) ;;  
   (cons #x402604 #x45) ;;  
   (cons #x402605 #xc0) ;;  
   (cons #x402606 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402607 #x8b) ;;  
   (cons #x402608 #x40) ;;  
   (cons #x402609 #x40) ;;  
   (cons #x40260a #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40260b #x55) ;;  
   (cons #x40260c #xc8) ;;  
   (cons #x40260d #x48) ;; movslq %edx,%rdx 
   (cons #x40260e #x63) ;;  
   (cons #x40260f #xd2) ;;  
   (cons #x402610 #x48) ;; shl $0x2,%rdx 
   (cons #x402611 #xc1) ;;  
   (cons #x402612 #xe2) ;;  
   (cons #x402613 #x02) ;;  
   (cons #x402614 #x48) ;; add %rdx,%rax 
   (cons #x402615 #x01) ;;  
   (cons #x402616 #xd0) ;;  
   (cons #x402617 #x8b) ;; mov (%rax),%eax 
   (cons #x402618 #x00) ;;  
   (cons #x402619 #x85) ;; test %eax,%eax 
   (cons #x40261a #xc0) ;;  
   (cons #x40261b #x74) ;; je 402627 <parse+0xbec> 
   (cons #x40261c #x0a) ;;  
   (cons #x40261d #xb8) ;; mov $0x0,%eax 
   (cons #x40261e #x00) ;;  
   (cons #x40261f #x00) ;;  
   (cons #x402620 #x00) ;;  
   (cons #x402621 #x00) ;;  
   (cons #x402622 #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x402623 #x46) ;;  
   (cons #x402624 #x02) ;;  
   (cons #x402625 #x00) ;;  
   (cons #x402626 #x00) ;;  
   (cons #x402627 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402628 #x7d) ;;  
   (cons #x402629 #xe4) ;;  
   (cons #x40262a #x01) ;;  
   (cons #x40262b #x0f) ;; jne 402700 <parse+0xcc5> 
   (cons #x40262c #x85) ;;  
   (cons #x40262d #xcf) ;;  
   (cons #x40262e #x00) ;;  
   (cons #x40262f #x00) ;;  
   (cons #x402630 #x00) ;;  
   (cons #x402631 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402632 #x8b) ;;  
   (cons #x402633 #x45) ;;  
   (cons #x402634 #xc0) ;;  
   (cons #x402635 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402636 #x8b) ;;  
   (cons #x402637 #x40) ;;  
   (cons #x402638 #x40) ;;  
   (cons #x402639 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40263a #x55) ;;  
   (cons #x40263b #xc8) ;;  
   (cons #x40263c #xf7) ;; neg %edx 
   (cons #x40263d #xda) ;;  
   (cons #x40263e #x48) ;; movslq %edx,%rdx 
   (cons #x40263f #x63) ;;  
   (cons #x402640 #xd2) ;;  
   (cons #x402641 #x48) ;; shl $0x2,%rdx 
   (cons #x402642 #xc1) ;;  
   (cons #x402643 #xe2) ;;  
   (cons #x402644 #x02) ;;  
   (cons #x402645 #x48) ;; add %rdx,%rax 
   (cons #x402646 #x01) ;;  
   (cons #x402647 #xd0) ;;  
   (cons #x402648 #x8b) ;; mov (%rax),%eax 
   (cons #x402649 #x00) ;;  
   (cons #x40264a #x85) ;; test %eax,%eax 
   (cons #x40264b #xc0) ;;  
   (cons #x40264c #x0f) ;; jne 402700 <parse+0xcc5> 
   (cons #x40264d #x85) ;;  
   (cons #x40264e #xae) ;;  
   (cons #x40264f #x00) ;;  
   (cons #x402650 #x00) ;;  
   (cons #x402651 #x00) ;;  
   (cons #x402652 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402653 #x8b) ;;  
   (cons #x402654 #x45) ;;  
   (cons #x402655 #xc0) ;;  
   (cons #x402656 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402657 #x8b) ;;  
   (cons #x402658 #x40) ;;  
   (cons #x402659 #x40) ;;  
   (cons #x40265a #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x40265b #x55) ;;  
   (cons #x40265c #xc8) ;;  
   (cons #x40265d #xf7) ;; neg %edx 
   (cons #x40265e #xda) ;;  
   (cons #x40265f #x48) ;; movslq %edx,%rdx 
   (cons #x402660 #x63) ;;  
   (cons #x402661 #xd2) ;;  
   (cons #x402662 #x48) ;; shl $0x2,%rdx 
   (cons #x402663 #xc1) ;;  
   (cons #x402664 #xe2) ;;  
   (cons #x402665 #x02) ;;  
   (cons #x402666 #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x402667 #x8d) ;;  
   (cons #x402668 #x0c) ;;  
   (cons #x402669 #x10) ;;  
   (cons #x40266a #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x40266b #x55) ;;  
   (cons #x40266c #xe8) ;;  
   (cons #x40266d #x89) ;; mov %edx,%eax 
   (cons #x40266e #xd0) ;;  
   (cons #x40266f #xc1) ;; shl $0x2,%eax 
   (cons #x402670 #xe0) ;;  
   (cons #x402671 #x02) ;;  
   (cons #x402672 #x01) ;; add %edx,%eax 
   (cons #x402673 #xd0) ;;  
   (cons #x402674 #x83) ;; add $0x1,%eax 
   (cons #x402675 #xc0) ;;  
   (cons #x402676 #x01) ;;  
   (cons #x402677 #x89) ;; mov %eax,(%rcx) 
   (cons #x402678 #x01) ;;  
   (cons #x402679 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40267a #x8b) ;;  
   (cons #x40267b #x45) ;;  
   (cons #x40267c #xc0) ;;  
   (cons #x40267d #x48) ;; mov 0x80(%rax),%rax 
   (cons #x40267e #x8b) ;;  
   (cons #x40267f #x80) ;;  
   (cons #x402680 #x80) ;;  
   (cons #x402681 #x00) ;;  
   (cons #x402682 #x00) ;;  
   (cons #x402683 #x00) ;;  
   (cons #x402684 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402685 #x55) ;;  
   (cons #x402686 #xc8) ;;  
   (cons #x402687 #xf7) ;; neg %edx 
   (cons #x402688 #xda) ;;  
   (cons #x402689 #x89) ;; mov %edx,(%rax) 
   (cons #x40268a #x10) ;;  
   (cons #x40268b #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x40268c #x8d) ;;  
   (cons #x40268d #x50) ;;  
   (cons #x40268e #x04) ;;  
   (cons #x40268f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402690 #x8b) ;;  
   (cons #x402691 #x45) ;;  
   (cons #x402692 #xc0) ;;  
   (cons #x402693 #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x402694 #x89) ;;  
   (cons #x402695 #x90) ;;  
   (cons #x402696 #x80) ;;  
   (cons #x402697 #x00) ;;  
   (cons #x402698 #x00) ;;  
   (cons #x402699 #x00) ;;  
   (cons #x40269a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40269b #x8b) ;;  
   (cons #x40269c #x45) ;;  
   (cons #x40269d #xc0) ;;  
   (cons #x40269e #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x40269f #x8b) ;;  
   (cons #x4026a0 #x48) ;;  
   (cons #x4026a1 #x30) ;;  
   (cons #x4026a2 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4026a3 #x45) ;;  
   (cons #x4026a4 #xc8) ;;  
   (cons #x4026a5 #x89) ;; mov %eax,%edx 
   (cons #x4026a6 #xc2) ;;  
   (cons #x4026a7 #xc1) ;; sar $0x1f,%edx 
   (cons #x4026a8 #xfa) ;;  
   (cons #x4026a9 #x1f) ;;  
   (cons #x4026aa #x31) ;; xor %edx,%eax 
   (cons #x4026ab #xd0) ;;  
   (cons #x4026ac #x29) ;; sub %edx,%eax 
   (cons #x4026ad #xd0) ;;  
   (cons #x4026ae #x48) ;; cltq 
   (cons #x4026af #x98) ;;  
   (cons #x4026b0 #x48) ;; shl $0x2,%rax 
   (cons #x4026b1 #xc1) ;;  
   (cons #x4026b2 #xe0) ;;  
   (cons #x4026b3 #x02) ;;  
   (cons #x4026b4 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x4026b5 #x8d) ;;  
   (cons #x4026b6 #x14) ;;  
   (cons #x4026b7 #x01) ;;  
   (cons #x4026b8 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x4026b9 #x8d) ;;  
   (cons #x4026ba #x4d) ;;  
   (cons #x4026bb #xc8) ;;  
   (cons #x4026bc #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4026bd #x8b) ;;  
   (cons #x4026be #x45) ;;  
   (cons #x4026bf #xc0) ;;  
   (cons #x4026c0 #x48) ;; mov (%rax),%rax 
   (cons #x4026c1 #x8b) ;;  
   (cons #x4026c2 #x00) ;;  
   (cons #x4026c3 #x48) ;; mov %rcx,%rbx 
   (cons #x4026c4 #x89) ;;  
   (cons #x4026c5 #xcb) ;;  
   (cons #x4026c6 #x48) ;; sub %rax,%rbx 
   (cons #x4026c7 #x29) ;;  
   (cons #x4026c8 #xc3) ;;  
   (cons #x4026c9 #x48) ;; mov %rbx,%rax 
   (cons #x4026ca #x89) ;;  
   (cons #x4026cb #xd8) ;;  
   (cons #x4026cc #x48) ;; sar $0x2,%rax 
   (cons #x4026cd #xc1) ;;  
   (cons #x4026ce #xf8) ;;  
   (cons #x4026cf #x02) ;;  
   (cons #x4026d0 #x83) ;; add $0x1,%eax 
   (cons #x4026d1 #xc0) ;;  
   (cons #x4026d2 #x01) ;;  
   (cons #x4026d3 #x89) ;; mov %eax,(%rdx) 
   (cons #x4026d4 #x02) ;;  
   (cons #x4026d5 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4026d6 #x8b) ;;  
   (cons #x4026d7 #x45) ;;  
   (cons #x4026d8 #xc0) ;;  
   (cons #x4026d9 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x4026da #x8b) ;;  
   (cons #x4026db #x48) ;;  
   (cons #x4026dc #x28) ;;  
   (cons #x4026dd #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4026de #x45) ;;  
   (cons #x4026df #xc8) ;;  
   (cons #x4026e0 #x89) ;; mov %eax,%edx 
   (cons #x4026e1 #xc2) ;;  
   (cons #x4026e2 #xc1) ;; sar $0x1f,%edx 
   (cons #x4026e3 #xfa) ;;  
   (cons #x4026e4 #x1f) ;;  
   (cons #x4026e5 #x31) ;; xor %edx,%eax 
   (cons #x4026e6 #xd0) ;;  
   (cons #x4026e7 #x29) ;; sub %edx,%eax 
   (cons #x4026e8 #xd0) ;;  
   (cons #x4026e9 #x48) ;; cltq 
   (cons #x4026ea #x98) ;;  
   (cons #x4026eb #x48) ;; shl $0x2,%rax 
   (cons #x4026ec #xc1) ;;  
   (cons #x4026ed #xe0) ;;  
   (cons #x4026ee #x02) ;;  
   (cons #x4026ef #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x4026f0 #x8d) ;;  
   (cons #x4026f1 #x14) ;;  
   (cons #x4026f2 #x01) ;;  
   (cons #x4026f3 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4026f4 #x45) ;;  
   (cons #x4026f5 #xc8) ;;  
   (cons #x4026f6 #x85) ;; test %eax,%eax 
   (cons #x4026f7 #xc0) ;;  
   (cons #x4026f8 #x0f) ;; setg %al 
   (cons #x4026f9 #x9f) ;;  
   (cons #x4026fa #xc0) ;;  
   (cons #x4026fb #x0f) ;; movzbl %al,%eax 
   (cons #x4026fc #xb6) ;;  
   (cons #x4026fd #xc0) ;;  
   (cons #x4026fe #x89) ;; mov %eax,(%rdx) 
   (cons #x4026ff #x02) ;;  
   (cons #x402700 #xc7) ;; movl $0x0,-0x1c(%rbp) 
   (cons #x402701 #x45) ;;  
   (cons #x402702 #xe4) ;;  
   (cons #x402703 #x00) ;;  
   (cons #x402704 #x00) ;;  
   (cons #x402705 #x00) ;;  
   (cons #x402706 #x00) ;;  
   (cons #x402707 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402708 #x45) ;;  
   (cons #x402709 #xe4) ;;  
   (cons #x40270a #x48) ;; cltq 
   (cons #x40270b #x98) ;;  
   (cons #x40270c #xc7) ;; movl $0x1,-0x38(%rbp,%rax,4) 
   (cons #x40270d #x44) ;;  
   (cons #x40270e #x85) ;;  
   (cons #x40270f #xc8) ;;  
   (cons #x402710 #x01) ;;  
   (cons #x402711 #x00) ;;  
   (cons #x402712 #x00) ;;  
   (cons #x402713 #x00) ;;  
   (cons #x402714 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402715 #x45) ;;  
   (cons #x402716 #xe4) ;;  
   (cons #x402717 #x01) ;;  
   (cons #x402718 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x402719 #x45) ;;  
   (cons #x40271a #xe4) ;;  
   (cons #x40271b #x48) ;; cltq 
   (cons #x40271c #x98) ;;  
   (cons #x40271d #xc7) ;; movl $0xfffffffe,-0x38(%rbp,%rax,4) 
   (cons #x40271e #x44) ;;  
   (cons #x40271f #x85) ;;  
   (cons #x402720 #xc8) ;;  
   (cons #x402721 #xfe) ;;  
   (cons #x402722 #xff) ;;  
   (cons #x402723 #xff) ;;  
   (cons #x402724 #xff) ;;  
   (cons #x402725 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402726 #x45) ;;  
   (cons #x402727 #xe4) ;;  
   (cons #x402728 #x01) ;;  
   (cons #x402729 #x8b) ;; mov -0x1c(%rbp),%eax 
   (cons #x40272a #x45) ;;  
   (cons #x40272b #xe4) ;;  
   (cons #x40272c #x48) ;; cltq 
   (cons #x40272d #x98) ;;  
   (cons #x40272e #xc7) ;; movl $0xfffffffc,-0x38(%rbp,%rax,4) 
   (cons #x40272f #x44) ;;  
   (cons #x402730 #x85) ;;  
   (cons #x402731 #xc8) ;;  
   (cons #x402732 #xfc) ;;  
   (cons #x402733 #xff) ;;  
   (cons #x402734 #xff) ;;  
   (cons #x402735 #xff) ;;  
   (cons #x402736 #x83) ;; addl $0x1,-0x1c(%rbp) 
   (cons #x402737 #x45) ;;  
   (cons #x402738 #xe4) ;;  
   (cons #x402739 #x01) ;;  
   (cons #x40273a #x8b) ;; mov -0x1c(%rbp),%edx 
   (cons #x40273b #x55) ;;  
   (cons #x40273c #xe4) ;;  
   (cons #x40273d #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x40273e #x8d) ;;  
   (cons #x40273f #x4d) ;;  
   (cons #x402740 #xc8) ;;  
   (cons #x402741 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402742 #x8b) ;;  
   (cons #x402743 #x45) ;;  
   (cons #x402744 #xc0) ;;  
   (cons #x402745 #x48) ;; mov %rcx,%rsi 
   (cons #x402746 #x89) ;;  
   (cons #x402747 #xce) ;;  
   (cons #x402748 #x48) ;; mov %rax,%rdi 
   (cons #x402749 #x89) ;;  
   (cons #x40274a #xc7) ;;  
   (cons #x40274b #xe8) ;; callq 4004f3 <addClause> 
   (cons #x40274c #xa3) ;;  
   (cons #x40274d #xdd) ;;  
   (cons #x40274e #xff) ;;  
   (cons #x40274f #xff) ;;  
   (cons #x402750 #x83) ;; cmpl $0x0,-0x1c(%rbp) 
   (cons #x402751 #x7d) ;;  
   (cons #x402752 #xe4) ;;  
   (cons #x402753 #x00) ;;  
   (cons #x402754 #x74) ;; je 402777 <parse+0xd3c> 
   (cons #x402755 #x21) ;;  
   (cons #x402756 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402757 #x7d) ;;  
   (cons #x402758 #xe4) ;;  
   (cons #x402759 #x01) ;;  
   (cons #x40275a #x75) ;; jne 402781 <parse+0xd46> 
   (cons #x40275b #x25) ;;  
   (cons #x40275c #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40275d #x8b) ;;  
   (cons #x40275e #x45) ;;  
   (cons #x40275f #xc0) ;;  
   (cons #x402760 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402761 #x8b) ;;  
   (cons #x402762 #x40) ;;  
   (cons #x402763 #x40) ;;  
   (cons #x402764 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402765 #x55) ;;  
   (cons #x402766 #xc8) ;;  
   (cons #x402767 #x48) ;; movslq %edx,%rdx 
   (cons #x402768 #x63) ;;  
   (cons #x402769 #xd2) ;;  
   (cons #x40276a #x48) ;; shl $0x2,%rdx 
   (cons #x40276b #xc1) ;;  
   (cons #x40276c #xe2) ;;  
   (cons #x40276d #x02) ;;  
   (cons #x40276e #x48) ;; add %rdx,%rax 
   (cons #x40276f #x01) ;;  
   (cons #x402770 #xd0) ;;  
   (cons #x402771 #x8b) ;; mov (%rax),%eax 
   (cons #x402772 #x00) ;;  
   (cons #x402773 #x85) ;; test %eax,%eax 
   (cons #x402774 #xc0) ;;  
   (cons #x402775 #x74) ;; je 402781 <parse+0xd46> 
   (cons #x402776 #x0a) ;;  
   (cons #x402777 #xb8) ;; mov $0x0,%eax 
   (cons #x402778 #x00) ;;  
   (cons #x402779 #x00) ;;  
   (cons #x40277a #x00) ;;  
   (cons #x40277b #x00) ;;  
   (cons #x40277c #xe9) ;; jmpq 40286d <parse+0xe32> 
   (cons #x40277d #xec) ;;  
   (cons #x40277e #x00) ;;  
   (cons #x40277f #x00) ;;  
   (cons #x402780 #x00) ;;  
   (cons #x402781 #x83) ;; cmpl $0x1,-0x1c(%rbp) 
   (cons #x402782 #x7d) ;;  
   (cons #x402783 #xe4) ;;  
   (cons #x402784 #x01) ;;  
   (cons #x402785 #x0f) ;; jne 40285a <parse+0xe1f> 
   (cons #x402786 #x85) ;;  
   (cons #x402787 #xcf) ;;  
   (cons #x402788 #x00) ;;  
   (cons #x402789 #x00) ;;  
   (cons #x40278a #x00) ;;  
   (cons #x40278b #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40278c #x8b) ;;  
   (cons #x40278d #x45) ;;  
   (cons #x40278e #xc0) ;;  
   (cons #x40278f #x48) ;; mov 0x40(%rax),%rax 
   (cons #x402790 #x8b) ;;  
   (cons #x402791 #x40) ;;  
   (cons #x402792 #x40) ;;  
   (cons #x402793 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x402794 #x55) ;;  
   (cons #x402795 #xc8) ;;  
   (cons #x402796 #xf7) ;; neg %edx 
   (cons #x402797 #xda) ;;  
   (cons #x402798 #x48) ;; movslq %edx,%rdx 
   (cons #x402799 #x63) ;;  
   (cons #x40279a #xd2) ;;  
   (cons #x40279b #x48) ;; shl $0x2,%rdx 
   (cons #x40279c #xc1) ;;  
   (cons #x40279d #xe2) ;;  
   (cons #x40279e #x02) ;;  
   (cons #x40279f #x48) ;; add %rdx,%rax 
   (cons #x4027a0 #x01) ;;  
   (cons #x4027a1 #xd0) ;;  
   (cons #x4027a2 #x8b) ;; mov (%rax),%eax 
   (cons #x4027a3 #x00) ;;  
   (cons #x4027a4 #x85) ;; test %eax,%eax 
   (cons #x4027a5 #xc0) ;;  
   (cons #x4027a6 #x0f) ;; jne 40285a <parse+0xe1f> 
   (cons #x4027a7 #x85) ;;  
   (cons #x4027a8 #xae) ;;  
   (cons #x4027a9 #x00) ;;  
   (cons #x4027aa #x00) ;;  
   (cons #x4027ab #x00) ;;  
   (cons #x4027ac #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4027ad #x8b) ;;  
   (cons #x4027ae #x45) ;;  
   (cons #x4027af #xc0) ;;  
   (cons #x4027b0 #x48) ;; mov 0x40(%rax),%rax 
   (cons #x4027b1 #x8b) ;;  
   (cons #x4027b2 #x40) ;;  
   (cons #x4027b3 #x40) ;;  
   (cons #x4027b4 #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4027b5 #x55) ;;  
   (cons #x4027b6 #xc8) ;;  
   (cons #x4027b7 #xf7) ;; neg %edx 
   (cons #x4027b8 #xda) ;;  
   (cons #x4027b9 #x48) ;; movslq %edx,%rdx 
   (cons #x4027ba #x63) ;;  
   (cons #x4027bb #xd2) ;;  
   (cons #x4027bc #x48) ;; shl $0x2,%rdx 
   (cons #x4027bd #xc1) ;;  
   (cons #x4027be #xe2) ;;  
   (cons #x4027bf #x02) ;;  
   (cons #x4027c0 #x48) ;; lea (%rax,%rdx,1),%rcx 
   (cons #x4027c1 #x8d) ;;  
   (cons #x4027c2 #x0c) ;;  
   (cons #x4027c3 #x10) ;;  
   (cons #x4027c4 #x8b) ;; mov -0x18(%rbp),%edx 
   (cons #x4027c5 #x55) ;;  
   (cons #x4027c6 #xe8) ;;  
   (cons #x4027c7 #x89) ;; mov %edx,%eax 
   (cons #x4027c8 #xd0) ;;  
   (cons #x4027c9 #xc1) ;; shl $0x2,%eax 
   (cons #x4027ca #xe0) ;;  
   (cons #x4027cb #x02) ;;  
   (cons #x4027cc #x01) ;; add %edx,%eax 
   (cons #x4027cd #xd0) ;;  
   (cons #x4027ce #x83) ;; add $0x1,%eax 
   (cons #x4027cf #xc0) ;;  
   (cons #x4027d0 #x01) ;;  
   (cons #x4027d1 #x89) ;; mov %eax,(%rcx) 
   (cons #x4027d2 #x01) ;;  
   (cons #x4027d3 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4027d4 #x8b) ;;  
   (cons #x4027d5 #x45) ;;  
   (cons #x4027d6 #xc0) ;;  
   (cons #x4027d7 #x48) ;; mov 0x80(%rax),%rax 
   (cons #x4027d8 #x8b) ;;  
   (cons #x4027d9 #x80) ;;  
   (cons #x4027da #x80) ;;  
   (cons #x4027db #x00) ;;  
   (cons #x4027dc #x00) ;;  
   (cons #x4027dd #x00) ;;  
   (cons #x4027de #x8b) ;; mov -0x38(%rbp),%edx 
   (cons #x4027df #x55) ;;  
   (cons #x4027e0 #xc8) ;;  
   (cons #x4027e1 #xf7) ;; neg %edx 
   (cons #x4027e2 #xda) ;;  
   (cons #x4027e3 #x89) ;; mov %edx,(%rax) 
   (cons #x4027e4 #x10) ;;  
   (cons #x4027e5 #x48) ;; lea 0x4(%rax),%rdx 
   (cons #x4027e6 #x8d) ;;  
   (cons #x4027e7 #x50) ;;  
   (cons #x4027e8 #x04) ;;  
   (cons #x4027e9 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4027ea #x8b) ;;  
   (cons #x4027eb #x45) ;;  
   (cons #x4027ec #xc0) ;;  
   (cons #x4027ed #x48) ;; mov %rdx,0x80(%rax) 
   (cons #x4027ee #x89) ;;  
   (cons #x4027ef #x90) ;;  
   (cons #x4027f0 #x80) ;;  
   (cons #x4027f1 #x00) ;;  
   (cons #x4027f2 #x00) ;;  
   (cons #x4027f3 #x00) ;;  
   (cons #x4027f4 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x4027f5 #x8b) ;;  
   (cons #x4027f6 #x45) ;;  
   (cons #x4027f7 #xc0) ;;  
   (cons #x4027f8 #x48) ;; mov 0x30(%rax),%rcx 
   (cons #x4027f9 #x8b) ;;  
   (cons #x4027fa #x48) ;;  
   (cons #x4027fb #x30) ;;  
   (cons #x4027fc #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x4027fd #x45) ;;  
   (cons #x4027fe #xc8) ;;  
   (cons #x4027ff #x89) ;; mov %eax,%edx 
   (cons #x402800 #xc2) ;;  
   (cons #x402801 #xc1) ;; sar $0x1f,%edx 
   (cons #x402802 #xfa) ;;  
   (cons #x402803 #x1f) ;;  
   (cons #x402804 #x31) ;; xor %edx,%eax 
   (cons #x402805 #xd0) ;;  
   (cons #x402806 #x29) ;; sub %edx,%eax 
   (cons #x402807 #xd0) ;;  
   (cons #x402808 #x48) ;; cltq 
   (cons #x402809 #x98) ;;  
   (cons #x40280a #x48) ;; shl $0x2,%rax 
   (cons #x40280b #xc1) ;;  
   (cons #x40280c #xe0) ;;  
   (cons #x40280d #x02) ;;  
   (cons #x40280e #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40280f #x8d) ;;  
   (cons #x402810 #x14) ;;  
   (cons #x402811 #x01) ;;  
   (cons #x402812 #x48) ;; lea -0x38(%rbp),%rcx 
   (cons #x402813 #x8d) ;;  
   (cons #x402814 #x4d) ;;  
   (cons #x402815 #xc8) ;;  
   (cons #x402816 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402817 #x8b) ;;  
   (cons #x402818 #x45) ;;  
   (cons #x402819 #xc0) ;;  
   (cons #x40281a #x48) ;; mov (%rax),%rax 
   (cons #x40281b #x8b) ;;  
   (cons #x40281c #x00) ;;  
   (cons #x40281d #x48) ;; mov %rcx,%rbx 
   (cons #x40281e #x89) ;;  
   (cons #x40281f #xcb) ;;  
   (cons #x402820 #x48) ;; sub %rax,%rbx 
   (cons #x402821 #x29) ;;  
   (cons #x402822 #xc3) ;;  
   (cons #x402823 #x48) ;; mov %rbx,%rax 
   (cons #x402824 #x89) ;;  
   (cons #x402825 #xd8) ;;  
   (cons #x402826 #x48) ;; sar $0x2,%rax 
   (cons #x402827 #xc1) ;;  
   (cons #x402828 #xf8) ;;  
   (cons #x402829 #x02) ;;  
   (cons #x40282a #x83) ;; add $0x1,%eax 
   (cons #x40282b #xc0) ;;  
   (cons #x40282c #x01) ;;  
   (cons #x40282d #x89) ;; mov %eax,(%rdx) 
   (cons #x40282e #x02) ;;  
   (cons #x40282f #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402830 #x8b) ;;  
   (cons #x402831 #x45) ;;  
   (cons #x402832 #xc0) ;;  
   (cons #x402833 #x48) ;; mov 0x28(%rax),%rcx 
   (cons #x402834 #x8b) ;;  
   (cons #x402835 #x48) ;;  
   (cons #x402836 #x28) ;;  
   (cons #x402837 #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x402838 #x45) ;;  
   (cons #x402839 #xc8) ;;  
   (cons #x40283a #x89) ;; mov %eax,%edx 
   (cons #x40283b #xc2) ;;  
   (cons #x40283c #xc1) ;; sar $0x1f,%edx 
   (cons #x40283d #xfa) ;;  
   (cons #x40283e #x1f) ;;  
   (cons #x40283f #x31) ;; xor %edx,%eax 
   (cons #x402840 #xd0) ;;  
   (cons #x402841 #x29) ;; sub %edx,%eax 
   (cons #x402842 #xd0) ;;  
   (cons #x402843 #x48) ;; cltq 
   (cons #x402844 #x98) ;;  
   (cons #x402845 #x48) ;; shl $0x2,%rax 
   (cons #x402846 #xc1) ;;  
   (cons #x402847 #xe0) ;;  
   (cons #x402848 #x02) ;;  
   (cons #x402849 #x48) ;; lea (%rcx,%rax,1),%rdx 
   (cons #x40284a #x8d) ;;  
   (cons #x40284b #x14) ;;  
   (cons #x40284c #x01) ;;  
   (cons #x40284d #x8b) ;; mov -0x38(%rbp),%eax 
   (cons #x40284e #x45) ;;  
   (cons #x40284f #xc8) ;;  
   (cons #x402850 #x85) ;; test %eax,%eax 
   (cons #x402851 #xc0) ;;  
   (cons #x402852 #x0f) ;; setg %al 
   (cons #x402853 #x9f) ;;  
   (cons #x402854 #xc0) ;;  
   (cons #x402855 #x0f) ;; movzbl %al,%eax 
   (cons #x402856 #xb6) ;;  
   (cons #x402857 #xc0) ;;  
   (cons #x402858 #x89) ;; mov %eax,(%rdx) 
   (cons #x402859 #x02) ;;  
   (cons #x40285a #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x40285b #x8b) ;;  
   (cons #x40285c #x45) ;;  
   (cons #x40285d #xc0) ;;  
   (cons #x40285e #x8b) ;; mov 0x10(%rax),%edx 
   (cons #x40285f #x50) ;;  
   (cons #x402860 #x10) ;;  
   (cons #x402861 #x48) ;; mov -0x40(%rbp),%rax 
   (cons #x402862 #x8b) ;;  
   (cons #x402863 #x45) ;;  
   (cons #x402864 #xc0) ;;  
   (cons #x402865 #x89) ;; mov %edx,0x14(%rax) 
   (cons #x402866 #x50) ;;  
   (cons #x402867 #x14) ;;  
   (cons #x402868 #xb8) ;; mov $0x1,%eax 
   (cons #x402869 #x01) ;;  
   (cons #x40286a #x00) ;;  
   (cons #x40286b #x00) ;;  
   (cons #x40286c #x00) ;;  
   (cons #x40286d #x48) ;; add $0x40,%rsp 
   (cons #x40286e #x83) ;;  
   (cons #x40286f #xc4) ;;  
   (cons #x402870 #x40) ;;  
   (cons #x402871 #x5b) ;; pop %rbx 
   (cons #x402872 #x5d) ;; pop %rbp 
   (cons #x402873 #xc3) ;; retq 
   
;; Section: <main>:


   (cons #x402874 #x55) ;; push %rbp 
   (cons #x402875 #x48) ;; mov %rsp,%rbp 
   (cons #x402876 #x89) ;;  
   (cons #x402877 #xe5) ;;  
   (cons #x402878 #x48) ;; sub $0xa0,%rsp 
   (cons #x402879 #x81) ;;  
   (cons #x40287a #xec) ;;  
   (cons #x40287b #xa0) ;;  
   (cons #x40287c #x00) ;;  
   (cons #x40287d #x00) ;;  
   (cons #x40287e #x00) ;;  
   (cons #x40287f #x89) ;; mov %edi,-0x94(%rbp) 
   (cons #x402880 #xbd) ;;  
   (cons #x402881 #x6c) ;;  
   (cons #x402882 #xff) ;;  
   (cons #x402883 #xff) ;;  
   (cons #x402884 #xff) ;;  
   (cons #x402885 #x48) ;; mov %rsi,-0xa0(%rbp) 
   (cons #x402886 #x89) ;;  
   (cons #x402887 #xb5) ;;  
   (cons #x402888 #x60) ;;  
   (cons #x402889 #xff) ;;  
   (cons #x40288a #xff) ;;  
   (cons #x40288b #xff) ;;  
   (cons #x40288c #x48) ;; movq $0x603040,-0x90(%rbp) 
   (cons #x40288d #xc7) ;;  
   (cons #x40288e #x85) ;;  
   (cons #x40288f #x70) ;;  
   (cons #x402890 #xff) ;;  
   (cons #x402891 #xff) ;;  
   (cons #x402892 #xff) ;;  
   (cons #x402893 #x40) ;;  
   (cons #x402894 #x30) ;;  
   (cons #x402895 #x60) ;;  
   (cons #x402896 #x00) ;;  
   (cons #x402897 #x48) ;; mov -0xa0(%rbp),%rax 
   (cons #x402898 #x8b) ;;  
   (cons #x402899 #x85) ;;  
   (cons #x40289a #x60) ;;  
   (cons #x40289b #xff) ;;  
   (cons #x40289c #xff) ;;  
   (cons #x40289d #xff) ;;  
   (cons #x40289e #x48) ;; add $0x8,%rax 
   (cons #x40289f #x83) ;;  
   (cons #x4028a0 #xc0) ;;  
   (cons #x4028a1 #x08) ;;  
   (cons #x4028a2 #x48) ;; mov (%rax),%rdx 
   (cons #x4028a3 #x8b) ;;  
   (cons #x4028a4 #x10) ;;  
   (cons #x4028a5 #x48) ;; lea -0x90(%rbp),%rax 
   (cons #x4028a6 #x8d) ;;  
   (cons #x4028a7 #x85) ;;  
   (cons #x4028a8 #x70) ;;  
   (cons #x4028a9 #xff) ;;  
   (cons #x4028aa #xff) ;;  
   (cons #x4028ab #xff) ;;  
   (cons #x4028ac #x48) ;; mov %rdx,%rsi 
   (cons #x4028ad #x89) ;;  
   (cons #x4028ae #xd6) ;;  
   (cons #x4028af #x48) ;; mov %rax,%rdi 
   (cons #x4028b0 #x89) ;;  
   (cons #x4028b1 #xc7) ;;  
   (cons #x4028b2 #xe8) ;; callq 401a3b <parse> 
   (cons #x4028b3 #x84) ;;  
   (cons #x4028b4 #xf1) ;;  
   (cons #x4028b5 #xff) ;;  
   (cons #x4028b6 #xff) ;;  
   (cons #x4028b7 #x85) ;; test %eax,%eax 
   (cons #x4028b8 #xc0) ;;  
   (cons #x4028b9 #x75) ;; jne 4028c4 <main+0x50> 
   (cons #x4028ba #x09) ;;  
   (cons #x4028bb #xc7) ;; movl $0x0,-0x4(%rbp) 
   (cons #x4028bc #x45) ;;  
   (cons #x4028bd #xfc) ;;  
   (cons #x4028be #x00) ;;  
   (cons #x4028bf #x00) ;;  
   (cons #x4028c0 #x00) ;;  
   (cons #x4028c1 #x00) ;;  
   (cons #x4028c2 #xeb) ;; jmp 4028e7 <main+0x73> 
   (cons #x4028c3 #x23) ;;  
   (cons #x4028c4 #x48) ;; lea -0x90(%rbp),%rax 
   (cons #x4028c5 #x8d) ;;  
   (cons #x4028c6 #x85) ;;  
   (cons #x4028c7 #x70) ;;  
   (cons #x4028c8 #xff) ;;  
   (cons #x4028c9 #xff) ;;  
   (cons #x4028ca #xff) ;;  
   (cons #x4028cb #x48) ;; mov %rax,%rdi 
   (cons #x4028cc #x89) ;;  
   (cons #x4028cd #xc7) ;;  
   (cons #x4028ce #xe8) ;; callq 401727 <solve> 
   (cons #x4028cf #x54) ;;  
   (cons #x4028d0 #xee) ;;  
   (cons #x4028d1 #xff) ;;  
   (cons #x4028d2 #xff) ;;  
   (cons #x4028d3 #x85) ;; test %eax,%eax 
   (cons #x4028d4 #xc0) ;;  
   (cons #x4028d5 #x75) ;; jne 4028e0 <main+0x6c> 
   (cons #x4028d6 #x09) ;;  
   (cons #x4028d7 #xc7) ;; movl $0x0,-0x4(%rbp) 
   (cons #x4028d8 #x45) ;;  
   (cons #x4028d9 #xfc) ;;  
   (cons #x4028da #x00) ;;  
   (cons #x4028db #x00) ;;  
   (cons #x4028dc #x00) ;;  
   (cons #x4028dd #x00) ;;  
   (cons #x4028de #xeb) ;; jmp 4028e7 <main+0x73> 
   (cons #x4028df #x07) ;;  
   (cons #x4028e0 #xc7) ;; movl $0x1,-0x4(%rbp) 
   (cons #x4028e1 #x45) ;;  
   (cons #x4028e2 #xfc) ;;  
   (cons #x4028e3 #x01) ;;  
   (cons #x4028e4 #x00) ;;  
   (cons #x4028e5 #x00) ;;  
   (cons #x4028e6 #x00) ;;  
   (cons #x4028e7 #xc9) ;; leaveq 
   (cons #x4028e8 #xc3) ;; retq 
   (cons #x4028e9 #x90) ;; nop 
   (cons #x4028ea #x90) ;; nop 
   (cons #x4028eb #x90) ;; nop 
   (cons #x4028ec #x90) ;; nop 
   (cons #x4028ed #x90) ;; nop 
   (cons #x4028ee #x90) ;; nop 
   (cons #x4028ef #x90) ;; nop 
   
;; Section: <__libc_csu_init>:


   (cons #x4028f0 #x48) ;; mov %rbp,-0x28(%rsp) 
   (cons #x4028f1 #x89) ;;  
   (cons #x4028f2 #x6c) ;;  
   (cons #x4028f3 #x24) ;;  
   (cons #x4028f4 #xd8) ;;  
   (cons #x4028f5 #x4c) ;; mov %r12,-0x20(%rsp) 
   (cons #x4028f6 #x89) ;;  
   (cons #x4028f7 #x64) ;;  
   (cons #x4028f8 #x24) ;;  
   (cons #x4028f9 #xe0) ;;  
   (cons #x4028fa #x48) ;; lea 0x200523(%rip),%rbp # 602e24 <__init_array_end> 
   (cons #x4028fb #x8d) ;;  
   (cons #x4028fc #x2d) ;;  
   (cons #x4028fd #x23) ;;  
   (cons #x4028fe #x05) ;;  
   (cons #x4028ff #x20) ;;  
   (cons #x402900 #x00) ;;  
   (cons #x402901 #x4c) ;; lea 0x20051c(%rip),%r12 # 602e24 <__init_array_end> 
   (cons #x402902 #x8d) ;;  
   (cons #x402903 #x25) ;;  
   (cons #x402904 #x1c) ;;  
   (cons #x402905 #x05) ;;  
   (cons #x402906 #x20) ;;  
   (cons #x402907 #x00) ;;  
   (cons #x402908 #x4c) ;; mov %r13,-0x18(%rsp) 
   (cons #x402909 #x89) ;;  
   (cons #x40290a #x6c) ;;  
   (cons #x40290b #x24) ;;  
   (cons #x40290c #xe8) ;;  
   (cons #x40290d #x4c) ;; mov %r14,-0x10(%rsp) 
   (cons #x40290e #x89) ;;  
   (cons #x40290f #x74) ;;  
   (cons #x402910 #x24) ;;  
   (cons #x402911 #xf0) ;;  
   (cons #x402912 #x4c) ;; mov %r15,-0x8(%rsp) 
   (cons #x402913 #x89) ;;  
   (cons #x402914 #x7c) ;;  
   (cons #x402915 #x24) ;;  
   (cons #x402916 #xf8) ;;  
   (cons #x402917 #x48) ;; mov %rbx,-0x30(%rsp) 
   (cons #x402918 #x89) ;;  
   (cons #x402919 #x5c) ;;  
   (cons #x40291a #x24) ;;  
   (cons #x40291b #xd0) ;;  
   (cons #x40291c #x48) ;; sub $0x38,%rsp 
   (cons #x40291d #x83) ;;  
   (cons #x40291e #xec) ;;  
   (cons #x40291f #x38) ;;  
   (cons #x402920 #x4c) ;; sub %r12,%rbp 
   (cons #x402921 #x29) ;;  
   (cons #x402922 #xe5) ;;  
   (cons #x402923 #x41) ;; mov %edi,%r13d 
   (cons #x402924 #x89) ;;  
   (cons #x402925 #xfd) ;;  
   (cons #x402926 #x49) ;; mov %rsi,%r14 
   (cons #x402927 #x89) ;;  
   (cons #x402928 #xf6) ;;  
   (cons #x402929 #x48) ;; sar $0x3,%rbp 
   (cons #x40292a #xc1) ;;  
   (cons #x40292b #xfd) ;;  
   (cons #x40292c #x03) ;;  
   (cons #x40292d #x49) ;; mov %rdx,%r15 
   (cons #x40292e #x89) ;;  
   (cons #x40292f #xd7) ;;  
   (cons #x402930 #xe8) ;; callq 400390 <_init> 
   (cons #x402931 #x5b) ;;  
   (cons #x402932 #xda) ;;  
   (cons #x402933 #xff) ;;  
   (cons #x402934 #xff) ;;  
   (cons #x402935 #x48) ;; test %rbp,%rbp 
   (cons #x402936 #x85) ;;  
   (cons #x402937 #xed) ;;  
   (cons #x402938 #x74) ;; je 402956 <__libc_csu_init+0x66> 
   (cons #x402939 #x1c) ;;  
   (cons #x40293a #x31) ;; xor %ebx,%ebx 
   (cons #x40293b #xdb) ;;  
   (cons #x40293c #x0f) ;; nopl 0x0(%rax) 
   (cons #x40293d #x1f) ;;  
   (cons #x40293e #x40) ;;  
   (cons #x40293f #x00) ;;  
   (cons #x402940 #x4c) ;; mov %r15,%rdx 
   (cons #x402941 #x89) ;;  
   (cons #x402942 #xfa) ;;  
   (cons #x402943 #x4c) ;; mov %r14,%rsi 
   (cons #x402944 #x89) ;;  
   (cons #x402945 #xf6) ;;  
   (cons #x402946 #x44) ;; mov %r13d,%edi 
   (cons #x402947 #x89) ;;  
   (cons #x402948 #xef) ;;  
   (cons #x402949 #x41) ;; callq *(%r12,%rbx,8) 
   (cons #x40294a #xff) ;;  
   (cons #x40294b #x14) ;;  
   (cons #x40294c #xdc) ;;  
   (cons #x40294d #x48) ;; add $0x1,%rbx 
   (cons #x40294e #x83) ;;  
   (cons #x40294f #xc3) ;;  
   (cons #x402950 #x01) ;;  
   (cons #x402951 #x48) ;; cmp %rbp,%rbx 
   (cons #x402952 #x39) ;;  
   (cons #x402953 #xeb) ;;  
   (cons #x402954 #x75) ;; jne 402940 <__libc_csu_init+0x50> 
   (cons #x402955 #xea) ;;  
   (cons #x402956 #x48) ;; mov 0x8(%rsp),%rbx 
   (cons #x402957 #x8b) ;;  
   (cons #x402958 #x5c) ;;  
   (cons #x402959 #x24) ;;  
   (cons #x40295a #x08) ;;  
   (cons #x40295b #x48) ;; mov 0x10(%rsp),%rbp 
   (cons #x40295c #x8b) ;;  
   (cons #x40295d #x6c) ;;  
   (cons #x40295e #x24) ;;  
   (cons #x40295f #x10) ;;  
   (cons #x402960 #x4c) ;; mov 0x18(%rsp),%r12 
   (cons #x402961 #x8b) ;;  
   (cons #x402962 #x64) ;;  
   (cons #x402963 #x24) ;;  
   (cons #x402964 #x18) ;;  
   (cons #x402965 #x4c) ;; mov 0x20(%rsp),%r13 
   (cons #x402966 #x8b) ;;  
   (cons #x402967 #x6c) ;;  
   (cons #x402968 #x24) ;;  
   (cons #x402969 #x20) ;;  
   (cons #x40296a #x4c) ;; mov 0x28(%rsp),%r14 
   (cons #x40296b #x8b) ;;  
   (cons #x40296c #x74) ;;  
   (cons #x40296d #x24) ;;  
   (cons #x40296e #x28) ;;  
   (cons #x40296f #x4c) ;; mov 0x30(%rsp),%r15 
   (cons #x402970 #x8b) ;;  
   (cons #x402971 #x7c) ;;  
   (cons #x402972 #x24) ;;  
   (cons #x402973 #x30) ;;  
   (cons #x402974 #x48) ;; add $0x38,%rsp 
   (cons #x402975 #x83) ;;  
   (cons #x402976 #xc4) ;;  
   (cons #x402977 #x38) ;;  
   (cons #x402978 #xc3) ;; retq 
   (cons #x402979 #x0f) ;; nopl 0x0(%rax) 
   (cons #x40297a #x1f) ;;  
   (cons #x40297b #x80) ;;  
   (cons #x40297c #x00) ;;  
   (cons #x40297d #x00) ;;  
   (cons #x40297e #x00) ;;  
   (cons #x40297f #x00) ;;  
   
;; Section: <__libc_csu_fini>:


   (cons #x402980 #xf3) ;; repz retq 
   (cons #x402981 #xc3) ;;  
   (cons #x402982 #x90) ;; nop 
   (cons #x402983 #x90) ;; nop 
   (cons #x402984 #x90) ;; nop 
   (cons #x402985 #x90) ;; nop 
   (cons #x402986 #x90) ;; nop 
   (cons #x402987 #x90) ;; nop 
   (cons #x402988 #x90) ;; nop 
   (cons #x402989 #x90) ;; nop 
   (cons #x40298a #x90) ;; nop 
   (cons #x40298b #x90) ;; nop 
   (cons #x40298c #x90) ;; nop 
   (cons #x40298d #x90) ;; nop 
   (cons #x40298e #x90) ;; nop 
   (cons #x40298f #x90) ;; nop 
   
;; Section: <__do_global_ctors_aux>:


   (cons #x402990 #x55) ;; push %rbp 
   (cons #x402991 #x48) ;; mov %rsp,%rbp 
   (cons #x402992 #x89) ;;  
   (cons #x402993 #xe5) ;;  
   (cons #x402994 #x53) ;; push %rbx 
   (cons #x402995 #x48) ;; sub $0x8,%rsp 
   (cons #x402996 #x83) ;;  
   (cons #x402997 #xec) ;;  
   (cons #x402998 #x08) ;;  
   (cons #x402999 #x48) ;; mov 0x200488(%rip),%rax # 602e28 <__CTOR_LIST__> 
   (cons #x40299a #x8b) ;;  
   (cons #x40299b #x05) ;;  
   (cons #x40299c #x88) ;;  
   (cons #x40299d #x04) ;;  
   (cons #x40299e #x20) ;;  
   (cons #x40299f #x00) ;;  
   (cons #x4029a0 #x48) ;; cmp $0xffffffffffffffff,%rax 
   (cons #x4029a1 #x83) ;;  
   (cons #x4029a2 #xf8) ;;  
   (cons #x4029a3 #xff) ;;  
   (cons #x4029a4 #x74) ;; je 4029bf <__do_global_ctors_aux+0x2f> 
   (cons #x4029a5 #x19) ;;  
   (cons #x4029a6 #xbb) ;; mov $0x602e28,%ebx 
   (cons #x4029a7 #x28) ;;  
   (cons #x4029a8 #x2e) ;;  
   (cons #x4029a9 #x60) ;;  
   (cons #x4029aa #x00) ;;  
   (cons #x4029ab #x0f) ;; nopl 0x0(%rax,%rax,1) 
   (cons #x4029ac #x1f) ;;  
   (cons #x4029ad #x44) ;;  
   (cons #x4029ae #x00) ;;  
   (cons #x4029af #x00) ;;  
   (cons #x4029b0 #x48) ;; sub $0x8,%rbx 
   (cons #x4029b1 #x83) ;;  
   (cons #x4029b2 #xeb) ;;  
   (cons #x4029b3 #x08) ;;  
   (cons #x4029b4 #xff) ;; callq *%rax 
   (cons #x4029b5 #xd0) ;;  
   (cons #x4029b6 #x48) ;; mov (%rbx),%rax 
   (cons #x4029b7 #x8b) ;;  
   (cons #x4029b8 #x03) ;;  
   (cons #x4029b9 #x48) ;; cmp $0xffffffffffffffff,%rax 
   (cons #x4029ba #x83) ;;  
   (cons #x4029bb #xf8) ;;  
   (cons #x4029bc #xff) ;;  
   (cons #x4029bd #x75) ;; jne 4029b0 <__do_global_ctors_aux+0x20> 
   (cons #x4029be #xf1) ;;  
   (cons #x4029bf #x48) ;; add $0x8,%rsp 
   (cons #x4029c0 #x83) ;;  
   (cons #x4029c1 #xc4) ;;  
   (cons #x4029c2 #x08) ;;  
   (cons #x4029c3 #x5b) ;; pop %rbx 
   (cons #x4029c4 #x5d) ;; pop %rbp 
   (cons #x4029c5 #xc3) ;; retq 
   (cons #x4029c6 #x90) ;; nop 
   (cons #x4029c7 #x90) ;; nop 
   
;; Section: <_fini>:


   (cons #x4029c8 #x48) ;; sub $0x8,%rsp 
   (cons #x4029c9 #x83) ;;  
   (cons #x4029ca #xec) ;;  
   (cons #x4029cb #x08) ;;  
   (cons #x4029cc #xe8) ;; callq 400420 <__do_global_dtors_aux> 
   (cons #x4029cd #x4f) ;;  
   (cons #x4029ce #xda) ;;  
   (cons #x4029cf #xff) ;;  
   (cons #x4029d0 #xff) ;;  
   (cons #x4029d1 #x48) ;; add $0x8,%rsp 
   (cons #x4029d2 #x83) ;;  
   (cons #x4029d3 #xc4) ;;  
   (cons #x4029d4 #x08) ;;  
   (cons #x4029d5 #xc3) ;; retq 
   
;; Section: <_IO_stdin_used>:


   (cons #x4029d8 #x01) ;; add %eax,(%rax) 
   (cons #x4029d9 #x00) ;;  
   (cons #x4029da #x02) ;; add (%rax),%al 
   (cons #x4029db #x00) ;;  
   
;; Section: <.eh_frame_hdr>:


   (cons #x4029dc #x01) ;; add %ebx,(%rbx) 
   (cons #x4029dd #x1b) ;;  
   (cons #x4029de #x03) ;; add (%rbx),%edi 
   (cons #x4029df #x3b) ;;  
   (cons #x4029e0 #x80) ;; addb $0x0,(%rax) 
   (cons #x4029e1 #x00) ;;  
   (cons #x4029e2 #x00) ;;  
   (cons #x4029e3 #x00) ;; add %cl,(%rdi) 
   (cons #x4029e4 #x0f) ;;  
   (cons #x4029e5 #x00) ;; add %al,(%rax) 
   (cons #x4029e6 #x00) ;;  
   (cons #x4029e7 #x00) ;; add %dl,%ah 
   (cons #x4029e8 #xd4) ;;  
   (cons #x4029e9 #xd9) ;; fcos 
   (cons #x4029ea #xff) ;;  
   (cons #x4029eb #xff) ;; lcallq *-0x25280000(%rax,%rax,1) 
   (cons #x4029ec #x9c) ;;  
   (cons #x4029ed #x00) ;;  
   (cons #x4029ee #x00) ;;  
   (cons #x4029ef #x00) ;;  
   (cons #x4029f0 #xd8) ;;  
   (cons #x4029f1 #xda) ;;  
   (cons #x4029f2 #xff) ;; (bad) 
   (cons #x4029f3 #xff) ;; inc %esp 
   (cons #x4029f4 #xc4) ;;  
   (cons #x4029f5 #x00) ;; add %al,(%rax) 
   (cons #x4029f6 #x00) ;;  
   (cons #x4029f7 #x00) ;; add %dl,(%rdi) 
   (cons #x4029f8 #x17) ;;  
   (cons #x4029f9 #xdb) ;; (bad) 
   (cons #x4029fa #xff) ;;  
   (cons #x4029fb #xff) ;; jmpq *%rsp 
   (cons #x4029fc #xe4) ;;  
   (cons #x4029fd #x00) ;; add %al,(%rax) 
   (cons #x4029fe #x00) ;;  
   (cons #x4029ff #x00) ;; add %dl,-0x24(%rdx) 
   (cons #x402a00 #x52) ;;  
   (cons #x402a01 #xdc) ;;  
   (cons #x402a02 #xff) ;; (bad) 
   (cons #x402a03 #xff) ;; incl (%rcx,%rax,1) 
   (cons #x402a04 #x04) ;;  
   (cons #x402a05 #x01) ;;  
   (cons #x402a06 #x00) ;; add %al,(%rax) 
   (cons #x402a07 #x00) ;;  
   (cons #x402a08 #x21) ;; and %ebx,%esi 
   (cons #x402a09 #xde) ;;  
   (cons #x402a0a #xff) ;; (bad) 
   (cons #x402a0b #xff) ;; jmpq *(%rcx,%rax,1) 
   (cons #x402a0c #x24) ;;  
   (cons #x402a0d #x01) ;;  
   (cons #x402a0e #x00) ;; add %al,(%rax) 
   (cons #x402a0f #x00) ;;  
   (cons #x402a10 #xef) ;; out %eax,(%dx) 
   (cons #x402a11 #xdf) ;; (bad) 
   (cons #x402a12 #xff) ;;  
   (cons #x402a13 #xff) ;; incl 0x0(%rcx,%rax,1) 
   (cons #x402a14 #x44) ;;  
   (cons #x402a15 #x01) ;;  
   (cons #x402a16 #x00) ;;  
   (cons #x402a17 #x00) ;; add %cl,(%rdi) 
   (cons #x402a18 #x0f) ;;  
   (cons #x402a19 #xe1) ;; loope 402a1a <_IO_stdin_used+0x42> 
   (cons #x402a1a #xff) ;;  
   (cons #x402a1b #xff) ;; jmpq *0x0(%rcx,%rax,1) 
   (cons #x402a1c #x64) ;;  
   (cons #x402a1d #x01) ;;  
   (cons #x402a1e #x00) ;;  
   (cons #x402a1f #x00) ;; add %cl,-0x1e(%rsi) 
   (cons #x402a20 #x4e) ;;  
   (cons #x402a21 #xe2) ;;  
   (cons #x402a22 #xff) ;; (bad) 
   (cons #x402a23 #xff) ;; incl -0x17500000(%rcx,%rax,1) 
   (cons #x402a24 #x84) ;;  
   (cons #x402a25 #x01) ;;  
   (cons #x402a26 #x00) ;;  
   (cons #x402a27 #x00) ;;  
   (cons #x402a28 #xb0) ;;  
   (cons #x402a29 #xe8) ;;  
   (cons #x402a2a #xff) ;; (bad) 
   (cons #x402a2b #xff) ;; jmpq *-0x13150000(%rcx,%rax,1) 
   (cons #x402a2c #xa4) ;;  
   (cons #x402a2d #x01) ;;  
   (cons #x402a2e #x00) ;;  
   (cons #x402a2f #x00) ;;  
   (cons #x402a30 #xeb) ;;  
   (cons #x402a31 #xec) ;;  
   (cons #x402a32 #xff) ;; (bad) 
   (cons #x402a33 #xff) ;; dec %esp 
   (cons #x402a34 #xcc) ;;  
   (cons #x402a35 #x01) ;; add %eax,(%rax) 
   (cons #x402a36 #x00) ;;  
   (cons #x402a37 #x00) ;; add %cl,-0x13(%rbx) 
   (cons #x402a38 #x4b) ;;  
   (cons #x402a39 #xed) ;;  
   (cons #x402a3a #xff) ;; (bad) 
   (cons #x402a3b #xff) ;; ljmpq *<internal disassembler error> 
   (cons #x402a3c #xec) ;;  
   (cons #x402a3d #x01) ;; add %eax,(%rax) 
   (cons #x402a3e #x00) ;;  
   (cons #x402a3f #x00) ;; add %bl,-0x10(%rdi) 
   (cons #x402a40 #x5f) ;;  
   (cons #x402a41 #xf0) ;;  
   (cons #x402a42 #xff) ;; (bad) 
   (cons #x402a43 #xff) ;; callq *(%rdx,%rax,1) 
   (cons #x402a44 #x14) ;;  
   (cons #x402a45 #x02) ;;  
   (cons #x402a46 #x00) ;; add %al,(%rax) 
   (cons #x402a47 #x00) ;;  
   (cons #x402a48 #x98) ;; cwtl 
   (cons #x402a49 #xfe) ;; (bad) 
   (cons #x402a4a #xff) ;; (bad) 
   (cons #x402a4b #xff) ;; (bad) 
   (cons #x402a4c #x3c) ;; cmp $0x2,%al 
   (cons #x402a4d #x02) ;;  
   (cons #x402a4e #x00) ;; add %al,(%rax) 
   (cons #x402a4f #x00) ;;  
   (cons #x402a50 #x14) ;; adc $0xff,%al 
   (cons #x402a51 #xff) ;;  
   (cons #x402a52 #xff) ;; (bad) 
   (cons #x402a53 #xff) ;; lcallq *0x0(%rdx,%rax,1) 
   (cons #x402a54 #x5c) ;;  
   (cons #x402a55 #x02) ;;  
   (cons #x402a56 #x00) ;;  
   (cons #x402a57 #x00) ;; add %ah,0x284ffff(%rdi,%rdi,8) 
   (cons #x402a58 #xa4) ;;  
   (cons #x402a59 #xff) ;;  
   (cons #x402a5a #xff) ;;  
   (cons #x402a5b #xff) ;;  
   (cons #x402a5c #x84) ;;  
   (cons #x402a5d #x02) ;;  
   
;; Section: <__FRAME_END__-0x218>:


   (cons #x402a60 #x14) ;; adc $0x0,%al 
   (cons #x402a61 #x00) ;;  
   (cons #x402a62 #x00) ;; add %al,(%rax) 
   (cons #x402a63 #x00) ;;  
   (cons #x402a64 #x00) ;; add %al,(%rax) 
   (cons #x402a65 #x00) ;;  
   (cons #x402a66 #x00) ;; add %al,(%rax) 
   (cons #x402a67 #x00) ;;  
   (cons #x402a68 #x01) ;; add %edi,0x52(%rdx) 
   (cons #x402a69 #x7a) ;;  
   (cons #x402a6a #x52) ;;  
   (cons #x402a6b #x00) ;; add %al,(%rcx) 
   (cons #x402a6c #x01) ;;  
   (cons #x402a6d #x78) ;; js 402a7f <_IO_stdin_used+0xa7> 
   (cons #x402a6e #x10) ;;  
   (cons #x402a6f #x01) ;; add %ebx,(%rbx) 
   (cons #x402a70 #x1b) ;;  
   (cons #x402a71 #x0c) ;; or $0x7,%al 
   (cons #x402a72 #x07) ;;  
   (cons #x402a73 #x08) ;; or %dl,0x24000001(%rax) 
   (cons #x402a74 #x90) ;;  
   (cons #x402a75 #x01) ;;  
   (cons #x402a76 #x00) ;;  
   (cons #x402a77 #x00) ;;  
   (cons #x402a78 #x24) ;;  
   (cons #x402a79 #x00) ;; add %al,(%rax) 
   (cons #x402a7a #x00) ;;  
   (cons #x402a7b #x00) ;; add %bl,(%rax,%rax,1) 
   (cons #x402a7c #x1c) ;;  
   (cons #x402a7d #x00) ;;  
   (cons #x402a7e #x00) ;; add %al,(%rax) 
   (cons #x402a7f #x00) ;;  
   (cons #x402a80 #x30) ;; xor %bl,%cl 
   (cons #x402a81 #xd9) ;;  
   (cons #x402a82 #xff) ;; (bad) 
   (cons #x402a83 #xff) ;; jmpq *(%rax) 
   (cons #x402a84 #x20) ;;  
   (cons #x402a85 #x00) ;; add %al,(%rax) 
   (cons #x402a86 #x00) ;;  
   (cons #x402a87 #x00) ;; add %al,(%rax) 
   (cons #x402a88 #x00) ;;  
   (cons #x402a89 #x0e) ;; (bad) 
   (cons #x402a8a #x10) ;; adc %al,0xe(%rsi) 
   (cons #x402a8b #x46) ;;  
   (cons #x402a8c #x0e) ;;  
   (cons #x402a8d #x18) ;; sbb %cl,0xf(%rdx) 
   (cons #x402a8e #x4a) ;;  
   (cons #x402a8f #x0f) ;;  
   (cons #x402a90 #x0b) ;; or 0x8(%rdi),%esi 
   (cons #x402a91 #x77) ;;  
   (cons #x402a92 #x08) ;;  
   (cons #x402a93 #x80) ;; addb $0x3f,(%rax) 
   (cons #x402a94 #x00) ;;  
   (cons #x402a95 #x3f) ;;  
   (cons #x402a96 #x1a) ;; sbb (%rbx),%bh 
   (cons #x402a97 #x3b) ;;  
   (cons #x402a98 #x2a) ;; sub (%rbx),%dh 
   (cons #x402a99 #x33) ;;  
   (cons #x402a9a #x24) ;; and $0x22,%al 
   (cons #x402a9b #x22) ;;  
   (cons #x402a9c #x00) ;; add %al,(%rax) 
   (cons #x402a9d #x00) ;;  
   (cons #x402a9e #x00) ;; add %al,(%rax) 
   (cons #x402a9f #x00) ;;  
   (cons #x402aa0 #x1c) ;; sbb $0x0,%al 
   (cons #x402aa1 #x00) ;;  
   (cons #x402aa2 #x00) ;; add %al,(%rax) 
   (cons #x402aa3 #x00) ;;  
   (cons #x402aa4 #x44) ;; add %r8b,(%rax) 
   (cons #x402aa5 #x00) ;;  
   (cons #x402aa6 #x00) ;;  
   (cons #x402aa7 #x00) ;; add %cl,(%rdx,%rbx,8) 
   (cons #x402aa8 #x0c) ;;  
   (cons #x402aa9 #xda) ;;  
   (cons #x402aaa #xff) ;; (bad) 
   (cons #x402aab #xff) ;; (bad) 
   (cons #x402aac #x3f) ;; (bad) 
   (cons #x402aad #x00) ;; add %al,(%rax) 
   (cons #x402aae #x00) ;;  
   (cons #x402aaf #x00) ;; add %al,(%rax) 
   (cons #x402ab0 #x00) ;;  
   (cons #x402ab1 #x41) ;; rex.B (bad) 
   (cons #x402ab2 #x0e) ;;  
   (cons #x402ab3 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402ab4 #x86) ;;  
   (cons #x402ab5 #x02) ;;  
   (cons #x402ab6 #x43) ;;  
   (cons #x402ab7 #x0d) ;;  
   (cons #x402ab8 #x06) ;;  
   (cons #x402ab9 #x7a) ;; jp 402ac7 <_IO_stdin_used+0xef> 
   (cons #x402aba #x0c) ;;  
   (cons #x402abb #x07) ;; (bad) 
   (cons #x402abc #x08) ;; or %al,(%rax) 
   (cons #x402abd #x00) ;;  
   (cons #x402abe #x00) ;; add %al,(%rax) 
   (cons #x402abf #x00) ;;  
   (cons #x402ac0 #x1c) ;; sbb $0x0,%al 
   (cons #x402ac1 #x00) ;;  
   (cons #x402ac2 #x00) ;; add %al,(%rax) 
   (cons #x402ac3 #x00) ;;  
   (cons #x402ac4 #x64) ;; add %al,%fs:(%rax) 
   (cons #x402ac5 #x00) ;;  
   (cons #x402ac6 #x00) ;;  
   (cons #x402ac7 #x00) ;; add %ch,(%rbx) 
   (cons #x402ac8 #x2b) ;;  
   (cons #x402ac9 #xda) ;; (bad) 
   (cons #x402aca #xff) ;;  
   (cons #x402acb #xff) ;; (bad) 
   (cons #x402acc #x3b) ;; cmp (%rcx),%eax 
   (cons #x402acd #x01) ;;  
   (cons #x402ace #x00) ;; add %al,(%rax) 
   (cons #x402acf #x00) ;;  
   (cons #x402ad0 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402ad1 #x41) ;;  
   (cons #x402ad2 #x0e) ;;  
   (cons #x402ad3 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402ad4 #x86) ;;  
   (cons #x402ad5 #x02) ;;  
   (cons #x402ad6 #x43) ;;  
   (cons #x402ad7 #x0d) ;;  
   (cons #x402ad8 #x06) ;;  
   (cons #x402ad9 #x03) ;; add (%rsi),%esi 
   (cons #x402ada #x36) ;;  
   (cons #x402adb #x01) ;; add %ecx,(%rdi,%rax,1) 
   (cons #x402adc #x0c) ;;  
   (cons #x402add #x07) ;;  
   (cons #x402ade #x08) ;; or %al,(%rax) 
   (cons #x402adf #x00) ;;  
   (cons #x402ae0 #x1c) ;; sbb $0x0,%al 
   (cons #x402ae1 #x00) ;;  
   (cons #x402ae2 #x00) ;; add %al,(%rax) 
   (cons #x402ae3 #x00) ;;  
   (cons #x402ae4 #x84) ;; test %al,(%rax) 
   (cons #x402ae5 #x00) ;;  
   (cons #x402ae6 #x00) ;; add %al,(%rax) 
   (cons #x402ae7 #x00) ;;  
   (cons #x402ae8 #x46) ;; rex.RX (bad) 
   (cons #x402ae9 #xdb) ;;  
   (cons #x402aea #xff) ;;  
   (cons #x402aeb #xff) ;; dec %edi 
   (cons #x402aec #xcf) ;;  
   (cons #x402aed #x01) ;; add %eax,(%rax) 
   (cons #x402aee #x00) ;;  
   (cons #x402aef #x00) ;; add %al,(%rax) 
   (cons #x402af0 #x00) ;;  
   (cons #x402af1 #x41) ;; rex.B (bad) 
   (cons #x402af2 #x0e) ;;  
   (cons #x402af3 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402af4 #x86) ;;  
   (cons #x402af5 #x02) ;;  
   (cons #x402af6 #x43) ;;  
   (cons #x402af7 #x0d) ;;  
   (cons #x402af8 #x06) ;;  
   (cons #x402af9 #x03) ;; add %edx,%ecx 
   (cons #x402afa #xca) ;;  
   (cons #x402afb #x01) ;; add %ecx,(%rdi,%rax,1) 
   (cons #x402afc #x0c) ;;  
   (cons #x402afd #x07) ;;  
   (cons #x402afe #x08) ;; or %al,(%rax) 
   (cons #x402aff #x00) ;;  
   (cons #x402b00 #x1c) ;; sbb $0x0,%al 
   (cons #x402b01 #x00) ;;  
   (cons #x402b02 #x00) ;; add %al,(%rax) 
   (cons #x402b03 #x00) ;;  
   (cons #x402b04 #xa4) ;; movsb %ds:(%rsi),%es:(%rdi) 
   (cons #x402b05 #x00) ;; add %al,(%rax) 
   (cons #x402b06 #x00) ;;  
   (cons #x402b07 #x00) ;; add %dh,%ch 
   (cons #x402b08 #xf5) ;;  
   (cons #x402b09 #xdc) ;; fdivr %st,%st(7) 
   (cons #x402b0a #xff) ;;  
   (cons #x402b0b #xff) ;; dec %esi 
   (cons #x402b0c #xce) ;;  
   (cons #x402b0d #x01) ;; add %eax,(%rax) 
   (cons #x402b0e #x00) ;;  
   (cons #x402b0f #x00) ;; add %al,(%rax) 
   (cons #x402b10 #x00) ;;  
   (cons #x402b11 #x41) ;; rex.B (bad) 
   (cons #x402b12 #x0e) ;;  
   (cons #x402b13 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402b14 #x86) ;;  
   (cons #x402b15 #x02) ;;  
   (cons #x402b16 #x43) ;;  
   (cons #x402b17 #x0d) ;;  
   (cons #x402b18 #x06) ;;  
   (cons #x402b19 #x03) ;; add %ecx,%ecx 
   (cons #x402b1a #xc9) ;;  
   (cons #x402b1b #x01) ;; add %ecx,(%rdi,%rax,1) 
   (cons #x402b1c #x0c) ;;  
   (cons #x402b1d #x07) ;;  
   (cons #x402b1e #x08) ;; or %al,(%rax) 
   (cons #x402b1f #x00) ;;  
   (cons #x402b20 #x1c) ;; sbb $0x0,%al 
   (cons #x402b21 #x00) ;;  
   (cons #x402b22 #x00) ;; add %al,(%rax) 
   (cons #x402b23 #x00) ;;  
   (cons #x402b24 #xc4) ;; (bad) 
   (cons #x402b25 #x00) ;; add %al,(%rax) 
   (cons #x402b26 #x00) ;;  
   (cons #x402b27 #x00) ;; add %ah,0x20ffffde(%rbx) 
   (cons #x402b28 #xa3) ;;  
   (cons #x402b29 #xde) ;;  
   (cons #x402b2a #xff) ;;  
   (cons #x402b2b #xff) ;;  
   (cons #x402b2c #x20) ;;  
   (cons #x402b2d #x01) ;; add %eax,(%rax) 
   (cons #x402b2e #x00) ;;  
   (cons #x402b2f #x00) ;; add %al,(%rax) 
   (cons #x402b30 #x00) ;;  
   (cons #x402b31 #x41) ;; rex.B (bad) 
   (cons #x402b32 #x0e) ;;  
   (cons #x402b33 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402b34 #x86) ;;  
   (cons #x402b35 #x02) ;;  
   (cons #x402b36 #x43) ;;  
   (cons #x402b37 #x0d) ;;  
   (cons #x402b38 #x06) ;;  
   (cons #x402b39 #x03) ;; add (%rbx),%ebx 
   (cons #x402b3a #x1b) ;;  
   (cons #x402b3b #x01) ;; add %ecx,(%rdi,%rax,1) 
   (cons #x402b3c #x0c) ;;  
   (cons #x402b3d #x07) ;;  
   (cons #x402b3e #x08) ;; or %al,(%rax) 
   (cons #x402b3f #x00) ;;  
   (cons #x402b40 #x1c) ;; sbb $0x0,%al 
   (cons #x402b41 #x00) ;;  
   (cons #x402b42 #x00) ;; add %al,(%rax) 
   (cons #x402b43 #x00) ;;  
   (cons #x402b44 #xe4) ;; in $0x0,%al 
   (cons #x402b45 #x00) ;;  
   (cons #x402b46 #x00) ;; add %al,(%rax) 
   (cons #x402b47 #x00) ;;  
   (cons #x402b48 #xa3) ;; movabs %eax,0x13fffffdf 
   (cons #x402b49 #xdf) ;;  
   (cons #x402b4a #xff) ;;  
   (cons #x402b4b #xff) ;;  
   (cons #x402b4c #x3f) ;;  
   (cons #x402b4d #x01) ;;  
   (cons #x402b4e #x00) ;;  
   (cons #x402b4f #x00) ;;  
   (cons #x402b50 #x00) ;;  
   (cons #x402b51 #x41) ;; rex.B (bad) 
   (cons #x402b52 #x0e) ;;  
   (cons #x402b53 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402b54 #x86) ;;  
   (cons #x402b55 #x02) ;;  
   (cons #x402b56 #x43) ;;  
   (cons #x402b57 #x0d) ;;  
   (cons #x402b58 #x06) ;;  
   (cons #x402b59 #x03) ;; add (%rdx),%edi 
   (cons #x402b5a #x3a) ;;  
   (cons #x402b5b #x01) ;; add %ecx,(%rdi,%rax,1) 
   (cons #x402b5c #x0c) ;;  
   (cons #x402b5d #x07) ;;  
   (cons #x402b5e #x08) ;; or %al,(%rax) 
   (cons #x402b5f #x00) ;;  
   (cons #x402b60 #x1c) ;; sbb $0x0,%al 
   (cons #x402b61 #x00) ;;  
   (cons #x402b62 #x00) ;; add %al,(%rax) 
   (cons #x402b63 #x00) ;;  
   (cons #x402b64 #x04) ;; add $0x1,%al 
   (cons #x402b65 #x01) ;;  
   (cons #x402b66 #x00) ;; add %al,(%rax) 
   (cons #x402b67 #x00) ;;  
   (cons #x402b68 #xc2) ;; retq $0xffe0 
   (cons #x402b69 #xe0) ;;  
   (cons #x402b6a #xff) ;;  
   (cons #x402b6b #xff) ;; jmpq *0x6(%rdx) 
   (cons #x402b6c #x62) ;;  
   (cons #x402b6d #x06) ;;  
   (cons #x402b6e #x00) ;; add %al,(%rax) 
   (cons #x402b6f #x00) ;;  
   (cons #x402b70 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402b71 #x41) ;;  
   (cons #x402b72 #x0e) ;;  
   (cons #x402b73 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402b74 #x86) ;;  
   (cons #x402b75 #x02) ;;  
   (cons #x402b76 #x43) ;;  
   (cons #x402b77 #x0d) ;;  
   (cons #x402b78 #x06) ;;  
   (cons #x402b79 #x03) ;; add 0x6(%rbp),%ebx 
   (cons #x402b7a #x5d) ;;  
   (cons #x402b7b #x06) ;;  
   (cons #x402b7c #x0c) ;; or $0x7,%al 
   (cons #x402b7d #x07) ;;  
   (cons #x402b7e #x08) ;; or %al,(%rax) 
   (cons #x402b7f #x00) ;;  
   (cons #x402b80 #x24) ;; and $0x0,%al 
   (cons #x402b81 #x00) ;;  
   (cons #x402b82 #x00) ;; add %al,(%rax) 
   (cons #x402b83 #x00) ;;  
   (cons #x402b84 #x24) ;; and $0x1,%al 
   (cons #x402b85 #x01) ;;  
   (cons #x402b86 #x00) ;; add %al,(%rax) 
   (cons #x402b87 #x00) ;;  
   (cons #x402b88 #x04) ;; add $0xe7,%al 
   (cons #x402b89 #xe7) ;;  
   (cons #x402b8a #xff) ;; (bad) 
   (cons #x402b8b #xff) ;; (bad) 
   (cons #x402b8c #x3b) ;; cmp (%rax,%rax,1),%eax 
   (cons #x402b8d #x04) ;;  
   (cons #x402b8e #x00) ;;  
   (cons #x402b8f #x00) ;; add %al,(%rax) 
   (cons #x402b90 #x00) ;;  
   (cons #x402b91 #x41) ;; rex.B (bad) 
   (cons #x402b92 #x0e) ;;  
   (cons #x402b93 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402b94 #x86) ;;  
   (cons #x402b95 #x02) ;;  
   (cons #x402b96 #x43) ;;  
   (cons #x402b97 #x0d) ;;  
   (cons #x402b98 #x06) ;;  
   (cons #x402b99 #x02) ;; add -0x7d(%rsi),%al 
   (cons #x402b9a #x46) ;;  
   (cons #x402b9b #x83) ;;  
   (cons #x402b9c #x03) ;; add (%rbx),%eax 
   (cons #x402b9d #x03) ;;  
   (cons #x402b9e #xf0) ;; lock add (%rdi,%rax,1),%ecx 
   (cons #x402b9f #x03) ;;  
   (cons #x402ba0 #x0c) ;;  
   (cons #x402ba1 #x07) ;;  
   (cons #x402ba2 #x08) ;; or %al,(%rax) 
   (cons #x402ba3 #x00) ;;  
   (cons #x402ba4 #x00) ;; add %al,(%rax) 
   (cons #x402ba5 #x00) ;;  
   (cons #x402ba6 #x00) ;; add %al,(%rax) 
   (cons #x402ba7 #x00) ;;  
   (cons #x402ba8 #x1c) ;; sbb $0x0,%al 
   (cons #x402ba9 #x00) ;;  
   (cons #x402baa #x00) ;; add %al,(%rax) 
   (cons #x402bab #x00) ;;  
   (cons #x402bac #x4c) ;; add %r8,(%rax) 
   (cons #x402bad #x01) ;;  
   (cons #x402bae #x00) ;;  
   (cons #x402baf #x00) ;; add %dl,(%rdi) 
   (cons #x402bb0 #x17) ;;  
   (cons #x402bb1 #xeb) ;; jmp 402bb2 <_IO_stdin_used+0x1da> 
   (cons #x402bb2 #xff) ;;  
   (cons #x402bb3 #xff) ;; jmpq *0x0(%rax) 
   (cons #x402bb4 #x60) ;;  
   (cons #x402bb5 #x00) ;;  
   (cons #x402bb6 #x00) ;; add %al,(%rax) 
   (cons #x402bb7 #x00) ;;  
   (cons #x402bb8 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402bb9 #x41) ;;  
   (cons #x402bba #x0e) ;;  
   (cons #x402bbb #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402bbc #x86) ;;  
   (cons #x402bbd #x02) ;;  
   (cons #x402bbe #x43) ;;  
   (cons #x402bbf #x0d) ;;  
   (cons #x402bc0 #x06) ;;  
   (cons #x402bc1 #x02) ;; add 0xc(%rbx),%bl 
   (cons #x402bc2 #x5b) ;;  
   (cons #x402bc3 #x0c) ;;  
   (cons #x402bc4 #x07) ;; (bad) 
   (cons #x402bc5 #x08) ;; or %al,(%rax) 
   (cons #x402bc6 #x00) ;;  
   (cons #x402bc7 #x00) ;; add %ah,(%rax,%rax,1) 
   (cons #x402bc8 #x24) ;;  
   (cons #x402bc9 #x00) ;;  
   (cons #x402bca #x00) ;; add %al,(%rax) 
   (cons #x402bcb #x00) ;;  
   (cons #x402bcc #x6c) ;; insb (%dx),%es:(%rdi) 
   (cons #x402bcd #x01) ;; add %eax,(%rax) 
   (cons #x402bce #x00) ;;  
   (cons #x402bcf #x00) ;; add %dl,-0x15(%rdi) 
   (cons #x402bd0 #x57) ;;  
   (cons #x402bd1 #xeb) ;;  
   (cons #x402bd2 #xff) ;; (bad) 
   (cons #x402bd3 #xff) ;; callq *(%rbx,%rax,1) 
   (cons #x402bd4 #x14) ;;  
   (cons #x402bd5 #x03) ;;  
   (cons #x402bd6 #x00) ;; add %al,(%rax) 
   (cons #x402bd7 #x00) ;;  
   (cons #x402bd8 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402bd9 #x41) ;;  
   (cons #x402bda #x0e) ;;  
   (cons #x402bdb #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402bdc #x86) ;;  
   (cons #x402bdd #x02) ;;  
   (cons #x402bde #x43) ;;  
   (cons #x402bdf #x0d) ;;  
   (cons #x402be0 #x06) ;;  
   (cons #x402be1 #x55) ;; push %rbp 
   (cons #x402be2 #x83) ;; addl $0x3,(%rbx) 
   (cons #x402be3 #x03) ;;  
   (cons #x402be4 #x03) ;;  
   (cons #x402be5 #xfa) ;; cli 
   (cons #x402be6 #x02) ;; add (%rdi,%rax,1),%cl 
   (cons #x402be7 #x0c) ;;  
   (cons #x402be8 #x07) ;;  
   (cons #x402be9 #x08) ;; or %al,(%rax) 
   (cons #x402bea #x00) ;;  
   (cons #x402beb #x00) ;; add %al,(%rax) 
   (cons #x402bec #x00) ;;  
   (cons #x402bed #x00) ;; add %al,(%rax) 
   (cons #x402bee #x00) ;;  
   (cons #x402bef #x00) ;; add %ah,(%rax,%rax,1) 
   (cons #x402bf0 #x24) ;;  
   (cons #x402bf1 #x00) ;;  
   (cons #x402bf2 #x00) ;; add %al,(%rax) 
   (cons #x402bf3 #x00) ;;  
   (cons #x402bf4 #x94) ;; xchg %eax,%esp 
   (cons #x402bf5 #x01) ;; add %eax,(%rax) 
   (cons #x402bf6 #x00) ;;  
   (cons #x402bf7 #x00) ;; add %al,-0x12(%rbx) 
   (cons #x402bf8 #x43) ;;  
   (cons #x402bf9 #xee) ;;  
   (cons #x402bfa #xff) ;; (bad) 
   (cons #x402bfb #xff) ;; (bad) 
   (cons #x402bfc #x39) ;; cmp %ecx,(%rsi) 
   (cons #x402bfd #x0e) ;;  
   (cons #x402bfe #x00) ;; add %al,(%rax) 
   (cons #x402bff #x00) ;;  
   (cons #x402c00 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402c01 #x41) ;;  
   (cons #x402c02 #x0e) ;;  
   (cons #x402c03 #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402c04 #x86) ;;  
   (cons #x402c05 #x02) ;;  
   (cons #x402c06 #x43) ;;  
   (cons #x402c07 #x0d) ;;  
   (cons #x402c08 #x06) ;;  
   (cons #x402c09 #x02) ;; add -0x61fcfc7d(%rsi),%dl 
   (cons #x402c0a #x96) ;;  
   (cons #x402c0b #x83) ;;  
   (cons #x402c0c #x03) ;;  
   (cons #x402c0d #x03) ;;  
   (cons #x402c0e #x9e) ;;  
   (cons #x402c0f #x0d) ;; or $0x8070c,%eax 
   (cons #x402c10 #x0c) ;;  
   (cons #x402c11 #x07) ;;  
   (cons #x402c12 #x08) ;;  
   (cons #x402c13 #x00) ;;  
   (cons #x402c14 #x00) ;; add %al,(%rax) 
   (cons #x402c15 #x00) ;;  
   (cons #x402c16 #x00) ;; add %al,(%rax) 
   (cons #x402c17 #x00) ;;  
   (cons #x402c18 #x1c) ;; sbb $0x0,%al 
   (cons #x402c19 #x00) ;;  
   (cons #x402c1a #x00) ;; add %al,(%rax) 
   (cons #x402c1b #x00) ;;  
   (cons #x402c1c #xbc) ;; mov $0x54000001,%esp 
   (cons #x402c1d #x01) ;;  
   (cons #x402c1e #x00) ;;  
   (cons #x402c1f #x00) ;;  
   (cons #x402c20 #x54) ;;  
   (cons #x402c21 #xfc) ;; cld 
   (cons #x402c22 #xff) ;; (bad) 
   (cons #x402c23 #xff) ;; pushq 0x0(%rbp) 
   (cons #x402c24 #x75) ;;  
   (cons #x402c25 #x00) ;;  
   (cons #x402c26 #x00) ;; add %al,(%rax) 
   (cons #x402c27 #x00) ;;  
   (cons #x402c28 #x00) ;; add %al,0xe(%rcx) 
   (cons #x402c29 #x41) ;;  
   (cons #x402c2a #x0e) ;;  
   (cons #x402c2b #x10) ;; adc %al,0x60d4302(%rsi) 
   (cons #x402c2c #x86) ;;  
   (cons #x402c2d #x02) ;;  
   (cons #x402c2e #x43) ;;  
   (cons #x402c2f #x0d) ;;  
   (cons #x402c30 #x06) ;;  
   (cons #x402c31 #x02) ;; add 0xc(%rax),%dh 
   (cons #x402c32 #x70) ;;  
   (cons #x402c33 #x0c) ;;  
   (cons #x402c34 #x07) ;; (bad) 
   (cons #x402c35 #x08) ;; or %al,(%rax) 
   (cons #x402c36 #x00) ;;  
   (cons #x402c37 #x00) ;; add %ah,(%rax,%rax,1) 
   (cons #x402c38 #x24) ;;  
   (cons #x402c39 #x00) ;;  
   (cons #x402c3a #x00) ;; add %al,(%rax) 
   (cons #x402c3b #x00) ;;  
   (cons #x402c3c #xdc) ;; faddl (%rcx) 
   (cons #x402c3d #x01) ;;  
   (cons #x402c3e #x00) ;; add %al,(%rax) 
   (cons #x402c3f #x00) ;;  
   (cons #x402c40 #xb0) ;; mov $0xfc,%al 
   (cons #x402c41 #xfc) ;;  
   (cons #x402c42 #xff) ;; (bad) 
   (cons #x402c43 #xff) ;; decl 0x0(%rcx) 
   (cons #x402c44 #x89) ;;  
   (cons #x402c45 #x00) ;;  
   (cons #x402c46 #x00) ;;  
   (cons #x402c47 #x00) ;;  
   (cons #x402c48 #x00) ;;  
   (cons #x402c49 #x51) ;; push %rcx 
   (cons #x402c4a #x8c) ;; mov %es,0xe5f0686(%rip) # e9f32d6 <memory+0xe3f0296> 
   (cons #x402c4b #x05) ;;  
   (cons #x402c4c #x86) ;;  
   (cons #x402c4d #x06) ;;  
   (cons #x402c4e #x5f) ;;  
   (cons #x402c4f #x0e) ;;  
   (cons #x402c50 #x40) ;; rex addl $0xffffff8f,(%rdi) 
   (cons #x402c51 #x83) ;;  
   (cons #x402c52 #x07) ;;  
   (cons #x402c53 #x8f) ;;  
   (cons #x402c54 #x02) ;; add 0x2048d03(%rsi),%cl 
   (cons #x402c55 #x8e) ;;  
   (cons #x402c56 #x03) ;;  
   (cons #x402c57 #x8d) ;;  
   (cons #x402c58 #x04) ;;  
   (cons #x402c59 #x02) ;;  
   (cons #x402c5a #x58) ;; pop %rax 
   (cons #x402c5b #x0e) ;; (bad) 
   (cons #x402c5c #x08) ;; or %al,(%rax) 
   (cons #x402c5d #x00) ;;  
   (cons #x402c5e #x00) ;; add %al,(%rax) 
   (cons #x402c5f #x00) ;;  
   (cons #x402c60 #x14) ;; adc $0x0,%al 
   (cons #x402c61 #x00) ;;  
   (cons #x402c62 #x00) ;; add %al,(%rax) 
   (cons #x402c63 #x00) ;;  
   (cons #x402c64 #x04) ;; add $0x2,%al 
   (cons #x402c65 #x02) ;;  
   (cons #x402c66 #x00) ;; add %al,(%rax) 
   (cons #x402c67 #x00) ;;  
   (cons #x402c68 #x18) ;; sbb %bh,%ch 
   (cons #x402c69 #xfd) ;;  
   (cons #x402c6a #xff) ;; (bad) 
   (cons #x402c6b #xff) ;; incl (%rdx) 
   (cons #x402c6c #x02) ;;  
   
;; Section: <__FRAME_END__>:


   (cons #x402c78 #x00) ;; add %al,(%rax) 
   (cons #x402c79 #x00) ;;  
   
;; Section: <__CTOR_LIST__>:


   (cons #x602e28 #xff) ;; (bad) 
   (cons #x602e29 #xff) ;; (bad) 
   (cons #x602e2a #xff) ;; (bad) 
   (cons #x602e2b #xff) ;; (bad) 
   (cons #x602e2c #xff) ;; (bad) 
   (cons #x602e2d #xff) ;; (bad) 
   (cons #x602e2e #xff) ;; (bad) 
   (cons #x602e2f #xff) ;; incl (%rax) 
   (cons #x602e30 #x00) ;;  
   
;; Section: <__CTOR_END__>:


   
;; Section: <__DTOR_LIST__>:


   (cons #x602e38 #xff) ;; (bad) 
   (cons #x602e39 #xff) ;; (bad) 
   (cons #x602e3a #xff) ;; (bad) 
   (cons #x602e3b #xff) ;; (bad) 
   (cons #x602e3c #xff) ;; (bad) 
   (cons #x602e3d #xff) ;; (bad) 
   (cons #x602e3e #xff) ;; (bad) 
   (cons #x602e3f #xff) ;; incl (%rax) 
   (cons #x602e40 #x00) ;;  
   
;; Section: <__JCR_END__>:


   
;; Section: <_DYNAMIC>:


   (cons #x602e50 #x01) ;; add %eax,(%rax) 
   (cons #x602e51 #x00) ;;  
   (cons #x602e52 #x00) ;; add %al,(%rax) 
   (cons #x602e53 #x00) ;;  
   (cons #x602e54 #x00) ;; add %al,(%rax) 
   (cons #x602e55 #x00) ;;  
   (cons #x602e56 #x00) ;; add %al,(%rax) 
   (cons #x602e57 #x00) ;;  
   (cons #x602e58 #x10) ;; adc %al,(%rax) 
   (cons #x602e59 #x00) ;;  
   (cons #x602e5a #x00) ;; add %al,(%rax) 
   (cons #x602e5b #x00) ;;  
   (cons #x602e5c #x00) ;; add %al,(%rax) 
   (cons #x602e5d #x00) ;;  
   (cons #x602e5e #x00) ;; add %al,(%rax) 
   (cons #x602e5f #x00) ;;  
   (cons #x602e60 #x0c) ;; or $0x0,%al 
   (cons #x602e61 #x00) ;;  
   (cons #x602e62 #x00) ;; add %al,(%rax) 
   (cons #x602e63 #x00) ;;  
   (cons #x602e64 #x00) ;; add %al,(%rax) 
   (cons #x602e65 #x00) ;;  
   (cons #x602e66 #x00) ;; add %al,(%rax) 
   (cons #x602e67 #x00) ;;  
   (cons #x602e68 #x90) ;; nop 
   (cons #x602e69 #x03) ;; add 0x0(%rax),%eax 
   (cons #x602e6a #x40) ;;  
   (cons #x602e6b #x00) ;;  
   (cons #x602e6c #x00) ;; add %al,(%rax) 
   (cons #x602e6d #x00) ;;  
   (cons #x602e6e #x00) ;; add %al,(%rax) 
   (cons #x602e6f #x00) ;;  
   (cons #x602e70 #x0d) ;; or $0x0,%eax 
   (cons #x602e71 #x00) ;;  
   (cons #x602e72 #x00) ;;  
   (cons #x602e73 #x00) ;;  
   (cons #x602e74 #x00) ;;  
   (cons #x602e75 #x00) ;; add %al,(%rax) 
   (cons #x602e76 #x00) ;;  
   (cons #x602e77 #x00) ;; add %cl,%al 
   (cons #x602e78 #xc8) ;;  
   (cons #x602e79 #x29) ;; sub %eax,0x0(%rax) 
   (cons #x602e7a #x40) ;;  
   (cons #x602e7b #x00) ;;  
   (cons #x602e7c #x00) ;; add %al,(%rax) 
   (cons #x602e7d #x00) ;;  
   (cons #x602e7e #x00) ;; add %al,(%rax) 
   (cons #x602e7f #x00) ;;  
   (cons #x602e80 #xf5) ;; cmc 
   (cons #x602e81 #xfe) ;; (bad) 
   (cons #x602e82 #xff) ;; ljmpq *0x0(%rdi) 
   (cons #x602e83 #x6f) ;;  
   (cons #x602e84 #x00) ;;  
   (cons #x602e85 #x00) ;; add %al,(%rax) 
   (cons #x602e86 #x00) ;;  
   (cons #x602e87 #x00) ;; add %bl,0x4002(%rax) 
   (cons #x602e88 #x98) ;;  
   (cons #x602e89 #x02) ;;  
   (cons #x602e8a #x40) ;;  
   (cons #x602e8b #x00) ;;  
   (cons #x602e8c #x00) ;;  
   (cons #x602e8d #x00) ;; add %al,(%rax) 
   (cons #x602e8e #x00) ;;  
   (cons #x602e8f #x00) ;; add %al,0x0(%rip) # 602e95 <_DYNAMIC+0x45> 
   (cons #x602e90 #x05) ;;  
   (cons #x602e91 #x00) ;;  
   (cons #x602e92 #x00) ;;  
   (cons #x602e93 #x00) ;;  
   (cons #x602e94 #x00) ;;  
   (cons #x602e95 #x00) ;; add %al,(%rax) 
   (cons #x602e96 #x00) ;;  
   (cons #x602e97 #x00) ;; add %al,(%rax) 
   (cons #x602e98 #x00) ;;  
   (cons #x602e99 #x03) ;; add 0x0(%rax),%eax 
   (cons #x602e9a #x40) ;;  
   (cons #x602e9b #x00) ;;  
   (cons #x602e9c #x00) ;; add %al,(%rax) 
   (cons #x602e9d #x00) ;;  
   (cons #x602e9e #x00) ;; add %al,(%rax) 
   (cons #x602e9f #x00) ;;  
   (cons #x602ea0 #x06) ;; (bad) 
   (cons #x602ea1 #x00) ;; add %al,(%rax) 
   (cons #x602ea2 #x00) ;;  
   (cons #x602ea3 #x00) ;; add %al,(%rax) 
   (cons #x602ea4 #x00) ;;  
   (cons #x602ea5 #x00) ;; add %al,(%rax) 
   (cons #x602ea6 #x00) ;;  
   (cons #x602ea7 #x00) ;; add %bh,0x4002(%rax) 
   (cons #x602ea8 #xb8) ;;  
   (cons #x602ea9 #x02) ;;  
   (cons #x602eaa #x40) ;;  
   (cons #x602eab #x00) ;;  
   (cons #x602eac #x00) ;;  
   (cons #x602ead #x00) ;; add %al,(%rax) 
   (cons #x602eae #x00) ;;  
   (cons #x602eaf #x00) ;; add %cl,(%rdx) 
   (cons #x602eb0 #x0a) ;;  
   (cons #x602eb1 #x00) ;; add %al,(%rax) 
   (cons #x602eb2 #x00) ;;  
   (cons #x602eb3 #x00) ;; add %al,(%rax) 
   (cons #x602eb4 #x00) ;;  
   (cons #x602eb5 #x00) ;; add %al,(%rax) 
   (cons #x602eb6 #x00) ;;  
   (cons #x602eb7 #x00) ;; add %bh,(%rax) 
   (cons #x602eb8 #x38) ;;  
   (cons #x602eb9 #x00) ;; add %al,(%rax) 
   (cons #x602eba #x00) ;;  
   (cons #x602ebb #x00) ;; add %al,(%rax) 
   (cons #x602ebc #x00) ;;  
   (cons #x602ebd #x00) ;; add %al,(%rax) 
   (cons #x602ebe #x00) ;;  
   (cons #x602ebf #x00) ;; add %cl,(%rbx) 
   (cons #x602ec0 #x0b) ;;  
   (cons #x602ec1 #x00) ;; add %al,(%rax) 
   (cons #x602ec2 #x00) ;;  
   (cons #x602ec3 #x00) ;; add %al,(%rax) 
   (cons #x602ec4 #x00) ;;  
   (cons #x602ec5 #x00) ;; add %al,(%rax) 
   (cons #x602ec6 #x00) ;;  
   (cons #x602ec7 #x00) ;; add %bl,(%rax) 
   (cons #x602ec8 #x18) ;;  
   (cons #x602ec9 #x00) ;; add %al,(%rax) 
   (cons #x602eca #x00) ;;  
   (cons #x602ecb #x00) ;; add %al,(%rax) 
   (cons #x602ecc #x00) ;;  
   (cons #x602ecd #x00) ;; add %al,(%rax) 
   (cons #x602ece #x00) ;;  
   (cons #x602ecf #x00) ;; add %dl,0x0(%rip) # 602ed5 <_DYNAMIC+0x85> 
   (cons #x602ed0 #x15) ;;  
   (cons #x602ed1 #x00) ;;  
   (cons #x602ed2 #x00) ;;  
   (cons #x602ed3 #x00) ;;  
   (cons #x602ed4 #x00) ;;  
   
;; Section: <.got>:


   
;; Section: <_GLOBAL_OFFSET_TABLE_>:


   (cons #x602fe8 #x50) ;; push %rax 
   (cons #x602fe9 #x2e) ;; cs 
   (cons #x602fea #x60) ;; (bad) 
   
;; Section: <__data_start>:


   
;; Section: <completed.6531>:


   
;; Section: <dtor_idx.6533>:


   
;; Section: <memory>:


   
;; Section: <.comment>:


   (cons #x0 #x47) ;; rex.RXB 
   (cons #x1 #x43) ;; rex.XB 
   (cons #x2 #x43) ;; rex.XB cmp (%r8),%spl 
   (cons #x3 #x3a) ;;  
   (cons #x4 #x20) ;;  
   (cons #x5 #x28) ;; sub %dl,0x62(%rbp) 
   (cons #x6 #x55) ;;  
   (cons #x7 #x62) ;;  
   (cons #x8 #x75) ;; jne 78 <_init-0x400318> 
   (cons #x9 #x6e) ;;  
   (cons #xa #x74) ;; je 81 <_init-0x40030f> 
   (cons #xb #x75) ;;  
   (cons #xc #x2f) ;; (bad) 
   (cons #xd #x4c) ;; imul $0x34206f72,0x61(%rsi),%r13 
   (cons #xe #x69) ;;  
   (cons #xf #x6e) ;;  
   (cons #x10 #x61) ;;  
   (cons #x11 #x72) ;;  
   (cons #x12 #x6f) ;;  
   (cons #x13 #x20) ;;  
   (cons #x14 #x34) ;;  
   (cons #x15 #x2e) ;; cs ss xor %cs:%ss:0x75627531(%rip),%ebp # 7562754f <_end+0x5d2ac10f> 
   (cons #x16 #x36) ;;  
   (cons #x17 #x2e) ;;  
   (cons #x18 #x33) ;;  
   (cons #x19 #x2d) ;;  
   (cons #x1a #x31) ;;  
   (cons #x1b #x75) ;;  
   (cons #x1c #x62) ;;  
   (cons #x1d #x75) ;;  
   (cons #x1e #x6e) ;; outsb %ds:(%rsi),(%dx) 
   (cons #x1f #x74) ;; je 96 <_init-0x4002fa> 
   (cons #x20 #x75) ;;  
   (cons #x21 #x35) ;; xor $0x2e342029,%eax 
   (cons #x22 #x29) ;;  
   (cons #x23 #x20) ;;  
   (cons #x24 #x34) ;;  
   (cons #x25 #x2e) ;;  
   (cons #x26 #x36) ;; ss xor %cs:%ss:(%rax),%eax 
   (cons #x27 #x2e) ;;  
   (cons #x28 #x33) ;;  
   (cons #x29 #x00) ;;  
))

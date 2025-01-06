; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2025, Yahya Sohail

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
; Yahya Sohail        <yahya@yahyasohail.com>

(in-package "X86ISA")

(include-book "oslib/argv" :dir :system)

(include-book "asmtest")
(include-book "../top" :ttags (:undef-flg :other-non-det :instrument))

(def-snippet-data real-snippet-data)

(init-x86-state-64
 nil
 0
 nil         ;; GPRs
 nil         ;; CRs
 nil         ;; MSRs
 nil         ;; SRs (visible)
 nil nil nil ;; (hidden)
 0           ;; rflags
 nil         ;;memory
 x86)

(!ctri *cr0* (change-cr0bits (ctri *cr0* x86)
                             :em 0
                             :mp 1) x86)

(!ctri *cr4* (change-cr4bits (ctri *cr4* x86)
                             :osfxsr 1
                             :osxmmexcpt 1) x86)

(binary-file-load "asmtest" :elf t)

(define run-test (x86 state)
  (b* (((mv argv state) (oslib::argv state))
       ((when (or (not (consp argv))
                  (not (stringp (car argv)))))
        (prog2$ (raise "error argv nil")
                (mv nil x86 state)))
       (name (car argv))
       (- (cw "~x0~%" name))
       ((mv res x86 state)
        (test-snippet name
                      :input-file (str::cat "inputs/" name ".in")
                      :output-file (str::cat "outputs/" name ".out")))
       (- (cw "~x0~%" res))
       (- (good-bye)))
      (mv res x86 state)))

:q
(save-exec "check-test" "MODIFIED" :init-forms '((x86isa::run-test x86isa::x86 state)))

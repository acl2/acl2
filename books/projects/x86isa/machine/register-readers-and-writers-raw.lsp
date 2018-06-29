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

(in-package "X86ISA")

;; ======================================================================

;; Undef Flg:

(defun undef-flg$notinline (x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
                   t)
            (equal (f-get-global
                    'in-verify-flg ACL2::*the-live-state*)
                   t))
    (return-from X86ISA::undef-flg$notinline
      (X86ISA::undef-flg-logic x86)))
  ;; TO-DO@Shilpi: For now, I'm just returning 0 as the "undefined"
  ;; value for flags.
  (mv 0 x86)
  ;; (b* ((- (cw "~%undef-flg at PC: ~x0~%" (X86ISA::rip X86ISA::*the-live-x86*))))
  ;;     (mv 0 x86))
  )

(defun undef-read$notinline (x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-read ACL2::*the-live-state*)
                   t)
            (equal (f-get-global
                    'in-verify-read ACL2::*the-live-state*)
                   t))
    (return-from X86ISA::undef-read$notinline
      (X86ISA::undef-read-logic x86)))
  ;; TO-DO@Shilpi: For now, I'm just returning 0 as the "undefined"
  ;; value.
  (mv 0 x86)
  ;; (b* ((- (cw "~%undef-read at PC: ~x0~%" (X86ISA::rip X86ISA::*the-live-x86*))))
  ;;     (mv 0 x86))
  )

;; Safe-!undef:

;; (defun safe-!undef$notinline (v x86)
;;   (declare (xargs :mode :program :stobjs x86))
;;   (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
;;                    t)
;;             (equal (f-get-global 'in-verify-flg
;;                                  ACL2::*the-live-state*)
;;                    t))
;;     (return-from X86ISA::safe-!undef$notinline
;;       (X86ISA::!undef v x86)))
;;   (er hard! 'safe-!undef
;;       "Ill-advised attempt to call safe-!undef during top-level ~
;;        evaluation."))

;; ======================================================================

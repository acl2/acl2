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

(include-book "syscalls"
              :ttags (:include-raw :undef-flg :syscall-exec))

;; ======================================================================

(defsection other-non-deterministic-computations
  :parents (machine)
  :short "Definitions of other non-deterministic computations"

  :long "<p>All the *-logic functions \(like @(see HW_RND_GEN-logic)
for the @('RDRAND') instruction\) should be untouchable --- we want to
disallow the use of these functions during evaluation as well as proof
since they aren't the top-level interface functions \(like @(see
HW_RND_GEN)\).</p>"

  )

(local (xdoc::set-default-parents other-non-deterministic-computations))

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

(define HW_RND_GEN-logic
  ((size :type (integer 2 8))
   x86)
  :guard (or (equal size 2)
             (equal size 4)
             (equal size 8))
  ;; Old implementation used the env field.
  ;; (pop-x86-oracle x86)
  (b* (((mv cf x86)
        (undef-flg x86))
       ((mv rand x86)
        (undef-read x86))
       (rand (loghead (ash size 3) rand)))
    (mv cf rand x86)))

(define HW_RND_GEN
  ((size :type (integer 2 8))
   x86)
  :inline nil
  :guard (or (equal size 2)
             (equal size 4)
             (equal size 8))
  (HW_RND_GEN-logic size x86))

;; ======================================================================

(push-untouchable (
                   HW_RND_GEN-logic
                   )
                  t)

;; Exec definitions:

(defsection other-non-deterministic-computations-exec
  :parents (other-non-deterministic-computations)
  :short "Definitions of non-deterministic computations to be used for
  execution"
  :long "<p>We smash the definition of @(see HW_RND_GEN) to provide
  random numbers during execution by using Lisp's @('random')
  function.</p>"

; Instruction to cert.pl for dependency tracking.
; (depends-on "other-non-det-raw.lsp")

  (defttag :other-non-det)
  (include-raw "other-non-det-raw.lsp"))

;; ======================================================================

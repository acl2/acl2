; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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
; Mertcan Temel         <mert@utexas.edu>

(include-book "top")
(include-book "misc/eval" :dir :system)

(encapsulate
  (((d2 *) => *) ((f2 *) => *) ((neg-m2 *) => *))
  (local (include-book "arithmetic-5/top" :dir :system))

  (local (defun d2 (x) (/ x 2)))
  (local (defun f2 (x) (floor x 2)))
  (local (defun neg-m2 (x) (- (mod x 2))))

  ;; syntaxp is necessary because rp-rewriter does not support "loop stoppers."
  (def-rp-rule +-comm
    (implies (syntaxp (and (not (lexorder y x))
                           (or (atom x)
                               (not (equal (car x) 'binary-+)))))
             (and (equal (+ y x) (+ x y))
                  (equal (+ y x z) (+ x y z)))))

  (def-rp-rule my+-assoc
    (equal (+ (+ a b) c) (+ a b c)))

  (progn
    ;; a lemma for rp-rewriter to maintain even-ness
    (def-rp-rule my+-assoc-for-evens
      (implies (and (evenp (+ a b)) (evenp c))
               (equal (+ (+ a b) c) (+ a b c))))

    (defthmd my+-assoc-for-evens-side-cond
      (implies (and (evenp (+ a b)) (evenp c))
               (evenp (+ a b c))))

    (rp-attach-sc my+-assoc-for-evens
                  my+-assoc-for-evens-side-cond))

  (def-rp-rule d2-is-f-2-when-even
    (implies (evenp x)
             (equal (d2 x) (f2 x))))

  ;; a function that rounds down a number to an even value
  ;; e.g., (round-to-even 93/10) = 8
  (progn
    (defun round-to-even (a)
      (+ a (neg-m2 a)))

    ;; add definition rule to rp-rewriter's rule-set
    (add-rp-rule round-to-even)

    ;; rhs of the definition rule
    (defthmd round-to-even-is-even
      (evenp (+ a (neg-m2 a))))

    (rp-attach-sc round-to-even
                  round-to-even-is-even)))

;; This should fail
;; could be proven with more lemmas
;; but not as flexible and as easy as below.
(acl2::must-fail
 (defthm three-round-to-evens
   (equal (d2 (+ (round-to-even a) (round-to-even b) (round-to-even c)))
          (f2 (+ (neg-m2 a) (neg-m2 b) (neg-m2 c) a b c)))))

(acl2::must-succeed
 (defthmrp three-round-to-evens-2 ;; use rp-rewriter as a clause-processor
   (equal (d2 (+ (round-to-even a) (round-to-even b) (round-to-even c)))
          (f2 (+ (neg-m2 a) (neg-m2 b) (neg-m2 c) a b c)))))

(acl2::must-succeed
 (defthmrp four-round-to-evens ;; use rp-rewriter as a clause-processor
   (equal (d2 (+ (round-to-even a) (round-to-even b)
                 (round-to-even c) (round-to-even d)))
          (f2 (+ (neg-m2 a) (neg-m2 b) (neg-m2 c) (neg-m2 d) a b c d)))))

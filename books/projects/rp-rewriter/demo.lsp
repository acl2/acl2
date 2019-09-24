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
  nil
  (local
   (include-book "arithmetic-5/top" :dir :system))

  (encapsulate
    nil
    ;; my+ is the same as + but with fewer rules
    ;; Define my+ and basic rules:
    (defun my-binary-+ (a b)
      (binary-+ a b))

    (defmacro my+ (&rest rest)
      (if rest
          (if (cdr rest)
              (xxxjoin 'my-binary-+ rest)
            (cons 'my-binary-+
                  (cons 0 (cons (car rest) nil))))
        0))

    (add-macro-fn my+ my-binary-+ t)

    ;; syntaxp is necessary because rp-rewriter does not support "loop stoppers."
    (defthm my+-comm-1
      (implies (syntaxp (not (lexorder y x)))
               (equal (my+ y x)
                      (my+ x y))))

    (defthm my+-comm-2
      (implies (syntaxp (not (lexorder y x)))
               (equal (my+ y (my+ x z))
                      (my+ x (my+ y z)))))

    (defthm my+-reorder
      (equal (my+ (my+ a b) c)
             (my+ a b c))))

  (progn
    (defun /2 (x)
      (/ x 2))

    (defun floor-2 (x)
      (floor x 2))

    (defun --mod-2 (x)
      (- (mod x 2))))

  (defthm /2-is-floor-2-when-even
    (implies (evenp x)
             (equal (/2 x)
                    (floor-2 x))))

  (local
   (defthm sum-of-two-evens-is-even
     (implies (and (evenp a)
                   (evenp b))
              (evenp (my+ a b)))))

  ;; a function that rounds down a number to an even value
  ;; e.g., (round-to-even 93/10) = 8
  (defun round-to-even (a)
    (my+ a (--mod-2 a)))

  (defthmd round-to-even-is-even
    (evenp (my+ a (--mod-2 a))))

  (rp-attach-sc round-to-even
                round-to-even-is-even)

  ;; a lemma for rp-rewriter to maintain even-ness
  (defthm my+-reorder-for-evens
    (implies (and (evenp (my+ a b))
                  (evenp c))
             (equal (my+ (my+ a b) c)
                    (my+ a b c))))

  (defthmd my+-reorder-for-evens-side-cond
    (implies (and (evenp (my+ a b))
                  (evenp c))
             (evenp (my+ a b c))))

  (rp-attach-sc my+-reorder-for-evens
                my+-reorder-for-evens-side-cond))

;; enabling only the useful functions gives a speed up.
;; (in-theory '((:REWRITE /2-IS-FLOOR-2-WHEN-EVEN)
;;              (:REWRITE MY+-COMM-1)
;;              (:REWRITE MY+-COMM-2)
;;              (:REWRITE MY+-REORDER-FOR-EVENS)
;;              (:definition round-to-even)))

;; This should fail
;; could be proven with more lemmas
;; but not as flexible and as easy as below.
(acl2::must-fail
 (defthm example3
   (equal (/2 (my+ (round-to-even a)
                   (round-to-even b)
                   (round-to-even c)))
          (floor-2 (my+ (--mod-2 a)
                        (--mod-2 b)
                        (--mod-2 c)
                        a b c)))
   :hints (("Goal"
            :in-theory (e/d () ())))))


;; we disable these functions because rp-rewriter is  too eager to open
;; definitions.
(in-theory (disable --mod-2
                    my-binary-+
                    floor
                    mod
                    evenp
                    floor-2
                    /2))

(acl2::must-succeed
 (defthmrp example3-l1
   (equal (/2 (my+ (round-to-even a)
                   (round-to-even b)
                   (round-to-even c)))
          (floor-2 (my+ (--mod-2 a)
                        (--mod-2 b)
                        (--mod-2 c)
                        a b c)))))

(acl2::must-succeed
 (defthmrp example3-l2
   (equal (/2 (my+ (round-to-even a)
                   (round-to-even b)
                   (round-to-even c)
                   (round-to-even d)))
          (floor-2 (my+ (--mod-2 a)
                        (--mod-2 b)
                        (--mod-2 c)
                        (--mod-2 d)
                        a b c d)))))

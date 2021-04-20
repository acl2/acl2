; Copyright (C) 2020 David S. Hardin
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

;; "Staging" book between the automatically-generated leg64 book and Codewalker.

(IN-PACKAGE "RTL")

(include-book "leg64")

(include-book "rtl/rel11/lib/bits" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

;; Unfortunately, conflicts exist between arithmetic-5 and RTL that can
;; severely slow down some proofs.  Much of this can be avoided by
;; disabling the following lemmas:

(in-theory
 #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)|
                |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)| mod-cancel-*-const
	        cancel-mod-+ reduce-additive-constant-< ash-to-floor |(floor x 2)|
                |(equal x (if a b c))| |(equal (if a b c) x)| |(logior 1 x)|
                mod-theorem-one-b |(mod (- x) y)|))

(DEFTHM BITS-UPPER-BOUND-LE
 (IMPLIES (AND (INTEGERP I) (INTEGERP J) (<= 0 I) (>= I J))
          (<= (BITS X I J) (1- (EXPT 2 (1+ (- I J))))))
 :INSTRUCTIONS
 (:PROMOTE (:CLAIM (INTEGERP (EXPT 2 (1+ (- I J)))))
           (:CLAIM (< (BITS X I J) (EXPT 2 (1+ (- I J))))
                   :HINTS (("Goal" :USE (:INSTANCE BITS-UPPER-BOUND))))
           :BASH)
  :rule-classes ((:forward-chaining :trigger-terms ((BITS X I J))) :rewrite))

(DEFTHM BITS-ELIM--THM
  (IMPLIES
   (AND
    (INTEGERP X)
    (INTEGERP I)
    (<= 0 I)
    (<= 0 X)
    (< X (EXPT 2 (1+ I))))
   (EQUAL (BITS X I 0) X))
  :hints (("Goal" :in-theory (e/d (bits-mod) ()))))


;; Codewalker requires the 'state' parameter to be the first parameter; for the
;; rac-generated steps primitive (leg64steps-loop-0) called by leg64steps, the
;; state parameter is the last parameter.  Thus, we rewrite leg64steps-loop-0
;; slightly, and call the result leg64stepn.

(DEFUN LEG64STEPN (S N)
 (DECLARE (XARGS :MEASURE (NFIX N)))
       (IF (AND (INTEGERP N) (> N 0))
           (LET ((S (LEG64STEP S)))
                (LEG64STEPN S (- N 1)))
           S))

;; Justification for leg64stepsn

(defthmd leg64stepn-eq-leg64steps-aux--thm
  (= (leg64stepn s i) (leg64steps-loop-0 i n s))
  :hints (("Goal" :in-theory (e/d (leg64steps-loop-0) (leg64step)))))

(DEFTHMD LEG64STEPN-EQ-LEGSTEPS--THM
   (= (LEG64STEPN S N) (LEG64STEPS S N))
   :INSTRUCTIONS
   ((:DIVE 2)
    (:REWRITE LEG64STEPS)
    :TOP
    (:PROVE
         :HINTS (("Goal" :USE (:INSTANCE LEG64STEPN-EQ-LEG64STEPS-AUX--THM
                                         (I N)))))))


(defthm leg64stepn-plus--thm
  (implies (and (integerp c1) (<= 0 c1)
                (integerp c2) (<= 0 c2))
           (= (leg64stepn s (+ c1 c2))
              (leg64stepn (leg64stepn s c1) c2)))
  :hints (("Goal" :in-theory (disable leg64step))))

(in-theory (enable bits-bits-prod))

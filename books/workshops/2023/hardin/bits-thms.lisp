;; Copyright (C) 2023-2024 David S. Hardin
;;
;; License: (An MIT/X11-style license)
;;
;;   Permission is hereby granted, free of charge, to any person obtaining a
;;   copy of this software and associated documentation files (the "Software"),
;;   to deal in the Software without restriction, including without limitation
;;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;   and/or sell copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following conditions:
;;
;;   The above copyright notice and this permission notice shall be included in
;;   all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;   DEALINGS IN THE SOFTWARE.

(in-package "RTL")

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

;; In RAC distribution now
;; (DEFTHM BITS-UPPER-BOUND
;;   (IMPLIES (AND (INTEGERP I) (INTEGERP J))
;;            (< (BITS X I J) (EXPT 2 (1+ (- I J)))))
;;   :INSTRUCTIONS
;;   (:PROMOTE
;;    (:CLAIM (AND (NATP (BITS X I J))
;;                 (< (BITS X I J) (EXPT 2 (1+ (- I J)))))
;;            :HINTS (("Goal" :USE (:INSTANCE BITS-BOUNDS))))
;;    :BASH))

(DEFTHM BITS-UPPER-BOUND-LE
  (IMPLIES
   (AND (INTEGERP I)
        (<= 0 I)
        (INTEGERP J)
        (>= I J))
   (<= (BITS X I j) (1- (EXPT 2 (1+ (- I J))))))
 :INSTRUCTIONS
 (:PROMOTE (:CLAIM (INTEGERP (EXPT 2 (1+ (- I J)))))
           (:CLAIM (< (BITS X I J) (EXPT 2 (1+ (- I J))))
                   :HINTS (("Goal" :USE (:INSTANCE BITS-UPPER-BOUND))))
           :BASH)
  :rule-classes ((:forward-chaining :trigger-terms ((BITS X I J))) :rewrite))

(DEFTHM BITS-ELIM--THM
  (IMPLIES
   (AND (INTEGERP I)
        (<= 0 I)
        ;; (INTEGERP J)
        (< 0 J)
        (< I (EXPT 2 (1+ J))))
   (EQUAL (BITS I J 0) I))
  :INSTRUCTIONS
  (:PROMOTE
   (:DV 1)
   (:REWRITE BITS)
   (:= (FL (* (MOD I (EXPT 2 (+ 1 J)))
              (/ (EXPT 2 0)))))
   (:DV 1 2)
   (:= 1)
   :UP
   (:CLAIM (INTEGERP (MOD I (EXPT 2 (+ 1 J)))))
   (:REWRITE ACL2::|arith (* x 1)|)
   :UP (:REWRITE FL)
   (:REWRITE ACL2::|(floor x 1)|)
   (:REWRITE (:REWRITE ACL2::MOD-X-Y-=-X . 3))
   :TOP :BASH))

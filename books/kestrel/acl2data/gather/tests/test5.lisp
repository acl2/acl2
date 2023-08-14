; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we test the :symbol-table field.

(in-package "ACL2")

(include-book "arithmetic/top-with-meta" :dir :system)

(local
 (defthm  my-inverse-of-*
; Just repeat inverse-of-*, to get a lemma in this book.  Make it local, just
; for kicks.
   (implies (and (acl2-numberp x) (not (equal x 0)))
            (equal (* x (/ x)) 1))))

(defmacro deffact (&rest args)
  `(defthm ,@args
     :rule-classes nil))

(deffact thm1
; Check rules in symbol-table.
  (member (* x y (/ x) (/ y))
          '(0 1)))

(include-book "arithmetic/binomial" :dir :system)

(deffact thm2
; Check theorem symbols in symbol-table and :by hints.
  (implies (and (integerp n) (<= 0 n))
 	   (equal (expt x n)
 		  (n-expt x n)))
  :hints (("Goal" :by n-expt-expt)))

(deffact thm3
; Variant of thm2 that uses rewriting and has more than one symbol in theorem
; from book.
  (implies (and (integerp n) (<= 0 n))
 	   (equal (+ (expt x n) (choose k n))
                  (+ (n-expt x n) (choose k n)))))

(deffact thm4
; Test :in-theory and :use hints, and avoidance of duplicates.
  (implies (and (natp n) (natp k))
 	   (and (equal (expt x n)
                       (n-expt x n))
                (equal (expt y k)
                       (n-expt y k))))
  :hints (("Goal" :use (n-expt-expt
                        (:instance n-expt-expt (x y) (n k)))
           :in-theory (e/d (append) (n-expt-expt)))))

(deffact thm5
; As above, but with atom for :use hint, and with a rune disabled.
  (implies (natp n)
 	   (equal (expt x n)
                  (n-expt x n)))
  :hints (("Goal" :use n-expt-expt
           :in-theory (disable (:rewrite n-expt-expt) append))))

(defun f1 (x) x)

(deffact thm6
; Test other hints and also symbol defined in this book.
  (implies (natp n)
 	   (equal (expt x n)
                  (n-expt x n)))
  :hints (("Goal"
           :restrict ((Associativity-of-+ ((i 3))))
           :hands-off (nth f1)
           :cases ((equal (choose k n) 17)))))

(include-book "clause-processors/autohide" :dir :system)

(deffact thm7
; Test :clause-processor hint and long form of :expand hint.
  (implies (natp n)
 	   (equal (expt x n)
                  (n-expt x n)))
  :hints (("Goal"
           :clause-processor (:function autohide-cp :hint '(nth))
           :expand ((append u v)))))

(deffact thm8
; Test :cases and short form of :expand hint, as well as a hint that's ingored
; for the :symbol-table (:do-not).
  (implies (natp n)
 	   (equal (expt x n)
                  (n-expt x n)))
  :hints (("Goal"
           :cases ((< 5 (choose i j)))
           :expand (append u v)
           :do-not '(generalize fertilize))))

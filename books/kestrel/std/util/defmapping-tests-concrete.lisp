; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping")

(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete (i.e. non-template-based) tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions (move):

; show an easily searchable title of a test:

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Identity isomorphisms over all values.")

(must-succeed
 (defmapping all-id any-p any-p identity identity
   :beta-of-alpha-thm t :alpha-of-beta-thm t))

(must-succeed
 (defmapping all-id any-p any-p identity identity
   :beta-of-alpha-thm t :alpha-of-beta-thm t :unconditional t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Identity isomorphisms over natural numbers.")

(must-succeed
 (defmapping nat-id natp natp identity identity
   :beta-of-alpha-thm t :alpha-of-beta-thm t))

(must-succeed
 (defmapping nat-id natp natp identity identity
   :beta-of-alpha-thm t :alpha-of-beta-thm t :unconditional t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphisms between naturals and integers.")

(must-succeed*

 (defun nat-to-int (n)
   (declare (xargs :guard (natp n)))
   (if (evenp n)
       (/ n 2)
     (- (/ (1+ n) 2))))

 (defun int-to-nat (i)
   (declare (xargs :guard (integerp i)))
   (if (>= i 0)
       (* 2 i)
     (1- (- (* 2 i)))))

 (local (include-book "arithmetic-5/top" :dir :system))

 (defmapping nat-int natp integerp nat-to-int int-to-nat
   :beta-of-alpha-thm t :alpha-of-beta-thm t)

 (defmapping int-nat integerp natp int-to-nat nat-to-int
   :beta-of-alpha-thm t :alpha-of-beta-thm t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphisms between {0, ..., 9} and {9, ..., 0}.")

(must-succeed*

 (defun swap-range (x)
   (declare (xargs :guard (integer-range-p 0 10 x)))
   (- 9 x))

 (defmapping zeronine
   (lambda (x) (integer-range-p 0 10 x))
   (lambda (x) (integer-range-p 0 10 x))
   swap-range
   swap-range
   :beta-of-alpha-thm t
   :alpha-of-beta-thm t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphisms between (MV X Y) and (MV Y X).")

(must-succeed*

 (defun swap-pair (x y)
   (declare (xargs :guard t))
   (mv y x))

 (defmapping swap-pair
   (lambda (x y) t)
   (lambda (x y) t)
   swap-pair
   swap-pair
   :beta-of-alpha-thm t
   :alpha-of-beta-thm t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Isomorphism between (MV X Y Z) and (MV (CONS X Y) Z).")

(must-succeed*

 (defun groupedp (xy z)
   (declare (xargs :guard t))
   (declare (ignore z))
   (consp xy))

 (defun group (x y z)
   (declare (xargs :guard t))
   (mv (cons x y) z))

 (defun ungroup (xy z)
   (declare (xargs :guard (consp xy)))
   (mv (car xy) (cdr xy) z))

 (defmapping grouping
   (lambda (x y z) t)
   groupedp
   group
   ungroup
   :beta-of-alpha-thm t
   :alpha-of-beta-thm t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Identity isomorphisms over pairs in an unspecified domain.")

(must-succeed*

 (defstub dom2 (* *) => *)

 (defmapping id-pair
   dom2
   dom2
   (lambda (x y) (mv x y))
   (lambda (x y) (mv x y))
   :beta-of-alpha-thm t
   :alpha-of-beta-thm t))

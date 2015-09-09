; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

;Rewrites an equality of two "predicates" to, essentially, an iff.  This can save you from having to do two
;proofs, one for each of the forward and back directions.

;Feel free to add more predicates to this list as time goes on.
(defun predicatep (term)
  (and (consp term) ;drop this test?
       (member (car term) '(< integerp power2p complex-rationalp rationalp bvecp))))

;This can cause case-splits, but that's sort of the point.
;We could actually rewrite to iff instead of the and of the implies...
(defthm equal-of-preds-rewrite
  (implies (and (syntaxp (and (predicatep a)
                              (predicatep b)))
                (case-split (booleanp a)) ;or force?
                (case-split (booleanp b)) ;or force?
                )
           (equal (equal a b)
                  (and (implies a b)
                       (implies b a)))))





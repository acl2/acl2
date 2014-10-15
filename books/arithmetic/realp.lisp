(in-package "ACL2")

; Contributed by Ruben Gamboa
; Copyright (C) 2014, University of Wyoming
; All rights reserved.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;; Surprisingly, ACL2 knows very little about the rational numbers.
;;; Even though its type system knows that x*y is rational when x and
;;; y are rational, it gets confused when a theorem has that as a
;;; hypothesis, because the crucial fact is needed by the rewriter,
;;; not the type-system.  Sad, really.

;;; The arithmetic books solve this problem for the rationals.  The
;;; same problems apply to ACL2(r) with the reals, so we include those
;;; simple theorems here.

#+non-standard-analysis
; [Jared] adding #+non-standard-analysis so that we can include this book in
; ordinary ACL2, and hence keep the include-book commands uniform across both
; ACL2 and ACL2(r).
(progn

(defthm realp-+
  (implies (and (realp x) (realp y))
	   (realp (+ x y))))

(defthm realp-uminus
  (implies (realp x)
	   (realp (- x))))

(defthm realp-*
  (implies (and (realp x) (realp y))
	   (realp (* x y))))

(defthm realp-udiv
  (implies (realp x)
	   (realp (/ x))))

)

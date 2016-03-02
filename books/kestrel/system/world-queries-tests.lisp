; World Queries -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the world query utilities in world-query.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world-queries")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (theorem-symbolp 'car-cdr-elim (w state)))

(assert-event (not (theorem-symbolp 'cons (w state))))

(assert-event (not (theorem-symbolp 'aaaaaaaaa (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert-event (theorem-symbolp 'th (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (function-namep 'len (w state)))

(assert-event (not (function-namep 'cons-car-cdr (w state))))

(assert-event (not (function-namep 'bbbbbbbbbbb (w state))))

(must-succeed*
 (defun f (x) x)
 (assert-event (function-namep 'f (w state))))

(assert-event (not (function-namep 33 (w state))))

(assert-event (not (function-namep "len" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (theorem-namep 'car-cdr-elim (w state)))

(assert-event (not (theorem-namep 'cons (w state))))

(assert-event (not (theorem-namep 'aaaaaaaaa (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert-event (theorem-namep 'th (w state))))

(assert-event (not (theorem-namep 8 (w state))))

(assert-event (not (theorem-namep "car-cdr-elim" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (definedp 'not (w state)))

(assert-event (not (definedp 'cons (w state))))

(must-succeed*
 (defun f (x) x)
 (assert-event (definedp 'f (w state))))

(must-succeed*
 (defstub f (*) => *)
 (assert-event (not (definedp 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm th (equal (f x) x)))
 (assert-event (not (definedp 'f (w state)))))

(must-succeed*
 (defchoose f x (y) (equal x y))
 (assert-event (not (definedp 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (guard-verifiedp 'len (w state)))

(assert-event (guard-verifiedp 'cons (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards t)) x)
 (assert-event (guard-verifiedp 'f (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-event (not (guard-verifiedp 'f (w state)))))

(must-succeed*
 (defthm th (acl2-numberp (+ (fix x) (fix y))))
 (verify-guards th)
 (assert-event (guard-verifiedp 'th (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert-event (not (guard-verifiedp 'th (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (eq (non-executablep 'not (w state)) nil))

(assert-event (eq (non-executablep 'len (w state)) nil))

(must-succeed*
 (defun-nx f (x) x)
 (assert-event (eq (non-executablep 'f (w state)) t)))

(must-succeed*
 (defun-sk g (x) (forall (y z) (equal x (cons y z))))
 (assert-event (eq (non-executablep 'g (w state)) t)))

(must-succeed*
 (defun-sk h (x y) (exists z (equal z (cons x y)))
   :witness-dcls ((declare (xargs :non-executable nil))))
 (assert-event (eq (non-executablep 'h (w state)) nil)))

(must-succeed*
 (defproxy p (* *) => *)
 (assert-event (eq (non-executablep 'p (w state)) :program)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (measure 'len (w state)) '(acl2-count x)))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-event (equal (measure 'f (w state))
                      '(nfix (binary-+ '10 (unary-- x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (well-founded-relation 'len (w state)) 'o<))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-event (equal (well-founded-relation 'f (w state)) 'o<)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert-event (fundef-enabledp 'f state)))

(must-succeed*
 (defund f (x) x)
 (assert-event (not (fundef-enabledp 'f state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (rune-enabledp '(:rewrite cons-car-cdr) state))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert-event (rune-enabledp '(:rewrite th) state)))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)))
 (assert-event (not (rune-enabledp '(:rewrite th) state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)) :rule-classes :type-prescription)
 (assert-event (rune-enabledp '(:type-prescription th) state)))

(must-succeed*
 (defthm th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert-event (rune-enabledp '(:rewrite th . 1) state))
 (assert-event (rune-enabledp '(:rewrite th . 2) state)))

(must-succeed*
 (defthmd th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert-event (not (rune-enabledp '(:rewrite th . 1) state)))
 (assert-event (not (rune-enabledp '(:rewrite th . 2) state))))

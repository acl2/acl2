; Tests for the lightweight world utilities
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "top")

;; primitive
(assert-event (function-symbolp 'binary-+ (w state)))
(assert-event (fn-logicp 'binary-+ (w state)))
(assert-event (not (fn-programp 'binary-+ (w state))))
(assert-event (not (fn-definedp 'binary-+ (w state))))
(assert-event (fn-primitivep 'binary-+ (w state)))
(assert-event (not (defined-functionp 'binary-+ (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'binary-+ (w state))))

;; primitive (cons, sometimes gets special treatment)
(assert-event (function-symbolp 'cons (w state)))
(assert-event (fn-logicp 'cons (w state)))
(assert-event (not (fn-programp 'cons (w state))))
(assert-event (not (fn-definedp 'cons (w state))))
(assert-event (fn-primitivep 'cons (w state)))
(assert-event (not (defined-functionp 'cons (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'cons (w state))))

;; primitive (if, sometimes gets special treatment)
(assert-event (function-symbolp 'if (w state)))
(assert-event (fn-logicp 'if (w state)))
(assert-event (not (fn-programp 'if (w state))))
(assert-event (not (fn-definedp 'if (w state))))
(assert-event (fn-primitivep 'if (w state)))
(assert-event (not (defined-functionp 'if (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'if (w state))))

;; primitive (equal, sometimes gets special treatment)
(assert-event (function-symbolp 'equal (w state)))
(assert-event (fn-logicp 'equal (w state)))
(assert-event (not (fn-programp 'equal (w state))))
(assert-event (not (fn-definedp 'equal (w state))))
(assert-event (fn-primitivep 'equal (w state)))
(assert-event (not (defined-functionp 'equal (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'equal (w state))))

;; built-in, :logic mode
(assert-event (function-symbolp 'natp (w state)))
(assert-event (fn-logicp 'natp (w state)))
(assert-event (not (fn-programp 'natp (w state))))
(assert-event (fn-definedp 'natp (w state)))
(assert-event (not (fn-primitivep 'natp (w state))))
(assert-event (defined-functionp 'natp (w state)))
(assert-event (not (defthm-or-defaxiom-symbolp 'natp (w state)))) ; even though there is a definitional axiom

;; built-in, :program mode
(assert-event (function-symbolp 'rewrite (w state)))
(assert-event (not (fn-logicp 'rewrite (w state))))
(assert-event (fn-programp 'rewrite (w state)))
(assert-event (fn-definedp 'rewrite (w state)))
(assert-event (not (fn-primitivep 'rewrite (w state))))
(assert-event (defined-functionp 'rewrite (w state)))
(assert-event (not (defthm-or-defaxiom-symbolp 'rewrite (w state))))

;; not built-in, :logic mode
(defun foo (x) x)
(assert-event (function-symbolp 'foo (w state)))
(assert-event (fn-logicp 'foo (w state)))
(assert-event (not (fn-programp 'foo (w state))))
(assert-event (fn-definedp 'foo (w state)))
(assert-event (not (fn-primitivep 'foo (w state))))
(assert-event (defined-functionp 'foo (w state)))
(assert-event (not (defthm-or-defaxiom-symbolp 'foo (w state))))

;; not built-in, :program mode
(defun bar (x) (declare (xargs :mode :program)) x)
(assert-event (function-symbolp 'bar (w state)))
(assert-event (not (fn-logicp 'bar (w state))))
(assert-event (fn-programp 'bar (w state)))
(assert-event (fn-definedp 'bar (w state)))
(assert-event (not (fn-primitivep 'bar (w state))))
(assert-event (defined-functionp 'bar (w state)))
(assert-event (not (defthm-or-defaxiom-symbolp 'bar (w state))))

;; not defined
(defstub stub (x) t)
(assert-event (function-symbolp 'stub (w state)))
(assert-event (fn-logicp 'stub (w state)))
(assert-event (not (fn-programp 'stub (w state))))
(assert-event (not (fn-definedp 'stub (w state))))
(assert-event (not (fn-primitivep 'stub (w state))))
(assert-event (not (defined-functionp 'stub (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'stub (w state))))

;; TODO: Is there a way to obtain a :program mode function with no body?

;; a constrained function introduced in an encapsulate
(encapsulate (((gt3 *) => *)) (local (defun gt3 (x) (< 3 x))) (defthm gt3-constraint (implies (gt3 x) (< 2 x))))
(assert-event (function-symbolp 'gt3 (w state)))
(assert-event (fn-logicp 'gt3 (w state)))
(assert-event (not (fn-programp 'gt3 (w state))))
(assert-event (not (fn-definedp 'gt3 (w state))))
(assert-event (not (fn-primitivep 'gt3 (w state))))
(assert-event (not (defined-functionp 'gt3 (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'gt3 (w state))))

;; a defchoose
(defchoose greater-number (x) (y) (> x y))
(assert-event (function-symbolp 'greater-number (w state)))
(assert-event (fn-logicp 'greater-number (w state)))
(assert-event (not (fn-programp 'greater-number (w state))))
(assert-event (not (fn-definedp 'greater-number (w state))))
(assert-event (not (fn-primitivep 'greater-number (w state))))
(assert-event (not (defined-functionp 'greater-number (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'greater-number (w state))))

;; a defun-sk
(defun-sk exists-greater (y) (exists x (< y x)))
(assert-event (function-symbolp 'exists-greater (w state)))
(assert-event (fn-logicp 'exists-greater (w state)))
(assert-event (not (fn-programp 'exists-greater (w state))))
(assert-event (fn-definedp 'exists-greater (w state))) ; actually is defined
(assert-event (not (fn-primitivep 'exists-greater (w state))))
(assert-event (defined-functionp 'exists-greater (w state))) ; actually is defined
(assert-event (not (defthm-or-defaxiom-symbolp 'exists-greater (w state))))
;; Also check the witness:
(assert-event (function-symbolp 'exists-greater-witness (w state)))
(assert-event (fn-logicp 'exists-greater-witness (w state)))
(assert-event (not (fn-programp 'exists-greater-witness (w state))))
(assert-event (not (fn-definedp 'exists-greater-witness (w state)))) ; witness is not defined
(assert-event (not (fn-primitivep 'exists-greater-witness (w state))))
(assert-event (not (defined-functionp 'exists-greater-witness (w state)))) ; witness is not defined
(assert-event (not (defthm-or-defaxiom-symbolp 'exists-greater-witness (w state))))

;; a defun-nx (still defined, just not executable)
(defun-nx foo-nx (x y) (< x y))
(assert-event (function-symbolp 'foo-nx (w state)))
(assert-event (fn-logicp 'foo-nx (w state)))
(assert-event (not (fn-programp 'foo-nx (w state))))
(assert-event (fn-definedp 'foo-nx (w state)))
(assert-event (not (fn-primitivep 'foo-nx (w state))))
(assert-event (defined-functionp 'foo-nx (w state)))
(assert-event (not (defthm-or-defaxiom-symbolp 'foo-nx (w state))))

;; An axiom that is a rule
(assert-event (not (function-symbolp 'car-cons (w state))))
(assert-event (not (defined-functionp 'car-cons (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'car-cons (w state)))

;; An axiom in :rule-classes nil
(assert-event (not (function-symbolp 'completion-of-symbol-name (w state))))
(assert-event (not (defined-functionp 'completion-of-symbol-name (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'completion-of-symbol-name (w state)))

;; A built-in :rewrite rule
(assert-event (not (function-symbolp 'default-pkg-imports (w state))))
(assert-event (not (defined-functionp 'default-pkg-imports (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'default-pkg-imports (w state)))

;; A built-in :type-prescription rule
(assert-event (not (function-symbolp 'true-listp-explode-atom (w state))))
(assert-event (not (defined-functionp 'true-listp-explode-atom (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'true-listp-explode-atom (w state)))

;; A built-in defthm in rule-classes nil
(assert-event (not (function-symbolp 'symbol-equality (w state))))
(assert-event (not (defined-functionp 'symbol-equality (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'symbol-equality (w state)))

;; A non-built-in defthm
(defthm my-car-cons (equal (car (cons x y)) x))
(assert-event (not (function-symbolp 'my-car-cons (w state))))
(assert-event (not (defined-functionp 'my-car-cons (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'my-car-cons (w state)))

;; A non-built-in defthm in :rule-classes nil
(defthm my-car-cons2 (equal (car (cons x y)) x) :rule-classes nil)
(assert-event (not (function-symbolp 'my-car-cons2 (w state))))
(assert-event (not (defined-functionp 'my-car-cons2 (w state))))
(assert-event (defthm-or-defaxiom-symbolp 'my-car-cons2 (w state)))

;; A label
(deflabel mylabel)
(assert-event (not (function-symbolp 'mylabel (w state))))
(assert-event (not (defined-functionp 'mylabel (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'mylabel (w state))))

;; A built-in macro
(assert-event (not (function-symbolp 'append (w state))))
(assert-event (not (defined-functionp 'append (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'defined-functionp (w state))))

;; A non-built-in macro
(defmacro mymac (x) `(+ ,x 1))
(assert-event (not (function-symbolp 'mymac (w state))))
(assert-event (not (defined-functionp 'mymac (w state))))
(assert-event (not (defthm-or-defaxiom-symbolp 'mymac (w state))))

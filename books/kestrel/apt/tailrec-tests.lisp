; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tailrec")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

(defmacro tailrec (&rest args)
  `(apt::tailrec ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test error checking on the OLD input.")

 ;; not a symbol:
 (must-fail (tailrec 78))

 ;; not existing:
 (must-fail (tailrec fffffffff))

 ;; not a function:
 (must-fail (tailrec car-cdr-elim))

 ;; not resolving to a function:
 (must-fail (tailrec gggggg{*}))

 ;; in program mode:
 (must-succeed*
  (defun f (x) (declare (xargs :mode :program)) x)
  (must-fail (tailrec f)))

 ;; resolving to a function in program mode:
 (must-succeed*
  (defun f{1} (x) (declare (xargs :mode :program)) x)
  (add-numbered-name-in-use f{1})
  (must-fail (tailrec f{*})))

 ;; not defined:
 (must-fail (tailrec cons))

 ;; multiple results:
 (must-succeed*
  (defun f (x) (mv x x))
  (must-fail (tailrec f)))

 ;; stobjs:
 (must-succeed*
  (defun f (state) (declare (xargs :stobjs state)) state)
  (must-fail (tailrec f)))

 ;; not recursive:
 (must-fail (tailrec atom))

 ;; mutually recursive:
 (must-fail (tailrec pseudo-termp))

 ;; unknown measure:
 (must-succeed*
  (encapsulate
    ()
    (local (defun m (x) (acl2-count x)))
    (local (defun f (x)
             (declare (xargs :measure (m x)))
             (if (atom x) nil (f (car x)))))
    (defun f (x)
      (declare (xargs :measure (:? x)))
      (if (atom x) nil (f (car x)))))
  (must-fail (tailrec f)))

 ;; body is not (IF ...):
 (must-succeed*
  (defun f (x)
    (declare (xargs :ruler-extenders :all))
    (cons 1 (if (consp x) (f (cdr x)) nil)))
  (must-fail (tailrec f)))

 ;; exit test calls function:
 (must-succeed*
  (defun f (x)
    (declare (xargs :measure (acl2-count x) :ruler-extenders :all))
    (if (and (consp x) (f (cdr x)))
        (f (cdr x))
      nil))
  (must-fail (tailrec f)))

 ;; first branch calls function:
 (must-succeed*
  (defun f (x) (if (consp x) (f (cdr x)) nil))
  (must-fail (tailrec f)))

 ;; first branch is not ground and variant is :MONOID or :MONOID-ALT:
 (must-succeed*
  (defun f (x) (if (atom x) (list x) (f (cdr x))))
  (must-fail (tailrec f :variant :monoid))
  (must-fail (tailrec f :variant :monoid-alt)))

 ;; recursive branch contains different calls to function:
 (must-succeed*
  (defun fib (x) ; Fibonacci
    (declare (xargs :guard (natp x)))
    (if (or (zp x) (equal x 1))
        1
      (+ (fib (- x 1))
         (fib (- x 2)))))
  (must-fail (tailrec fib)))

 ;; function is already tail-recursive:
 (must-succeed*
  (defun f (x) (if (atom x) nil (f (cdr x))))
  (must-fail (tailrec f)))

 ;; recursive branch is (IF ...):
 (must-succeed*
  (defun f (x) (if (atom x) nil (if (atom (car x)) nil (f (cdr x)))))
  (must-fail (tailrec f)))

 ;; recursive branch is (IF ...) via AND macro:
 (must-succeed*
  (defun f (x) (if (atom x) nil (and (atom (car x)) (f (cdr x)))))
  (must-fail (tailrec f)))

 ;; recursive branch cannot be decomposed:
 (must-succeed*
  (defun f (x y) (if (atom x) nil (list x y (f (cdr x) y))))
  (must-fail (tailrec f)))

 ;; not guard-verified (and VERIFY-GUARDS is T):
 (must-succeed*
  (defun f (x)
    (declare (xargs :verify-guards nil))
    (if (atom x) nil (list (f (car x)))))
  (must-fail (tailrec f :verify-guards t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test successful applications with default options.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; with guard verification:
 (must-succeed*
  (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))
  (tailrec f)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x) (f{1} x nil))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x)))))

 ;; without guard verification:
 (must-succeed*
  (defun f (x)
    (declare (xargs :verify-guards nil))
    (if (atom x) nil (lub (car x) (f (cdr x)))))
  (tailrec f)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x) :verify-guards nil))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x)
     (declare (xargs :verify-guards nil))
     (f{1} x nil))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :VARIANT option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not :MONOID, :MONOID-ALT, or :ASSOC:
 (must-fail (tailrec f :variant "monoid"))

 ;; default:
 (must-succeed*
  (tailrec f)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x) (f{1} x nil))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x)))))

 ;; monoidal:
 (must-succeed*
  (tailrec f :variant :monoid)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x) (f{1} x nil))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x)))))

 ;; alternative monoidal:
 (must-succeed*
  (tailrec f :variant :monoid-alt)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x) (f{1} x nil))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x)))))

 ;; associative:
 (must-succeed*
  (tailrec f :variant :assoc)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) (lub r nil) (f{1} (cdr x) (lub r (car x)))))
   (defun f{1}-wrapper (x) (and (not (atom x)) (f{1} (cdr x) (car x))))
   (defthm f-~>-f{1}-wrapper (equal (f x) (f{1}-wrapper x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :DOMAIN option.")

 ;; error checking:
 (must-succeed*

  ;; least upper bound in lattice consisting of NIL as bottom, T as top,
  ;; and all the other values between NIL and T and incomparable to each other:
  (defun lub (x y)
    (cond ((null x) y)
          ((null y) x)
          ((equal x y) x)
          (t t)))

  ;; target function:
  (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

  ;; not :AUTO, a function, macro, or lambda:
  (must-fail (tailrec f :domain 44))
  (must-fail (tailrec f :domain car-cdr-elim))
  (must-fail (tailrec f :domain (natp x)))

  ;; not in logic mode:
  (must-succeed*
   (defun p (x) (declare (xargs :mode :program)) (consp x))
   (must-fail (tailrec f :domain p))
   (must-fail (tailrec f :domain (lambda (z) (or (p z) (acl2-numberp z))))))

  ;; not unary:
  (must-succeed*
   (defun p (a b) (equal a b))
   (must-fail (tailrec f :domain p)))
  (must-fail (tailrec f :domain (lambda (a b) (not (equal b a)))))

  ;; multiple results:
  (must-succeed*
   (defun p (a) (mv (list a) (cons 1 a)))
   (must-fail (tailrec f :domain p)))
  (must-fail (tailrec f :domain (lambda (b) (mv b (list b) (list (list b))))))

  ;; stobjs:
  (must-succeed*
   (defun p (state) (declare (xargs :stobjs state)) state)
   (must-fail (tailrec f :domain p)))
  (must-fail (tailrec f :domain (lambda (state) t)))

  ;; not closed:
  (must-fail (tailrec f :domain (lambda (c) (and (natp c) (integerp d)))))

  ;; not guard-verified:
  (must-succeed*
   (defun p (a) (declare (xargs :verify-guards nil)) (natp a))
   (must-fail (tailrec f :domain p))
   (must-fail (tailrec f :domain (lambda (a) (or (p a) (natp a))))))

  ;; same as OLD:
  (must-fail (tailrec f :domain f))

  ;; calls OLD:
  (must-fail (tailrec f :domain (lambda (a) (equal (f a) 3)))))

 ;; successful applications:
 (must-succeed*

  ;; target function (factorial):
  (defun fact (n)
    (declare (xargs :guard (natp n)))
    (if (zp n) 1 (* n (fact (1- n)))))

  ;; default:
  (must-succeed*
   (tailrec fact)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (acl2-numberp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defun fact{1}-wrapper (n)
      (declare (xargs :guard (natp n)))
      (fact{1} n 1))
    (defthm fact-~>-fact{1}-wrapper (equal (fact n) (fact{1}-wrapper n)))))

  ;; automatic:
  (must-succeed*
   (tailrec fact :domain :auto)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (acl2-numberp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defun fact{1}-wrapper (n)
      (declare (xargs :guard (natp n)))
      (fact{1} n 1))
    (defthm fact-~>-fact{1}-wrapper (equal (fact n) (fact{1}-wrapper n)))))

  ;; function name:
  (must-succeed*
   (tailrec fact :domain natp)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n) :guard (and (natp n) (natp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defun fact{1}-wrapper (n)
      (declare (xargs :guard (natp n)))
      (fact{1} n 1))
    (defthm fact-~>-fact{1}-wrapper (equal (fact n) (fact{1}-wrapper n)))))

  ;; macro name:
  (must-succeed*
   (defmacro intp (m) `(integerp ,m))
   (tailrec fact :domain intp)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (integerp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defun fact{1}-wrapper (n)
      (declare (xargs :guard (natp n)))
      (fact{1} n 1))
    (defthm fact-~>-fact{1}-wrapper (equal (fact n) (fact{1}-wrapper n)))))

  ;; lambda expression:
  (must-succeed*
   (tailrec fact :domain (lambda (a) (acl2-numberp a)))
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (acl2-numberp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defun fact{1}-wrapper (n)
      (declare (xargs :guard (natp n)))
      (fact{1} n 1))
    (defthm fact-~>-fact{1}-wrapper (equal (fact n) (fact{1}-wrapper n)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-NAME option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a symbol:
 (must-fail (tailrec f :new-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :new-name cons))

 ;; keyword (other than :AUTO):
 (must-fail (tailrec f :new-name :g))

 ;; name that already exists:
 (must-fail (tailrec f :new-name car-cdr-elim))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (function-namep 'f{1} (w state))))

 ;; automatic:
 (must-succeed*
  (tailrec f :new-name :auto)
  (assert! (function-namep 'f{1} (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :new-name g)
  (assert! (function-namep 'g (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-ENABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not T, NIL, or :AUTO:
 (must-fail (tailrec f :new-enable 4))

 ;; default, with target function enabled:
 (must-succeed*
  (tailrec f)
  (assert! (fundef-enabledp 'f{1} state)))

 ;; default, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (tailrec f)
  (assert! (fundef-disabledp 'f{1} state)))

 ;; automatic, with target function enabled:
 (must-succeed*
  (tailrec f :new-enable :auto)
  (assert! (fundef-enabledp 'f{1} state)))

 ;; automatic, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (tailrec f :new-enable :auto)
  (assert! (fundef-disabledp 'f{1} state)))

 ;; enable, with target function enabled:
 (must-succeed*
  (tailrec f :new-enable t)
  (assert! (fundef-enabledp 'f{1} state)))

 ;; enable, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (tailrec f :new-enable t)
  (assert! (fundef-enabledp 'f{1} state)))

 ;; disable, with target function enabled:
 (must-succeed*
  (tailrec f :new-enable nil)
  (assert! (fundef-disabledp 'f{1} state)))

 ;; disable, with target function disabled:
 (must-succeed*
  (in-theory (disable f))
  (tailrec f :new-enable nil)
  (assert! (fundef-disabledp 'f{1} state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :WRAPPER option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not T or NIL:
 (must-fail (tailrec f :wrapper "none"))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (function-namep 'f{1}-wrapper (w state))))

 ;; generate:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (function-namep 'f{1}-wrapper (w state))))

 ;; do not generate:
 (must-succeed*
  (tailrec f :wrapper nil)
  (assert! (not (function-namep 'f{1}-wrapper (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :WRAPPER-NAME option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a symbol:
 (must-fail (tailrec f :wrapper-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :wrapper-name cons))

 ;; keyword (other than :AUTO):
 (must-fail (tailrec f :wrapper-name :g))

 ;; name that already exists:
 (must-fail (tailrec f :wrapper-name car-cdr-elim))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (function-namep 'f{1}-wrapper (w state))))

 ;; automatic:
 (must-succeed*
  (tailrec f :wrapper-name :auto)
  (assert! (function-namep 'f{1}-wrapper (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :wrapper-name g)
  (assert! (function-namep 'g (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :WRAPPER-ENABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not T or NIL:
 (must-fail (tailrec f :wrapper-enable 4))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (fundef-enabledp 'f{1}-wrapper state)))

 ;; enable:
 (must-succeed*
  (tailrec f :wrapper-enable t)
  (assert! (fundef-enabledp 'f{1}-wrapper state)))

 ;; disable:
 (must-succeed*
  (tailrec f :wrapper-enable nil)
  (assert! (fundef-disabledp 'f{1}-wrapper state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :THM-NAME option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a symbol:
 (must-fail (tailrec f :thm-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :thm-name cons))

 ;; keyword (other than :AUTO):
 (must-fail (tailrec f :thm-name :f))

 ;; name that already exists:
 (must-fail (tailrec f :thm-name car-cdr-elim))

 ;; determining a name that already exists:
 (must-succeed*
  (defun f-is-f{1}-wrapper () nil)
  (must-fail (tailrec f :thm-name :is)))

 ;; determining, by default, a name that already exists:
 (must-succeed*
  (defun f-~>-f{1}-wrapper () nil)
  (must-fail (tailrec f)))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (theorem-namep 'f-~>-f{1}-wrapper (w state))))

 ;; automatic:
 (must-succeed*
  (tailrec f :thm-name :auto)
  (assert! (theorem-namep 'f-~>-f{1}-wrapper (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :thm-name f-thm)
  (assert! (theorem-namep 'f-thm (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :THM-ENABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not T or NIL:
 (must-fail (tailrec f :thm-enable 7))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}-wrapper) state)))

 ;; enable:
 (must-succeed*
  (tailrec f :thm-enable t)
  (assert! (rune-enabledp '(:rewrite f-~>-f{1}-wrapper) state)))

 ;; disable:
 (must-succeed*
  (tailrec f :thm-enable nil)
  (assert! (rune-disabledp '(:rewrite f-~>-f{1}-wrapper) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NON-EXECUTABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; non-executable target function:
 (defun-nx g (x) (if (atom x) nil (lub (car x) (g (cdr x)))))

 ;; not T, NIL, or :AUTO:
 (must-fail (tailrec f :non-executable "t"))
 (must-fail (tailrec g :non-executable 0))

 ;; default, with target function not non-executable:
 (must-succeed*
  (tailrec f)
  (assert! (not (non-executablep 'f{1} (w state)))))

 ;; default, with target function non-executable:
 (must-succeed*
  (tailrec g)
  (assert! (non-executablep 'g{1} (w state))))

 ;; automatic, with target function not non-executable:
 (must-succeed*
  (tailrec f :non-executable :auto)
  (assert! (not (non-executablep 'f{1} (w state)))))

 ;; automatic, with target function non-executable:
 (must-succeed*
  (tailrec g :non-executable :auto)
  (assert! (non-executablep 'g{1} (w state))))

 ;; make non-executable, with target function not non-executable:
 (must-succeed*
  (tailrec f :non-executable t)
  (assert! (non-executablep 'f{1} (w state))))

 ;; make non-executable, with target function non-executable:
 (must-succeed*
  (tailrec g :non-executable t)
  (assert! (non-executablep 'g{1} (w state))))

 ;; do not make non-executable, with target function not non-executable:
 (must-succeed*
  (tailrec f :non-executable nil)
  (assert! (not (non-executablep 'f{1} (w state)))))

 ;; do not make non-executable, with target function non-executable:
 (must-succeed*
  (tailrec g :non-executable nil)
  (assert! (not (non-executablep 'g{1} (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :VERIFY-GUARDS option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; guard-verified target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; non-guard-verified target function:
 (defun g (x)
   (declare (xargs :verify-guards nil))
   (if (atom x) nil (lub (car x) (g (cdr x)))))

 ;; not T, NIL, or :AUTO:
 (must-fail (tailrec f :verify-guards (1 2 3)))
 (must-fail (tailrec g :verify-guards "T"))

 ;; default, with target function guard-verified:
 (must-succeed*
  (tailrec f)
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; default, with target function not guard-verified:
 (must-succeed*
  (tailrec g)
  (assert! (not (guard-verified-p 'g{1} (w state)))))

 ;; automatic, with target function guard-verified:
 (must-succeed*
  (tailrec f :verify-guards :auto)
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; automatic, with target function not guard-verified:
 (must-succeed*
  (tailrec g :verify-guards :auto)
  (assert! (not (guard-verified-p 'g{1} (w state)))))

 ;; verify guards, with target function guard-verified:
 (must-succeed*
  (tailrec f :verify-guards t)
  (assert! (guard-verified-p 'f{1} (w state))))

 ;; verify guards, with target function not guard-verified:
 (must-succeed*
  (must-fail (tailrec g :verify-guards t)))

 ;; do not verify guards, with target function guard-verified:
 (must-succeed*
  (tailrec f :verify-guards nil)
  (assert! (not (guard-verified-p 'f{1} (w state)))))

 ;; do not verify guards, with target function not guard-verified:
 (must-succeed*
  (tailrec g :verify-guards nil)
  (assert! (not (guard-verified-p 'g{1} (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :HINTS option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a list:
 (must-fail (tailrec f :hints 8))

 ;; not a keyword-value list:
 (must-fail
  (tailrec f :hints (33
                     (("Goal" :in-theory (enable len)))
                     'symbol
                     (("Goal" :in-theory (enable len))))))

 ;; not an applicability condition name:
 (must-fail
  (tailrec f :hints (:not-an-appcond (("Goal" :in-theory (enable len))))))

 ;; duplicate applicability condition names:
 (must-fail
  (tailrec f :hints (:domain-of-base
                     (("Goal" :in-theory (enable atom)))
                     :domain-of-base
                     (("Goal" :in-theory (enable len))))))

 ;; valid but unnecessary hints:
 (must-succeed
  (tailrec f :hints (:domain-of-base
                     (("Goal" :in-theory (enable natp)))
                     :domain-of-nonrec
                     (("Goal" :in-theory (enable natp))))))

 ;; necessary hints:
 (must-succeed*
  (in-theory (disable lub))
  (must-fail (tailrec f))
  (tailrec f
           :hints (:combine-associativity
                   (("Goal" :in-theory (enable lub)))
                   :combine-left-identity
                   (("Goal" :in-theory (enable lub)))
                   :combine-right-identity
                   (("Goal" :in-theory (enable lub)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :PRINT option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a print specifier:
 (must-fail (tailrec f :print 1)
            :with-output-off nil)

 ;; default output:
 (must-succeed (tailrec f)
               :with-output-off nil)

 ;; no output:
 (must-succeed (tailrec f :print nil)
               :with-output-off nil)

 ;; error output:
 (must-succeed (tailrec f :print :error)
               :with-output-off nil)

 ;; result output:
 (must-succeed (tailrec f :print :result)
               :with-output-off nil)

 ;; information output:
 (must-succeed (tailrec f :print :info)
               :with-output-off nil)

 ;; all output:
 (must-succeed (tailrec f :print :all)
               :with-output-off nil)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :SHOW-ONLY option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a boolean:
 (must-fail (tailrec f :show-only #\T))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (function-namep 'f{1} (w state))))

 ;; show only:
 (must-succeed*
  (tailrec f :show-only t)
  (assert! (not (function-namep 'f{1} (w state))))
  :with-output-off nil)

 ;; submit events:
 (must-succeed*
  (tailrec f :show-only nil)
  (assert! (function-namep 'f{1} (w state))))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test handling of redundancy.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; initial call without :PRINT and without :SHOW-ONLY:
 (must-succeed*
  (tailrec f)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; initial call with :PRINT :ALL and without :SHOW-ONLY:
 (must-succeed*
  (tailrec f :print :all)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; initial call with :PRINT NIL and without :SHOW-ONLY:
 (must-succeed*
  (tailrec f :print nil)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; initial call without :PRINT and with :SHOW-ONLY T:
 (must-succeed*
  (tailrec f :show-only t)
  (must-fail-local (must-be-redundant (tailrec f))))

 ;; initial call without :PRINT and with :SHOW-ONLY NIL:
 (must-succeed*
  (tailrec f :show-only nil)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; initial call with :PRINT :ALL and with :SHOW-ONLY T:
 (must-succeed*
  (tailrec f :print :all :show-only t)
  (must-fail-local (must-be-redundant (tailrec f))))

 ;; initial call with :PRINT :ALL and with :SHOW-ONLY NIL:
 (must-succeed*
  (tailrec f :print :all :show-only nil)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; initial call with :PRINT NIL and with :SHOW-ONLY T:
 (must-succeed*
  (tailrec f :print nil :show-only t)
  (must-fail-local (must-be-redundant (tailrec f))))

 ;; initial call with :PRINT NIL and with :SHOW-ONLY NIL:
 (must-succeed*
  (tailrec f :print nil :show-only nil)
  (must-be-redundant (tailrec f))
  (must-be-redundant (tailrec f :print :all))
  (must-be-redundant (tailrec f :print nil))
  (must-be-redundant (tailrec f :show-only t))
  (must-be-redundant (tailrec f :show-only nil))
  (must-be-redundant (tailrec f :print :all :show-only t))
  (must-be-redundant (tailrec f :print nil :show-only t))
  (must-be-redundant (tailrec f :print :all :show-only nil))
  (must-be-redundant (tailrec f :print nil :show-only nil)))

 ;; non-redundant calls:
 (must-succeed*
  (tailrec f)
  ;; different target:
  (must-succeed*
   (defun g (x) (if (atom x) nil (lub (car x) (g (cdr x)))))
   (must-fail-local (must-be-redundant (tailrec g))))
  ;; different domain:
  (must-fail-local (must-be-redundant (tailrec f :domain natp)))
  ;; different options:
  (must-fail-local
   (must-be-redundant (tailrec f :verify-guards nil)))
  (must-fail-local
   (must-be-redundant (tailrec f :new-name f-new)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "More examples.")

 ;; triangular numbers:
 (must-succeed*
  (defun tri (n)
    (declare (xargs :guard (natp n)))
    (if (zp n) 0 (+ n (tri (1- n)))))
  (tailrec tri :domain rationalp)
  (must-be-redundant
   (defun tri{1} (n r)
     (declare (xargs :measure (acl2-count n)
                     :guard (and (natp n) (rationalp r))))
     (if (zp n) r (tri{1} (+ -1 n) (+ r n))))
   (defun tri{1}-wrapper (n)
     (declare (xargs :guard (natp n)))
     (tri{1} n 0))
   (defthm tri-~>-tri{1}-wrapper (equal (tri n) (tri{1}-wrapper n)))))

 ;; pyramidal numbers (i.e. sum of squares):
 (must-succeed*
  (defun pyr (n)
    (declare (xargs :guard (natp n)))
    (if (zp n) 0 (+ (* n n) (pyr (1- n)))))
  (tailrec pyr :domain integerp)
  (must-be-redundant
   (defun pyr{1} (n r)
     (declare (xargs :measure (acl2-count n)
                     :guard (and (natp n) (integerp r))))
     (if (zp n) r (pyr{1} (+ -1 n) (+ r (* n n)))))
   (defun pyr{1}-wrapper (n)
     (declare (xargs :guard (natp n)))
     (pyr{1} n 0))
   (defthm pyr-~>-pyr{1}-wrapper (equal (pyr n) (pyr{1}-wrapper n)))))

 ;; sum list elements:
 (must-succeed*
  (defun list-sum (l)
    (declare (xargs :guard (acl2-number-listp l)))
    (if (endp l) 0 (+ (car l) (list-sum (cdr l)))))
  (tailrec list-sum :variant :monoid-alt :domain acl2-numberp)
  (must-be-redundant
   (defun list-sum{1} (l r)
     (declare (xargs :measure (acl2-count l)
                     :guard (and (acl2-number-listp l) (acl2-numberp r))))
     (if (endp l) r (list-sum{1} (cdr l) (+ r (car l)))))
   (defun list-sum{1}-wrapper (l)
     (declare (xargs :guard (acl2-number-listp l)))
     (list-sum{1} l 0))
   (defthm list-sum-~>-list-sum{1}-wrapper
     (equal (list-sum l) (list-sum{1}-wrapper l)))))

 ;; length of list:
 (must-succeed*
  (defun list-len (l)
    (declare (xargs :guard (true-listp l)))
    (if (endp l) 0 (1+ (list-len (cdr l)))))
  (tailrec list-len :domain natp)
  (must-be-redundant
   (defun list-len{1} (l r)
     (declare (xargs :measure (acl2-count l)
                     :guard (and (true-listp l) (natp r))))
     (if (endp l) r (list-len{1} (cdr l) (+ r 1))))
   (defun list-len{1}-wrapper (l)
     (declare (xargs :guard (true-listp l)))
     (list-len{1} l 0))
   (defthm list-len-~>-list-len{1}-wrapper
     (equal (list-len l) (list-len{1}-wrapper l)))))

 ;; reverse list:
 (must-succeed*
  (defun list-rev (l)
    (if (atom l) nil (append (list-rev (cdr l)) (list (car l)))))
  (tailrec list-rev :domain true-listp)
  (must-be-redundant
   (defun list-rev{1} (l r)
     (declare (xargs :measure (acl2-count l) :guard (true-listp r)))
     (if (atom l) r (list-rev{1} (cdr l) (append (list (car l)) r))))
   (defun list-rev{1}-wrapper (l) (list-rev{1} l nil))
   (defthm list-rev-~>-list-rev{1}-wrapper
     (equal (list-rev l) (list-rev{1}-wrapper l)))))

 ;; raise to power:
 (must-succeed*
  (defun power (x n)
    (declare (xargs :guard (and (acl2-numberp x) (natp n))))
    (if (zp n) 1 (* x (power x (1- n)))))
  (tailrec power :variant :monoid-alt :domain acl2-numberp)
  (must-be-redundant
   (defun power{1} (x n r)
     (declare (xargs :measure (acl2-count n)
                     :guard (and (and (acl2-numberp x) (natp n))
                                 (acl2-numberp r))))
     (if (zp n) r (power{1} x (+ -1 n) (* r x))))
   (defun power{1}-wrapper (x n)
     (declare (xargs :guard (and (acl2-numberp x) (natp n))))
     (power{1} x n 1))
   (defthm power-~>-power{1}-wrapper
     (equal (power x n) (power{1}-wrapper x n))))))

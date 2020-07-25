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
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-fail-local" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

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

 ;; base branch is not ground and variant is :MONOID or :MONOID-ALT:
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
   (defthm f-to-f{1} (equal (f x) (f{1} x nil)))))

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
   (defthm f-to-f{1} (equal (f x) (f{1} x nil))))))

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
   (defthm f-to-f{1} (equal (f x) (f{1} x nil)))))

 ;; monoidal:
 (must-succeed*
  (tailrec f :variant :monoid)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defthm f-to-f{1} (equal (f x) (f{1} x nil)))))

 ;; alternative monoidal:
 (must-succeed*
  (tailrec f :variant :monoid-alt)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) r (f{1} (cdr x) (lub r (car x)))))
   (defthm f-to-f{1} (equal (f x) (f{1} x nil)))))

 ;; associative:
 (must-succeed*
  (tailrec f :variant :assoc)
  (must-be-redundant
   (defun f{1} (x r)
     (declare (xargs :measure (acl2-count x)))
     (if (atom x) (lub r nil) (f{1} (cdr x) (lub r (car x)))))
   (defthm f-to-f{1}
     (equal (f x)
            (and (not (atom x)) (f{1} (cdr x) (car x))))))))

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
    (defthm fact-to-fact{1} (equal (fact n) (fact{1} n 1)))))

  ;; automatic:
  (must-succeed*
   (tailrec fact :domain :auto)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (acl2-numberp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defthm fact-to-fact{1} (equal (fact n) (fact{1} n 1)))))

  ;; function name:
  (must-succeed*
   (tailrec fact :domain natp)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n) :guard (and (natp n) (natp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defthm fact-to-fact{1} (equal (fact n) (fact{1} n 1)))))

  ;; macro name:
  (must-succeed*
   (defmacro intp (m) `(integerp ,m))
   (tailrec fact :domain intp)
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (integerp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defthm fact-to-fact{1} (equal (fact n) (fact{1} n 1)))))

  ;; lambda expression:
  (must-succeed*
   (tailrec fact :domain (lambda (a) (acl2-numberp a)))
   (must-be-redundant
    (defun fact{1} (n r)
      (declare (xargs :measure (acl2-count n)
                      :guard (and (natp n) (acl2-numberp r))))
      (if (zp n) r (fact{1} (+ -1 n) (* r n))))
    (defthm fact-to-fact{1} (equal (fact n) (fact{1} n 1)))))))

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

 (test-title "Test the :ACCUMULATOR option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; not a legal variable name and not :AUTO:
 (must-fail (tailrec f :accumulator "acc"))
 (must-fail (tailrec f :accumulator 15))
 (must-fail (tailrec f :accumulator (acc)))
 (must-fail (tailrec f :accumulator :acc))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert-equal (car (last (formals 'f{1} (w state)))) 'r))

 ;; automatic:
 (must-succeed*
  (tailrec f :accumulator :auto)
  (assert-equal (car (last (formals 'f{1} (w state)))) 'r))

 ;; specified:
 (must-succeed*
  (tailrec f :accumulator a)
  (assert-equal (car (last (formals 'f{1} (w state)))) 'a))
 (must-succeed*
  (tailrec f :accumulator acc)
  (assert-equal (car (last (formals 'f{1} (w state)))) 'acc)))

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
  (assert! (not (function-namep 'f-aux{1} (w state))))
  (assert! (function-namep 'f{1} (w state)))
  (assert! (irecursivep 'f{1} (w state))))

 ;; generate:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (function-namep 'f-aux{1} (w state)))
  (assert! (function-namep 'f{1} (w state)))
  (assert! (irecursivep 'f-aux{1} (w state)))
  (assert! (not (irecursivep 'f{1} (w state)))))

 ;; do not generate:
 (must-succeed*
  (tailrec f :wrapper nil)
  (assert! (not (function-namep 'f-aux{1} (w state))))
  (assert! (function-namep 'f{1} (w state)))
  (assert! (irecursivep 'f{1} (w state)))))

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
 (must-fail (tailrec f :wrapper t :wrapper-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :wrapper t :wrapper-name cons))

 ;; keyword (other than :AUTO):
 (must-fail (tailrec f :wrapper t :wrapper-name :g))

 ;; name that already exists:
 (must-fail (tailrec f :wrapper t :wrapper-name car-cdr-elim))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (function-namep 'f{1} (w state)))
  (assert! (not (irecursivep 'f{1} (w state)))))

 ;; automatic:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-name :auto)
  (assert! (function-namep 'f{1} (w state)))
  (assert! (not (irecursivep 'f{1} (w state)))))

 ;; specified:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-name g)
  (assert! (function-namep 'g (w state)))
  (assert! (not (irecursivep 'g (w state))))))

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
 (must-fail (tailrec f :wrapper t :wrapper-enable 4))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (fundef-disabledp 'f{1} state)))

 ;; enable:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-enable t)
  (assert! (fundef-enabledp 'f{1} state)))

 ;; disable:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-enable nil)
  (assert! (fundef-disabledp 'f{1} state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :OLD-TO-NEW-NAME option.")

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
 (must-fail (tailrec f :old-to-new-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :old-to-new-name cons))

 ;; name that already exists:
 (must-fail (tailrec f :old-to-new-name car-cdr-elim))

 ;; determining a name that already exists:
 (must-succeed*
  (defun f-is-f{1} () nil)
  (must-fail (tailrec f :old-to-new-name :-is-)))

 ;; determining, by default, a name that already exists:
 (must-succeed*
  (defun f-to-f{1} () nil)
  (must-fail (tailrec f)))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (theorem-namep 'f-to-f{1} (w state))))

 ;; specified separator:
 (must-succeed*
  (tailrec f :old-to-new-name :-becomes-)
  (assert! (theorem-namep 'f-becomes-f{1} (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :old-to-new-name f-thm)
  (assert! (theorem-namep 'f-thm (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-TO-OLD-NAME option.")

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
 (must-fail (tailrec f :new-to-old-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :new-to-old-name cons))

 ;; name that already exists:
 (must-fail (tailrec f :new-to-old-name car-cdr-elim))

 ;; determining a name that already exists:
 (must-succeed*
  (defun f{1}-is-f () nil)
  (must-fail (tailrec f :new-to-old-name :-is-)))

 ;; determining, by default, a name that already exists:
 (must-succeed*
  (defun f{1}-to-f () nil)
  (must-fail (tailrec f)))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (theorem-namep 'f{1}-to-f (w state))))

 ;; specified separator:
 (must-succeed*
  (tailrec f :new-to-old-name :-becomes-)
  (assert! (theorem-namep 'f{1}-becomes-f (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :new-to-old-name f-thm)
  (assert! (theorem-namep 'f-thm (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :OLD-TO-WRAPPER-NAME option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; supplied when disallowed:
 (must-fail (tailrec f :wrapper nil :old-to-wrapper-name g))

 ;; not a symbol:
 (must-fail (tailrec f :wrapper t :old-to-wrapper-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :wrapper t :old-to-wrapper-name cons))

 ;; name that already exists:
 (must-fail (tailrec f :wrapper t :old-to-wrapper-name car-cdr-elim))

 ;; determining a name that already exists:
 (must-succeed*
  (defun f-is-f{1} () nil)
  (must-fail (tailrec f :wrapper t :old-to-wrapper-name :-is-)))

 ;; determining, by default, a name that already exists:
 (must-succeed*
  (defun f-to-f{1} () nil)
  (must-fail (tailrec f :wrapper t)))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (theorem-namep 'f-to-f{1} (w state))))

 ;; specified separator:
 (must-succeed*
  (tailrec f :wrapper t :old-to-wrapper-name :-becomes-)
  (assert! (theorem-namep 'f-becomes-f{1} (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :wrapper t :old-to-wrapper-name f-thm)
  (assert! (theorem-namep 'f-thm (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :WRAPPER-TO-OLD-NAME option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; supplied when disallowed:
 (must-fail (tailrec f :wrapper nil :wrapper-to-old-name g))

 ;; not a symbol:
 (must-fail (tailrec f :wrapper t :wrapper-to-old-name 33))

 ;; in the main Lisp package:
 (must-fail (tailrec f :wrapper t :wrapper-to-old-name cons))

 ;; name that already exists:
 (must-fail (tailrec f :wrapper t :wrapper-to-old-name car-cdr-elim))

 ;; determining a name that already exists:
 (must-succeed*
  (defun f{1}-is-f () nil)
  (must-fail (tailrec f :wrapper t :wrapper-to-old-name :-is-)))

 ;; determining, by default, a name that already exists:
 (must-succeed*
  (defun f{1}-to-f () nil)
  (must-fail (tailrec f :wrapper t)))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (theorem-namep 'f{1}-to-f (w state))))

 ;; specified separator:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-to-old-name :-becomes-)
  (assert! (theorem-namep 'f{1}-becomes-f (w state))))

 ;; specified:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-to-old-name f-thm)
  (assert! (theorem-namep 'f-thm (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :OLD-TO-NEW-ENABLE option.")

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
 (must-fail (tailrec f :old-to-new-enable 7))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (rune-disabledp '(:rewrite f-to-f{1}) state)))

 ;; enable:
 (must-succeed*
  (tailrec f :old-to-new-enable t)
  (assert! (rune-enabledp '(:rewrite f-to-f{1}) state)))

 ;; disable:
 (must-succeed*
  (tailrec f :old-to-new-enable nil)
  (assert! (rune-disabledp '(:rewrite f-to-f{1}) state)))

 ;; enabled when also the new-to-old theorem is:
 (must-fail
  (tailrec f :wrapper t :old-to-new-enable t :new-to-old-enable t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :NEW-TO-OLD-ENABLE option.")

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
 (must-fail (tailrec f :new-to-old-enable 7))

 ;; default:
 (must-succeed*
  (tailrec f)
  (assert! (rune-disabledp '(:rewrite f{1}-to-f) state)))

 ;; enable:
 (must-succeed*
  (tailrec f :new-to-old-enable t)
  (assert! (rune-enabledp '(:rewrite f{1}-to-f) state)))

 ;; disable:
 (must-succeed*
  (tailrec f :new-to-old-enable nil)
  (assert! (rune-disabledp '(:rewrite f{1}-to-f) state)))

 ;; enabled when also the old-to-new theorem is:
 (must-fail
  (tailrec f :new-to-old-enable t :old-to-new-enable t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :OLD-TO-WRAPPER-ENABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; supplied when disallowed:
 (must-fail (tailrec f :wrapper nil :old-to-wrapper-enable t))
 (must-fail (tailrec f :wrapper nil :old-to-wrapper-enable nil))

 ;; not T or NIL:
 (must-fail (tailrec f :wrapper t :old-to-wrapper-enable 7))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t)
  (assert! (rune-disabledp '(:rewrite f-to-f{1}) state)))

 ;; enable:
 (must-succeed*
  (tailrec f :wrapper t :old-to-wrapper-enable t)
  (assert! (rune-enabledp '(:rewrite f-to-f{1}) state)))

 ;; disable:
 (must-succeed*
  (tailrec f :wrapper t :old-to-wrapper-enable nil)
  (assert! (rune-disabledp '(:rewrite f-to-f{1}) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test the :WRAPPER-TO-OLD-ENABLE option.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))

 ;; supplied when disallowed:
 (must-fail (tailrec f :wrapper nil :wrapper-to-old-enable t))
 (must-fail (tailrec f :wrapper nil :wrapper-to-old-enable nil))

 ;; not T or NIL:
 (must-fail (tailrec f :wrapper t :wrapper-to-old-enable 7))

 ;; default:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-enable nil)
  (assert! (rune-disabledp '(:rewrite f{1}-to-f) state)))

 ;; enable:
 (must-succeed*
  (tailrec f
           :wrapper t
           :wrapper-enable nil
           :old-to-wrapper-enable nil
           :wrapper-to-old-enable t)
  (assert! (rune-enabledp '(:rewrite f{1}-to-f) state)))

 ;; disable:
 (must-succeed*
  (tailrec f :wrapper t :wrapper-to-old-enable nil)
  (assert! (rune-disabledp '(:rewrite f{1}-to-f) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test non-executability.")

 ;; least upper bound in lattice consisting of NIL as bottom, T as top,
 ;; and all the other values between NIL and T and incomparable to each other:
 (defun lub (x y)
   (cond ((null x) y)
         ((null y) x)
         ((equal x y) x)
         (t t)))

 ;; executable target function:
 (defun f (x) (if (atom x) nil (lub (car x) (f (cdr x)))))
 (assert! (not (non-executablep 'f (w state))))

 ;; non-executable target function:
 (defun-nx g (x) (if (atom x) nil (lub (car x) (g (cdr x)))))
 (assert! (non-executablep 'g (w state)))

 ;; transforming F preserves executability:
 (tailrec f)
 (assert! (not (non-executablep 'f{1} (w state))))

 ;; transforming G preserves non-executability:
 (tailrec g)
 (assert! (non-executablep 'g{1} (w state))))

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

 (test-title "Test handling of swapped base and recursive branches.")

 (defun fact (n)
   (declare (xargs :guard (natp n)))
   (if (not (zp n))
       (* n (fact (1- n)))
     1))

 (tailrec fact))

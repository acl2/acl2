; System Utilities -- World Queries -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "world-queries")
(include-book "kestrel/utilities/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (function-symbol-listp nil (w state)))

(assert! (function-symbol-listp '(len cons atom) (w state)))

(assert! (not (function-symbol-listp '(len cons aaaaatom) (w state))))

(must-succeed*
 (defun f (x) x)
 (defun g (x) x)
 (assert! (function-symbol-listp '(f g g) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (theorem-symbol-listp nil (w state)))

(assert! (theorem-symbol-listp '(car-cdr-elim cons-car-cdr) (w state)))

(assert! (not (theorem-symbol-listp '(car-cdr-elim len) (w state))))

(must-succeed*
 (defthm th1 (acl2-numberp (+ x y)))
 (defthm th2 (acl2-numberp (- x)))
 (assert! (theorem-symbol-listp '(th2 th1) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (macro-symbol-listp nil (w state)))

(assert! (macro-symbol-listp '(append + * *) (w state)))

(assert! (not (macro-symbol-listp '(append binary-+) (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (defmacro n (x) `(cons ,x ,x))
 (assert! (macro-symbol-listp '(m n append) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (function-namep 'len (w state)))

(assert! (not (function-namep 'cons-car-cdr (w state))))

(assert! (not (function-namep 'bbbbbbbbbbb (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (function-namep 'f (w state))))

(assert! (not (function-namep 33 (w state))))

(assert! (not (function-namep "len" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (theorem-namep 'car-cdr-elim (w state)))

(assert! (not (theorem-namep 'cons (w state))))

(assert! (not (theorem-namep 'aaaaaaaaa (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (theorem-namep 'th (w state))))

(assert! (not (theorem-namep 8 (w state))))

(assert! (not (theorem-namep "car-cdr-elim" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (macro-namep 'append (w state)))

(assert! (not (macro-namep 'cons (w state))))

(assert! (not (macro-namep 'aaaaaaaaaa (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (assert! (macro-namep 'm (w state))))

(assert! (not (macro-namep 5/3 (w state))))

(assert! (not (macro-namep "append" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (function-name-listp nil (w state)))

(assert! (function-name-listp '(len cons atom) (w state)))

(assert! (not (function-name-listp '(len cons aaaaatom) (w state))))

(must-succeed*
 (defun f (x) x)
 (defun g (x) x)
 (assert! (function-name-listp '(f g g) (w state))))

(assert! (not (function-name-listp 33 (w state))))

(assert! (not (function-name-listp '(1 2 3) (w state))))

(assert! (not (function-name-listp "ab" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (theorem-name-listp nil (w state)))

(assert! (theorem-name-listp '(car-cdr-elim cons-car-cdr) (w state)))

(assert! (not (theorem-name-listp '(car-cdr-elim len) (w state))))

(must-succeed*
 (defthm th1 (acl2-numberp (+ x y)))
 (defthm th2 (acl2-numberp (- x)))
 (assert! (theorem-name-listp '(th2 th1) (w state))))

(assert! (not (theorem-name-listp 33 (w state))))

(assert! (not (theorem-name-listp '(1 2 3) (w state))))

(assert! (not (theorem-name-listp "ab" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (macro-name-listp nil (w state)))

(assert! (macro-name-listp '(append + * *) (w state)))

(assert! (not (macro-name-listp '(append binary-+) (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (defmacro n (x) `(cons ,x ,x))
 (assert! (macro-name-listp '(m n append) (w state))))

(assert! (not (macro-name-listp 33 (w state))))

(assert! (not (macro-name-listp '(1 2 3) (w state))))

(assert! (not (macro-name-listp "ab" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (logical-name-listp '(append "ACL2" car-cdr-elim cons) (w state)))

(assert! (not (logical-name-listp '(1 2 3) (w state))))

(assert! (not (logical-name-listp '(cccccccc) (w state))))

(assert! (not (logical-name-listp "xyz" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (logic-function-namep 'len (w state)))

(assert! (not (logic-function-namep 'car-cdr-elim (w state))))

(assert! (not (logic-function-namep 'aaaaaaaaa (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (logic-function-namep 'f (w state))))

(assert! (not (logic-function-namep "len" (w state))))

(assert! (not (logic-function-namep 'error1 (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert! (not (logic-function-namep 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (formals+ 'len (w state)) '(x))

(must-succeed*
 (defun f (x y zz aaa b77) (list x y zz aaa b77))
 (assert-equal (formals+ 'f (w state)) '(x y zz aaa b77)))

(assert-equal (formals+ '(lambda (x y) (binary-+ x y)) (w state))
              '(x y))

(assert-equal (formals+ '(lambda () '33) (w state))
              nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (arity+ 'len (w state)) 1)

(must-succeed*
 (defun f (x y zz aaa b77) (list x y zz aaa b77))
 (assert-equal (arity+ 'f (w state)) 5))

(assert-equal (arity+ '(lambda (x y) (binary-+ x y)) (w state))
              2)

(assert-equal (arity+ '(lambda () '33) (w state))
              0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (stobjs-in+ 'cons (w state)) '(nil nil))

(assert-equal (stobjs-in+ 'fmt (w state)) '(nil nil nil state nil))

(must-succeed*
 (defstobj s)
 (defun f (x s state)
   (declare (ignore x s state) (xargs :stobjs (s state)))
   nil)
 (assert-equal (stobjs-in+ 'f (w state)) '(nil s state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (stobjs-out+ 'cons (w state)) '(nil))

(assert-equal (stobjs-out+ 'fmt (w state)) '(nil state))

(must-succeed*
 (defstobj s)
 (defun f (x s) (declare (xargs :stobjs s)) (mv s x))
 (assert-equal (stobjs-out+ 'f (w state)) '(s nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (macro-args+ 'list (w state)) '(&rest args))

(must-succeed*
 (defmacro mac (x y z &key a (b '3) (c '(#\a 1/3) cp)) (list x y z a b c cp))
 (assert-equal (macro-args+ 'mac (w state))
               '(x y z &key a (b '3) (c '(#\a 1/3) cp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (definedp 'not (w state)))

(assert! (not (definedp 'cons (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (definedp 'f (w state))))

(must-succeed*
 (defstub f (*) => *)
 (assert! (not (definedp 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm th (equal (f x) x)))
 (assert! (not (definedp 'f (w state)))))

(must-succeed*
 (defchoose f x (y) (equal x y))
 (assert! (not (definedp 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (definedp+ 'not (w state)))

(assert! (not (definedp+ 'cons (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (definedp+ 'f (w state))))

(must-succeed*
 (defstub f (*) => *)
 (assert! (not (definedp+ 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm th (equal (f x) x)))
 (assert! (not (definedp+ 'f (w state)))))

(must-succeed*
 (defchoose f x (y) (equal x y))
 (assert! (not (definedp+ 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (primitivep+ 'cons (w state)))

(assert! (primitivep+ 'binary-+ (w state)))

(assert! (not (primitivep+ 'len (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (not (primitivep+ 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-p 'len (w state)))

(assert! (guard-verified-p 'cons (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards t)) x)
 (assert! (guard-verified-p 'f (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert! (not (guard-verified-p 'f (w state)))))

(must-succeed*
 (defthm th (acl2-numberp (+ (fix x) (fix y))))
 (verify-guards th)
 (assert! (guard-verified-p 'th (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (not (guard-verified-p 'th (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-p+ 'len (w state)))

(assert! (guard-verified-p+ 'cons (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards t)) x)
 (assert! (guard-verified-p+ 'f (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert! (not (guard-verified-p+ 'f (w state)))))

(must-succeed*
 (defthm th (acl2-numberp (+ (fix x) (fix y))))
 (verify-guards th)
 (assert! (guard-verified-p+ 'th (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (not (guard-verified-p+ 'th (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubody+ 'atom (w state)) '(not (consp x)))

(must-succeed*
 (defun f (x) x)
 (assert-equal (ubody+ 'f (w state)) 'x))

(must-succeed*
 (defun p (x) (and (natp x) (natp 3)))
 (assert-equal (body 'p t (w state)) '(natp x))
 (assert-equal (ubody+ 'p (w state)) '(if (natp x) (natp '3) 'nil)))

(assert-equal (ubody+ '(lambda (x y) (cons x (h '3))) (w state))
              '(cons x (h '3)))

(assert-equal (ubody+ '(lambda (a) (h a '"abc")) (w state))
              '(h a '"abc"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (uguard 'atom (w state)) *t*)

(assert-equal (uguard 'car (w state)) '(if (consp x) 't (equal x 'nil)))

(must-succeed*
 (defun f (x) (declare (xargs :guard (natp x))) x)
 (assert-equal (uguard 'f (w state)) '(natp x)))

(assert-equal (uguard '(lambda (z y) (binary-+ y (cons z '2))) (w state)) *t*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (uguard+ 'atom (w state)) *t*)

(assert-equal (uguard+ 'car (w state)) '(if (consp x) 't (equal x 'nil)))

(must-succeed*
 (defun f (x) (declare (xargs :guard (natp x))) x)
 (assert-equal (uguard+ 'f (w state)) '(natp x)))

(assert-equal (uguard+ '(lambda (z y) (binary-+ y (cons z '2))) (w state)) *t*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (non-executablep 'not (w state))))

(assert! (not (non-executablep 'len (w state))))

(must-succeed*
 (defun-nx f (x) x)
 (assert! (non-executablep 'f (w state))))

(must-succeed*
 (defun-sk g (x) (forall (y z) (equal x (cons y z))))
 (assert! (non-executablep 'g (w state))))

(must-succeed*
 (defun-sk h (x y) (exists z (equal z (cons x y)))
   :witness-dcls ((declare (xargs :non-executable nil))))
 (assert! (not (non-executablep 'h (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (non-executablep+ 'not (w state))))

(assert! (not (non-executablep+ 'len (w state))))

(must-succeed*
 (defun-nx f (x) x)
 (assert! (non-executablep+ 'f (w state))))

(must-succeed*
 (defun-sk g (x) (forall (y z) (equal x (cons y z))))
 (assert! (non-executablep+ 'g (w state))))

(must-succeed*
 (defun-sk h (x y) (exists z (equal z (cons x y)))
   :witness-dcls ((declare (xargs :non-executable nil))))
 (assert! (not (non-executablep+ 'h (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-nx f (x) (cons (list x) (list x)))
 (assert-equal (ubody 'f (w state))
               '(return-last 'progn
                             (throw-nonexec-error 'f (cons x 'nil))
                             (cons (cons x 'nil) (cons x 'nil))))
 (assert-equal (unwrapped-nonexec-body 'f (w state))
               '(cons (cons x 'nil) (cons x 'nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun-nx f (x) (cons (list x) (list x)))
 (assert-equal (ubody 'f (w state))
               '(return-last 'progn
                             (throw-nonexec-error 'f (cons x 'nil))
                             (cons (cons x 'nil) (cons x 'nil))))
 (assert-equal (unwrapped-nonexec-body+ 'f (w state))
               '(cons (cons x 'nil) (cons x 'nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (number-of-results 'cons (w state)) 1)

(assert-equal (number-of-results 'len (w state)) 1)

(must-succeed*
 (defun f (x) (mv x (list x)))
 (assert-equal (number-of-results 'f (w state)) 2))

(must-succeed*
 (defun f (x) (mv x (list x) (list x x)))
 (assert-equal (number-of-results 'f (w state)) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (number-of-results+ 'cons (w state)) 1)

(assert-equal (number-of-results+ 'len (w state)) 1)

(must-succeed*
 (defun f (x) (mv x (list x)))
 (assert-equal (number-of-results+ 'f (w state)) 2))

(must-succeed*
 (defun f (x) (mv x (list x) (list x x)))
 (assert-equal (number-of-results+ 'f (w state)) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (no-stobjs-p 'cons (w state)))

(assert! (no-stobjs-p 'len (w state)))

(assert! (not (no-stobjs-p 'guard-obligation (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (no-stobjs-p 'f (w state))))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert! (not (no-stobjs-p 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (no-stobjs-p+ 'cons (w state)))

(assert! (no-stobjs-p+ 'len (w state)))

(assert! (not (no-stobjs-p+ 'guard-obligation (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (no-stobjs-p+ 'f (w state))))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert! (not (no-stobjs-p+ 'f (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (irecursivep 'cons (w state)) nil)

(assert-equal (irecursivep 'len (w state)) '(len))

(assert-equal (irecursivep 'pseudo-termp (w state))
              '(pseudo-termp pseudo-term-listp))

(must-succeed*
 (defun f (x) (if (consp x) (f (car x)) 0))
 (assert-equal (irecursivep 'f (w state)) '(f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (irecursivep+ 'cons (w state)) nil)

(assert-equal (irecursivep+ 'len (w state)) '(len))

(assert-equal (irecursivep+ 'pseudo-termp (w state))
              '(pseudo-termp pseudo-term-listp))

(must-succeed*
 (defun f (x) (if (consp x) (f (car x)) 0))
 (assert-equal (irecursivep+ 'f (w state)) '(f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (measure 'len (w state)) '(acl2-count x))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (measure 'f (w state))
               '(nfix (binary-+ '10 (unary-- x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (measure+ 'len (w state)) '(acl2-count x))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (measure+ 'f (w state))
               '(nfix (binary-+ '10 (unary-- x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (measured-subset 'len (w state)) '(x))

(assert-equal (measured-subset 'binary-append (w state)) '(x))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (measured-subset 'f (w state)) '(x)))

(must-succeed*
 (defun f (x y z)
   (declare (xargs :measure (nfix (- 10 y))))
   (if (and (natp y) (< y 10))
       (f x (1+ y) z)
     (cons x z)))
 (assert-equal (measured-subset 'f (w state)) '(y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (measured-subset+ 'len (w state)) '(x))

(assert-equal (measured-subset+ 'binary-append (w state)) '(x))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (measured-subset+ 'f (w state)) '(x)))

(must-succeed*
 (defun f (x y z)
   (declare (xargs :measure (nfix (- 10 y))))
   (if (and (natp y) (< y 10))
       (f x (1+ y) z)
     (cons x z)))
 (assert-equal (measured-subset+ 'f (w state)) '(y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (well-founded-relation 'len (w state)) 'o<)

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (well-founded-relation 'f (w state)) 'o<))

(must-succeed*
 ;; well-founded relation:
 (defun o-p$ (x) (o-p x))
 (defun o<$ (x y) (o< x y))
 (defun id (x) x)
 (defthm o<$-is-well-founded-relation
   (and (implies (o-p$ x) (o-p (id x)))
        (implies (and (o-p$ x)
                      (o-p$ y)
                      (o<$ x y))
                 (o< (id x) (id y))))
   :rule-classes :well-founded-relation)
 ;; function using the well-founded relation just introduced:
 (defun f (x)
   (declare (xargs :well-founded-relation o<$))
   (if (zp x)
       nil
     (f (1- x))))
 ;; test:
 (assert-equal (well-founded-relation 'f (w state)) 'o<$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (well-founded-relation+ 'len (w state)) 'o<)

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (well-founded-relation+ 'f (w state)) 'o<))

(must-succeed*
 ;; well-founded relation:
 (defun o-p$ (x) (o-p x))
 (defun o<$ (x y) (o< x y))
 (defun id (x) x)
 (defthm o<$-is-well-founded-relation
   (and (implies (o-p$ x) (o-p (id x)))
        (implies (and (o-p$ x)
                      (o-p$ y)
                      (o<$ x y))
                 (o< (id x) (id y))))
   :rule-classes :well-founded-relation)
 ;; function using the well-founded relation just introduced:
 (defun f (x)
   (declare (xargs :well-founded-relation o<$))
   (if (zp x)
       nil
     (f (1- x))))
 ;; test:
 (assert-equal (well-founded-relation+ 'f (w state)) 'o<$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ruler-extenders 'len (w state)) '(mv-list return-last))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders 'f (w state)) '(cons)))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders :all))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders 'f (w state)) :all))

(must-succeed*
 (defun fact (n)
   (declare (xargs :ruler-extenders (:lambdas)))
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1)))
 (assert-equal (ruler-extenders 'fact (w state)) '(:lambdas)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ruler-extenders+ 'len (w state)) '(mv-list return-last))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders+ 'f (w state)) '(cons)))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders :all))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders+ 'f (w state)) :all))

(must-succeed*
 (defun fact (n)
   (declare (xargs :ruler-extenders (:lambdas)))
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1)))
 (assert-equal (ruler-extenders+ 'fact (w state)) '(:lambdas)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (macro-required-args+ 'tthm (w state)) '(fn))

(assert-equal (macro-required-args+ 'list (w state)) nil)

(assert-equal (macro-required-args+ 'defun (w state)) nil)

(assert-equal (macro-required-args+ 'defthm (w state)) '(name term))

(assert-equal (macro-required-args+ 'defun-sk (w state)) '(name args))

(must-succeed*
 (defmacro m (a) `(list ,a))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))

(must-succeed*
 (defmacro m (a &key b) `(list ,a ,(or b :default)))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))

(must-succeed*
 (defmacro m (&whole form a &optional b &key c (d '3) (e '#\e e-p))
   `(list ,a ,b ,c ,d ,e ,e-p ,form))
 (assert-equal (macro-required-args+ 'm (w state)) '(a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (macro-keyword-args+ 'tthm (w state)) nil)

(assert-equal (macro-keyword-args+ 'list (w state)) nil)

(assert-equal (macro-keyword-args+ 'defun (w state)) nil)

(assert-equal
 (macro-keyword-args+ 'defthm (w state)) '((rule-classes . (:rewrite))
                                           (instructions . nil)
                                           (hints . nil)
                                           (otf-flg . nil)))

(assert-equal (macro-keyword-args+ 'defun-sk (w state)) nil)

(must-succeed*
 (defmacro m (a) `(list ,a))
 (assert-equal (macro-keyword-args+ 'm (w state)) nil))

(must-succeed*
 (defmacro m (a &key b) `(list ,a ,(or b :default)))
 (assert-equal (macro-keyword-args+ 'm (w state)) '((b . nil))))

(must-succeed*
 (defmacro m (&whole form a &optional b &key c (d '3) (e '#\e e-p))
   `(list ,a ,b ,c ,d ,e ,e-p ,form))
 (assert-equal (macro-keyword-args+ 'm (w state)) '((c . nil)
                                                    (d . 3)
                                                    (e . #\e))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (thm-formula 'car-cdr-elim (w state))
              '(implies (consp x)
                        (equal (cons (car x) (cdr x)) x)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (thm-formula 'th (w state)) '(acl2-numberp (unary-- x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (thm-formula+ 'car-cdr-elim (w state))
              '(implies (consp x)
                        (equal (cons (car x) (cdr x)) x)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (thm-formula+ 'th (w state)) '(acl2-numberp (unary-- x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (classes 'car-cdr-elim (w state)) '((:elim)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (classes 'th (w state)) '((:rewrite))))

(must-succeed*
 (defthm th (booleanp (if x t nil)) :rule-classes :type-prescription)
 (assert-equal (classes 'th (w state))
               '((:type-prescription :typed-term (if x 't 'nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (classes+ 'car-cdr-elim (w state)) '((:elim)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (classes+ 'th (w state)) '((:rewrite))))

(must-succeed*
 (defthm th (booleanp (if x t nil)) :rule-classes :type-prescription)
 (assert-equal (classes+ 'th (w state))
               '((:type-prescription :typed-term (if x 't 'nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (let ((im (induction-machine 'len (w state))))
           (and (pseudo-induction-machinep 'len im)
                (= (len im) 2)
                (let ((im1 (first im)))
                  (and (equal (access tests-and-calls im1 :tests)
                              '((consp x)))
                       (equal (access tests-and-calls im1 :calls)
                              '((len (cdr x))))))
                (let ((im2 (second im)))
                  (and (equal (access tests-and-calls im2 :tests)
                              '((not (consp x))))
                       (equal (access tests-and-calls im2 :calls)
                              nil))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((im (induction-machine 'fib (w state))))
            (and (pseudo-induction-machinep 'fib im)
                 (= (len im) 3)
                 (let ((im1 (first im)))
                   (and (equal (access tests-and-calls im1 :tests)
                               '((zp n)))
                        (equal (access tests-and-calls im1 :calls)
                               nil)))
                 (let ((im2 (second im)))
                   (and (equal (access tests-and-calls im2 :tests)
                               '((not (zp n))
                                 (= n '1)))
                        (equal (access tests-and-calls im2 :calls)
                               nil)))
                 (let ((im3 (third im)))
                   (and (equal (access tests-and-calls im3 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-calls im3 :calls)
                               '((fib (binary-+ '-1 n))
                                 (fib (binary-+ '-2 n))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (let ((im (induction-machine+ 'len (w state))))
           (and (pseudo-induction-machinep 'len im)
                (= (len im) 2)
                (let ((im1 (first im)))
                  (and (equal (access tests-and-calls im1 :tests)
                              '((consp x)))
                       (equal (access tests-and-calls im1 :calls)
                              '((len (cdr x))))))
                (let ((im2 (second im)))
                  (and (equal (access tests-and-calls im2 :tests)
                              '((not (consp x))))
                       (equal (access tests-and-calls im2 :calls)
                              nil))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((im (induction-machine+ 'fib (w state))))
            (and (pseudo-induction-machinep 'fib im)
                 (= (len im) 3)
                 (let ((im1 (first im)))
                   (and (equal (access tests-and-calls im1 :tests)
                               '((zp n)))
                        (equal (access tests-and-calls im1 :calls)
                               nil)))
                 (let ((im2 (second im)))
                   (and (equal (access tests-and-calls im2 :tests)
                               '((not (zp n))
                                 (= n '1)))
                        (equal (access tests-and-calls im2 :calls)
                               nil)))
                 (let ((im3 (third im)))
                   (and (equal (access tests-and-calls im3 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-calls im3 :calls)
                               '((fib (binary-+ '-1 n))
                                 (fib (binary-+ '-2 n))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-tests-and-callp (make tests-and-call
                                       :tests '((f x))
                                       :call ''3)))

(assert! (not (pseudo-tests-and-callp (make tests-and-call
                                            :tests "a"
                                            :call 2))))

(assert! (not (pseudo-tests-and-callp 88)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (pseudo-tests-and-call-listp nil))

(assert! (pseudo-tests-and-call-listp (list (make tests-and-call
                                                  :tests '((f x))
                                                  :call '(g y z))
                                            (make tests-and-call
                                                  :tests '('3 x)
                                                  :call ''#\a))))

(assert! (not (pseudo-tests-and-call-listp (list (make tests-and-call
                                                       :tests 1
                                                       :call 2)
                                                 (make tests-and-call
                                                       :tests "a"
                                                       :call "b")))))

(assert! (not (pseudo-tests-and-call-listp 88)))

(assert! (not (pseudo-tests-and-call-listp (make tests-and-call
                                                 :tests 1
                                                 :call 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (let ((rc (recursive-calls 'len (w state))))
           (and (pseudo-tests-and-call-listp rc)
                (= (len rc) 1)
                (let ((rc1 (first rc)))
                  (and  (equal (access tests-and-call rc1 :tests)
                               '((consp x)))
                        (equal (access tests-and-call rc1 :call)
                               '(len (cdr x))))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((rc (recursive-calls 'fib (w state))))
            (and (pseudo-tests-and-call-listp rc)
                 (= (len rc) 2)
                 (let ((rc1 (first rc)))
                   (and (equal (access tests-and-call rc1 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc1 :call)
                               '(fib (binary-+ '-1 n)))))
                 (let ((rc2 (second rc)))
                   (and (equal (access tests-and-call rc2 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc2 :call)
                               '(fib (binary-+ '-2 n)))))))))

(must-succeed*
 (defun fib (n)
   (declare (xargs :mode :program))
   (if (zp n)
       1
     (if (= n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert! (let ((rc (recursive-calls 'fib (w state))))
            (and (pseudo-tests-and-call-listp rc)
                 (= (len rc) 2)
                 (let ((rc1 (first rc)))
                   (and (equal (access tests-and-call rc1 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc1 :call)
                               '(fib (binary-+ '-1 n)))))
                 (let ((rc2 (second rc)))
                   (and (equal (access tests-and-call rc2 :tests)
                               '((not (zp n))
                                 (not (= n '1))))
                        (equal (access tests-and-call rc2 :call)
                               '(fib (binary-+ '-2 n)))))))))

(must-succeed*
 (defun nonrec (x) (cons x x))
 (assert-equal (recursive-calls 'nonrec (w state)) nil))

(must-succeed*
 (defun nonrec (x) (declare (xargs :mode :program)) (cons x x))
 (assert-equal (recursive-calls 'nonrec (w state)) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defund f (x) x)
 (assert! (fundef-disabledp 'f state)))

(must-succeed*
 (defun f (x) x)
 (assert! (not (fundef-disabledp 'f state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert! (fundef-enabledp 'f state)))

(must-succeed*
 (defund f (x) x)
 (assert! (not (fundef-enabledp 'f state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (rune-disabledp '(:rewrite cons-car-cdr) state)))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)))
 (assert! (rune-disabledp '(:rewrite th) state)))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (not (rune-disabledp '(:rewrite th) state))))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)) :rule-classes :type-prescription)
 (assert! (rune-disabledp '(:type-prescription th) state)))

(must-succeed*
 (defthmd th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (rune-disabledp '(:rewrite th . 1) state))
 (assert! (rune-disabledp '(:rewrite th . 2) state)))

(must-succeed*
 (defthm th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (not (rune-disabledp '(:rewrite th . 1) state)))
 (assert! (not (rune-disabledp '(:rewrite th . 2) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (rune-enabledp '(:rewrite cons-car-cdr) state))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (rune-enabledp '(:rewrite th) state)))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)))
 (assert! (not (rune-enabledp '(:rewrite th) state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)) :rule-classes :type-prescription)
 (assert! (rune-enabledp '(:type-prescription th) state)))

(must-succeed*
 (defthm th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (rune-enabledp '(:rewrite th . 1) state))
 (assert! (rune-enabledp '(:rewrite th . 2) state)))

(must-succeed*
 (defthmd th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (not (rune-enabledp '(:rewrite th . 1) state)))
 (assert! (not (rune-enabledp '(:rewrite th . 2) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (string-listp (known-packages state)))

(assert! (no-duplicatesp-equal (known-packages state)))

(assert! (member-equal "ACL2" (known-packages state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (string-listp (known-packages+ state)))

(assert! (no-duplicatesp-equal (known-packages+ state)))

(assert! (member-equal "ACL2" (known-packages+ state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (string-listp (included-books (w state))))

(assert! (no-duplicatesp-equal (included-books (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun latest-event-landmark (wrld)
   (declare (xargs :guard (plist-worldp wrld)))
   (if (endp wrld)
       nil
     (let ((triple (car wrld)))
       (if (eq (car triple) 'event-landmark)
           (cddr triple)
         (latest-event-landmark (cdr wrld))))))
 (assert!
  (pseudo-event-landmark-listp (list (latest-event-landmark (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun latest-command-landmark (wrld)
   (declare (xargs :guard (plist-worldp wrld)))
   (if (endp wrld)
       nil
     (let ((triple (car wrld)))
       (if (eq (car triple) 'command-landmark)
           (cddr triple)
         (latest-command-landmark (cdr wrld))))))
 (comp t) ; seems to be needed for Allegro CL (but isn't for LispWorks; hmm...)
 (assert!
  (pseudo-command-landmark-listp (list (latest-command-landmark (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) '(f)))

(must-succeed*
 (defun f (x) x)
 (verify-guards f)
 (assert-equal (event-landmark-names (cddr (nth 0 (w state)))) nil))

(must-succeed*
 (mutual-recursion
  (defun f (term)
    (if (variablep term)
        0
      (if (fquotep term)
          0
        (1+ (f-lst (fargs term))))))
  (defun f-lst (terms)
    (if (endp terms)
        0
      (+ (f (car terms))
         (f-lst (cdr terms))))))
 (assert-equal (event-landmark-names (cddr (nth 0 (w state))))
               '(f f-lst)))

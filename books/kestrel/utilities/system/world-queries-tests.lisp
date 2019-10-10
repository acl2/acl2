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

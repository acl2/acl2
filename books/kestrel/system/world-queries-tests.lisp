; World Queries -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the world query utilities in world-queries.lisp.

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

(assert-event (macro-symbolp 'append (w state)))

(assert-event (not (macro-symbolp 'cons (w state))))

(assert-event (not (macro-symbolp 'aaaaaaaaaa (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (assert-event (macro-symbolp 'm (w state))))

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

(assert-event (macro-namep 'append (w state)))

(assert-event (not (macro-namep 'cons (w state))))

(assert-event (not (macro-namep 'aaaaaaaaaa (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (assert-event (macro-namep 'm (w state))))

(assert-event (not (macro-namep 5/3 (w state))))

(assert-event (not (macro-namep "append" (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (logical-name-listp '(append "ACL2" car-cdr-elim cons) (w state)))

(assert-event (not (logical-name-listp '(1 2 3) (w state))))

(assert-event (not (logical-name-listp '(cccccccc) (w state))))

(assert-event (not (logical-name-listp "xyz" (w state))))

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

(assert-event (guard-verified-p 'len (w state)))

(assert-event (guard-verified-p 'cons (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards t)) x)
 (assert-event (guard-verified-p 'f (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-event (not (guard-verified-p 'f (w state)))))

(must-succeed*
 (defthm th (acl2-numberp (+ (fix x) (fix y))))
 (verify-guards th)
 (assert-event (guard-verified-p 'th (w state))))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert-event (not (guard-verified-p 'th (w state)))))

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

(must-succeed*
 (defun-nx f (x) (cons (list x) (list x)))
 (assert-event (equal (body 'f nil (w state))
                      '(return-last 'progn
                                    (throw-nonexec-error 'f (cons x 'nil))
                                    (cons (cons x 'nil) (cons x 'nil)))))
 (assert-event (equal (unwrapped-nonexec-body 'f (w state))
                      '(cons (cons x 'nil) (cons x 'nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (no-stobjs-p 'cons (w state)))

(assert-event (no-stobjs-p 'len (w state)))

(assert-event (not (no-stobjs-p 'guard-obligation (w state))))

(must-succeed*
 (defun f (x) x)
 (assert-event (no-stobjs-p 'f (w state))))

(must-succeed*
 (defun f (state) (declare (xargs :stobjs state)) state)
 (assert-event (not (no-stobjs-p 'f (w state)))))

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

(assert-event (equal (measured-subset 'len (w state)) '(x)))

(assert-event (equal (measured-subset 'binary-append (w state)) '(x)))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-event (equal (measured-subset 'f (w state)) '(x))))

(must-succeed*
 (defun f (x y z)
   (declare (xargs :measure (nfix (- 10 y))))
   (if (and (natp y) (< y 10))
       (f x (1+ y) z)
     (cons x z)))
 (assert-event (equal (measured-subset 'f (w state)) '(y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (well-founded-relation 'len (w state)) 'o<))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-event (equal (well-founded-relation 'f (w state)) 'o<)))

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
 (assert-event (equal (well-founded-relation 'f (w state)) 'o<$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (ruler-extenders 'len (w state))
                     '(mv-list return-last)))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-event (equal (ruler-extenders 'f (w state))
                      '(cons))))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders :all))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-event (equal (ruler-extenders 'f (w state))
                      :all)))

(must-succeed*
 (defun fact (n)
   (declare (xargs :ruler-extenders (:lambdas)))
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1)))
 (assert-event (equal (ruler-extenders 'fact (w state))
                      '(:lambdas))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (macro-required-args 'tthm (w state)) '(fn)))

(assert-event (equal (macro-required-args 'list (w state)) nil))

(must-succeed*
 (defmacro m (a) `(list ,a))
 (assert-event (equal (macro-required-args 'm (w state)) '(a))))

(must-succeed*
 (defmacro m (a &key b) `(list ,a ,(or b :default)))
 (assert-event (equal (macro-required-args 'm (w state)) '(a))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (string-listp (included-books (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (let ((im (induction-machine 'len (w state))))
                (and (pseudo-induction-machinep 'len im)
                     (eql (len im) 2)
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
     (if (eql n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert-event (let ((im (induction-machine 'fib (w state))))
                 (and (pseudo-induction-machinep 'fib im)
                      (eql (len im) 3)
                      (let ((im1 (first im)))
                        (and (equal (access tests-and-calls im1 :tests)
                                    '((zp n)))
                             (equal (access tests-and-calls im1 :calls)
                                    nil)))
                      (let ((im2 (second im)))
                        (and (equal (access tests-and-calls im2 :tests)
                                    '((not (zp n))
                                      (eql n '1)))
                             (equal (access tests-and-calls im2 :calls)
                                    nil)))
                      (let ((im3 (third im)))
                        (and (equal (access tests-and-calls im3 :tests)
                                    '((not (zp n))
                                      (not (eql n '1))))
                             (equal (access tests-and-calls im3 :calls)
                                    '((fib (binary-+ '-1 n))
                                      (fib (binary-+ '-2 n))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (pseudo-tests-and-callp (make tests-and-call
                                            :tests '((f x))
                                            :call ''3)))

(assert-event (not (pseudo-tests-and-callp (make tests-and-call
                                                 :tests "a"
                                                 :call 2))))

(assert-event (not (pseudo-tests-and-callp 88)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (pseudo-tests-and-call-listp nil))

(assert-event (pseudo-tests-and-call-listp (list (make tests-and-call
                                                       :tests '((f x))
                                                       :call '(g y z))
                                                 (make tests-and-call
                                                       :tests '('3 x)
                                                       :call ''#\a))))

(assert-event (not (pseudo-tests-and-call-listp (list (make tests-and-call
                                                            :tests 1
                                                            :call 2)
                                                      (make tests-and-call
                                                            :tests "a"
                                                            :call "b")))))

(assert-event (not (pseudo-tests-and-call-listp 88)))

(assert-event (not (pseudo-tests-and-call-listp (make tests-and-call
                                                      :tests 1
                                                      :call 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (let ((rc (recursive-calls 'len (w state))))
                (and (pseudo-tests-and-call-listp rc)
                     (eql (len rc) 1)
                     (let ((rc1 (first rc)))
                       (and  (equal (access tests-and-call rc1 :tests)
                                    '((consp x)))
                             (equal (access tests-and-call rc1 :call)
                                    '(len (cdr x))))))))

(must-succeed*
 (defun fib (n)
   (if (zp n)
       1
     (if (eql n 1)
         1
       (+ (fib (- n 1))
          (fib (- n 2))))))
 (assert-event (let ((rc (recursive-calls 'fib (w state))))
                 (and (pseudo-tests-and-call-listp rc)
                      (eql (len rc) 2)
                      (let ((rc1 (first rc)))
                        (and (equal (access tests-and-call rc1 :tests)
                                    '((not (zp n))
                                      (not (eql n '1))))
                             (equal (access tests-and-call rc1 :call)
                                    '(fib (binary-+ '-1 n)))))
                      (let ((rc2 (second rc)))
                        (and (equal (access tests-and-call rc2 :tests)
                                    '((not (zp n))
                                      (not (eql n '1))))
                             (equal (access tests-and-call rc2 :call)
                                    '(fib (binary-+ '-2 n)))))))))

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
 (assert-event
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
 (assert-event
  (pseudo-command-landmark-listp (list (latest-command-landmark (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) x)
 (assert-event (equal (event-landmark-names (cddr (nth 0 (w state))))
                      '(f))))

(must-succeed*
 (defun f (x) x)
 (verify-guards f)
 (assert-event (equal (event-landmark-names (cddr (nth 0 (w state))))
                      nil)))

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
 (assert-event (equal (event-landmark-names (cddr (nth 0 (w state))))
                      '(f f-lst))))

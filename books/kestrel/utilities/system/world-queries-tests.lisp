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

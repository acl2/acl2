; Integer Arithmetic -- Meta Rule Support
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "meta/term-defuns" :dir :system)
(local (include-book "meta/term-lemmas" :dir :system :load-compiled-file nil))

(include-book "operations")
(local (in-theory (enable binary-i+)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is an adaptation of [books]/meta/meta-plus-equal.lisp,
; authored by Matt Kaufmann and John Cowles,
; to integer arithmetic; specifically.
;
; This book is verbatim equivalent to [books]/meta/meta-plus-equal.lisp,
; with the following substitutions:
;
;   binary-+     --> binary-i+
;   +            --> binary-i+
;   fix          --> ifix
;   acl2-numberp --> integerp
;
; The purpose of this book is to prove
; an analogue of the cancel_plus-equal-correct meta rule,
; for integers.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defevaluator ev-iplus-equal ev-iplus-equal-list
  ((binary-i+ x y)
   (ifix x)
   (equal x y)
   (integerp x)
   (if x y z)))

(defun cancel_iplus-equal$1 (x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (consp x))))

; Not all of

; (and (consp (cadr x))
;      (eq (car (cadr x)) 'binary-+)
;      (consp (caddr x))
;      (eq (car (caddr x)) 'binary-+))

; hold.

  (mv-let
    (elt term)
    (cond ((and (consp (cadr x))
                (eq (car (cadr x)) 'binary-i+))
           (mv (caddr x) (cadr x)))
          ((and (consp (caddr x))
                (eq (car (caddr x)) 'binary-i+))
           (mv (cadr x) (caddr x)))
          (t (mv nil nil)))
    (cond
     ((and elt (fringe-occur 'binary-i+ elt term))
      (list 'if
            (list 'integerp elt)
            (list 'equal
                  *0*
                  (binary-op_tree 'binary-i+
                                  0
                                  'ifix
                                  (del elt (binary-op_fringe 'binary-i+ term))))
            *nil*))
     (t x))))

(defun cancel_iplus-equal (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
	   (eq (car x) 'equal))
      (cond
       ((and (consp (cadr x))
             (eq (car (cadr x)) 'binary-i+)
             (consp (caddr x))
             (eq (car (caddr x)) 'binary-i+))
        (let* ((lt-side (binary-op_fringe 'binary-i+ (cadr x)))
               (rt-side (binary-op_fringe 'binary-i+ (caddr x)))
               (int (bagint lt-side rt-side)))
          (if int
              (list 'equal
                    (binary-op_tree 'binary-i+
                                    0
                                    'ifix
                                    (bagdiff lt-side int))
                    (binary-op_tree 'binary-i+
                                    0
                                    'ifix
                                    (bagdiff rt-side int)))
            x)))
       (t (cancel_iplus-equal$1 x)))
    x))

(local
 (defthm integerp-ev-iplus-equal
   (integerp (ev-iplus-equal (binary-op_tree 'binary-i+ 0 'ifix fringe) a))
   :rule-classes :type-prescription))

(local (in-theory (disable binary-op_tree)))

(local
 (defthm ev-iplus-equal-binary-op_tree-append
   (equal (ev-iplus-equal (binary-op_tree 'binary-i+
                                          0 'ifix
                                          (append fringe1 fringe2))
                          a)
          (binary-i+ (ev-iplus-equal (binary-op_tree 'binary-i+
                                                     0 'ifix
                                                     fringe1)
                                     a)
                     (ev-iplus-equal (binary-op_tree 'binary-i+
                                                     0 'ifix
                                                     fringe2)
                                     a)))
   :hints (("Goal" :induct (append fringe1 fringe2)))))

(local
 (defthm ev-iplus-equal-binary-op_tree-fringe
   (equal (ev-iplus-equal (binary-op_tree 'binary-i+
                                          0 'ifix
                                          (binary-op_fringe 'binary-i+ x))
                          a)
          (ifix (ev-iplus-equal x a)))))

(local
 (defthm iplus-cancel-left
   (equal (equal (binary-i+ x y) (binary-i+ x z))
          (equal (ifix y) (ifix z)))))

(local
 (defthm binary-op_tree-iplus-fringe-del-lemma
   (implies (memb summand fringe)
            (equal (binary-i+ (ev-iplus-equal summand a)
                              (ev-iplus-equal (binary-op_tree 'binary-i+
                                                              0 'ifix
                                                              (del summand fringe))
                                              a))
                   (ev-iplus-equal (binary-op_tree 'binary-i+
                                                   0 'ifix
                                                   fringe)
                                   a)))
   :rule-classes nil
   :hints (("Goal" :expand ((binary-op_tree 'binary-i+
                                            0 'ifix
                                            (cdr fringe)))))))

(local
 (defthm binary-op_tree-iplus-fringe-del
   (implies (and (memb summand fringe)
                 (integerp y))
            (equal (equal y
                          (ev-iplus-equal (binary-op_tree 'binary-i+
                                                          0 'ifix
                                                          (del summand fringe))
                                          a))
                   (equal (binary-i+ y (ev-iplus-equal summand a))
                          (ev-iplus-equal (binary-op_tree 'binary-i+
                                                          0 'ifix
                                                          fringe)
                                          a))))
   :hints (("Goal" :use binary-op_tree-iplus-fringe-del-lemma))))

(local
 (defthm cancel_iplus-equal$1-property
   (implies (and (consp x)
                 (equal (car x) 'equal))
            (equal (ev-iplus-equal (cancel_iplus-equal$1 x) a)
                   (ev-iplus-equal x a)))))

(local
 (in-theory (disable cancel_iplus-equal$1)))

(local
 (encapsulate
   ()

   (local
    (defthm binary-op_tree-opener-extra-1
      (implies (and (consp fringe)
                    (not (consp (cdr fringe))))
               (equal (binary-op_tree 'binary-i+ 0 op fringe)
                      (list op (car fringe))))))

   (defthm cancel_equal-iplus-correct-lemma-1
     (implies (subbagp fringe2 fringe1)
              (equal
               (binary-i+ (ev-iplus-equal (binary-op_tree
                                           'binary-i+
                                           0
                                           'ifix
                                           (bagdiff fringe1 fringe2))
                                          a)
                          (ev-iplus-equal (binary-op_tree
                                           'binary-i+
                                           0
                                           'ifix
                                           fringe2)
                                          a))
               (ev-iplus-equal (binary-op_tree
                                'binary-i+
                                0
                                'ifix
                                fringe1)
                               a)))
     :rule-classes nil)))

(local
 (defthm cancel_equal-iplus-correct-lemma
   (equal
    (equal
     (ev-iplus-equal (binary-op_tree
                      'binary-i+
                      0
                      'ifix
                      (bagdiff (binary-op_fringe 'binary-i+ x1)
                               (bagint (binary-op_fringe 'binary-i+ x1)
                                       (binary-op_fringe 'binary-i+ x2))))
                     a)
     (ev-iplus-equal (binary-op_tree
                      'binary-i+
                      0
                      'ifix
                      (bagdiff (binary-op_fringe 'binary-i+ x2)
                               (bagint (binary-op_fringe 'binary-i+ x1)
                                       (binary-op_fringe 'binary-i+ x2))))
                     a))
    (equal (ifix (ev-iplus-equal x1 a))
           (ifix (ev-iplus-equal x2 a))))
   :hints (("Goal" :use
            ((:instance cancel_equal-iplus-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-i+ x1))
                        (fringe2 (bagint (binary-op_fringe 'binary-i+ x1)
                                         (binary-op_fringe 'binary-i+ x2))))
             (:instance cancel_equal-iplus-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-i+ x2))
                        (fringe2 (bagint (binary-op_fringe 'binary-i+ x1)
                                         (binary-op_fringe 'binary-i+ x2)))))))))

(defthm cancel_iplus-equal-correct
  (equal (ev-iplus-equal x a)
         (ev-iplus-equal (cancel_iplus-equal x) a))
  :rule-classes ((:meta :trigger-fns (equal))))

; ACL2 books on arithmetic metafunctions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann and John Cowles
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "term-defuns")

(local (include-book "term-lemmas"
                     :load-compiled-file nil))

(local (include-book "arithmetic/equalities" :dir :system
                     :load-compiled-file nil))

(defevaluator ev-times-equal ev-times-equal-list
  ((binary-* x y)
   (fix x)
   (equal x y)
   (acl2-numberp x)
   (if x y z)))

(defun cancel_times-equal$1 (x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (consp x))))

; Not all of

; (and (consp (cadr x))
;      (eq (car (cadr x)) 'binary-*)
;      (consp (caddr x))
;      (eq (car (caddr x)) 'binary-*))

; hold.

  (mv-let
   (elt term)
   (cond ((and (consp (cadr x))
               (eq (car (cadr x)) 'binary-*))
          (mv (caddr x) (cadr x)))
         ((and (consp (caddr x))
               (eq (car (caddr x)) 'binary-*))
          (mv (cadr x) (caddr x)))
         (t (mv nil nil)))
   (cond
    ((and elt (fringe-occur 'binary-* elt term))
     (list 'if
           (list 'acl2-numberp elt)
           (list 'if
                 (list 'equal elt *0*)
                 *t*
                 (list 'equal
                       *1*
                       (binary-op_tree
                        'binary-*
                        1
                        'fix
                        (del elt (binary-op_fringe 'binary-* term)))))
           *nil*))
    (t x))))

(defun formal-some-zerop (lst)
  (declare (xargs :guard (and (consp lst)
                              (true-listp lst))))
  (cond
   ((endp (cdr lst))
    (list 'equal *0* (list 'fix (car lst))))
   ((memb (car lst) (cdr lst))
    (formal-some-zerop (cdr lst)))
   (t (list 'if
            (list 'equal *0* (list 'fix (car lst)))
            *t*
            (formal-some-zerop (cdr lst))))))

(defun cancel_times-equal (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
	   (eq (car x) 'equal))
      (cond
       ((and (consp (cadr x))
             (eq (car (cadr x)) 'binary-*)
             (consp (caddr x))
             (eq (car (caddr x)) 'binary-*))
        (let* ((lt-side (binary-op_fringe 'binary-* (cadr x)))
               (rt-side (binary-op_fringe 'binary-* (caddr x)))
               (int (bagint lt-side rt-side)))
          (if int
              (list 'if
                    (formal-some-zerop int)
                    *t*
                    (list 'equal
                          (binary-op_tree 'binary-*
                                          1
                                          'fix
                                          (bagdiff lt-side int))
                          (binary-op_tree 'binary-*
                                          1
                                          'fix
                                          (bagdiff rt-side int))))
            x)))
       (t (cancel_times-equal$1 x)))
    x))

(local
 (defthm acl2-numberp-ev-times-equal
   (acl2-numberp (ev-times-equal (binary-op_tree 'binary-* 1 'fix fringe) a))
   :rule-classes :type-prescription))

(local (in-theory (disable binary-op_tree)))

(local
 (defthm ev-times-equal-binary-op_tree-append
   (equal (ev-times-equal (binary-op_tree 'binary-*
                                         1 'fix
                                         (append fringe1 fringe2))
                         a)
          (* (ev-times-equal (binary-op_tree 'binary-*
                                            1 'fix
                                            fringe1)
                            a)
             (ev-times-equal (binary-op_tree 'binary-*
                                            1 'fix
                                            fringe2)
                            a)))
   :hints (("Goal" :induct (append fringe1 fringe2)))))

(local
 (defthm ev-times-equal-binary-op_tree-fringe
   (equal (ev-times-equal (binary-op_tree 'binary-*
                                         1 'fix
                                         (binary-op_fringe 'binary-* x))
                         a)
          (fix (ev-times-equal x a)))))

(local
 (defthm times-cancel-left
   (equal (equal (* x y) (* x z))
          (or (equal (fix x) 0)
              (equal (fix y) (fix z))))))

(local
 (defthm binary-op_tree-times-fringe-del-lemma
   (implies (memb summand fringe)
            (equal (* (ev-times-equal summand a)
                      (ev-times-equal (binary-op_tree 'binary-*
                                                     1 'fix
                                                     (del summand fringe))
                                     a))
                   (ev-times-equal (binary-op_tree 'binary-*
                                                  1 'fix
                                                  fringe)
                                  a)))
   :rule-classes nil
   :hints (("Goal" :expand ((binary-op_tree 'binary-*
                                            1 'fix
                                            (cdr fringe)))))))

(local
 (encapsulate
  ()

  (local
   (defthm times-cancel-left-better
     (implies (equal left (* x y))
              (equal (equal left (* x z))
                     (or (equal (fix x) 0)
                         (equal (fix y) (fix z)))))))

  (defthm binary-op_tree-times-fringe-del
    (implies (and (memb summand fringe)
                  (acl2-numberp y)
                  (not (equal (fix (ev-times-equal summand a)) 0)))
             (equal (equal y
                           (ev-times-equal (binary-op_tree 'binary-*
                                                           1 'fix
                                                           (del summand fringe))
                                           a))
                    (equal (* (ev-times-equal summand a) y)
                           (ev-times-equal (binary-op_tree 'binary-*
                                                           1 'fix
                                                           fringe)
                                           a))))
    :hints (("Goal" :use binary-op_tree-times-fringe-del-lemma
             :in-theory (disable commutativity-of-*))))))

(local
 (defthm memb-of-fringe-non-zero
   (implies (and (memb x (binary-op_fringe 'binary-* term))
                 (acl2-numberp (ev-times-equal term a))
                 (not (equal (ev-times-equal term a) 0)))
            (and (not (equal (ev-times-equal x a) 0))
                 (acl2-numberp (ev-times-equal x a))))))

(local
 (defthm cancel_times-equal$1-property
   (implies (and (consp x)
                 (equal (car x) 'equal))
            (equal (ev-times-equal (cancel_times-equal$1 x) a)
                   (ev-times-equal x a)))))

(local
 (in-theory (disable cancel_times-equal$1)))

(local
 (defthm ev-times-equal-binary-op_tree-is-zero
   (implies (and (memb x fringe)
                 (equal (fix (ev-times-equal x a)) 0))
            (equal (ev-times-equal (binary-op_tree 'binary-* 1 'fix fringe)
                                   a)
                   0))))

(local
 (defthm ev-times-equal-binary-op_tree-is-zero-from-del
   (implies (equal (ev-times-equal (binary-op_tree 'binary-* 1 'fix (del x fringe))
                                   a)
                   0)
            (equal (ev-times-equal (binary-op_tree 'binary-* 1 'fix fringe)
                                   a)
                   0))
   :hints (("Goal" :expand ((binary-op_tree 'binary-* 1 'fix fringe)
                            (binary-op_tree 'binary-* 1 'fix (cdr fringe)))))))

(local
 (encapsulate
  ()

  (local
   (defthm binary-op_tree-opener-extra-1
     (implies (and (consp fringe)
                   (not (consp (cdr fringe))))
              (equal (binary-op_tree 'binary-* 1 op fringe)
                     (list op (car fringe))))))

  (local
   (defthm cancel_equal-times-correct-lemma-1-lemma
     (implies (memb x fringe)
              (equal (* (ev-times-equal x a)
                        (ev-times-equal (binary-op_tree 'binary-*
                                                        1 'fix
                                                        (del x fringe))
                                        a))
                     (fix (ev-times-equal (binary-op_tree 'binary-*
                                                          1 'fix
                                                          fringe)
                                          a))))
     :hints (("Goal" :use
              ((:instance
                binary-op_tree-times-fringe-del
                (summand x)
                (y (ev-times-equal (binary-op_tree 'binary-*
                                                   1 'fix
                                                   (del x fringe))
                                   a))
                (fringe fringe)
                (a a)))
              :in-theory (disable binary-op_tree-times-fringe-del)))))

  (defthm cancel_equal-times-correct-lemma-1
    (implies (subbagp fringe2 fringe1)
             (equal
              (* (ev-times-equal (binary-op_tree
                                  'binary-*
                                  1
                                  'fix
                                  fringe2)
                                 a)
                 (ev-times-equal (binary-op_tree
                                  'binary-*
                                  1
                                  'fix
                                  (bagdiff fringe1 fringe2))
                                 a))
              (ev-times-equal (binary-op_tree
                               'binary-*
                               1
                               'fix
                               fringe1)
                              a)))
    :hints (("Goal" :expand ((binary-op_tree 'binary-*
                                             1 'fix
                                             fringe2)))))))

(local
 (encapsulate
  ()

  (local
   (defthm times-cancel-right-left-better
     (implies (equal left (* y x))
              (equal (equal left (* x z))
                     (or (equal (fix x) 0)
                         (equal (fix y) (fix z)))))))

  (defthm cancel_equal-times-correct-lemma-2
    (implies (and (subbagp fringe2 fringe1)
                  (not (equal (ev-times-equal
                               (binary-op_tree
                                'binary-*
                                1
                                'fix
                                fringe2)
                               a)
                              0))
                  (acl2-numberp y))
             (equal
              (equal y
                     (ev-times-equal (binary-op_tree
                                      'binary-*
                                      1
                                      'fix
                                      (bagdiff fringe1 fringe2))
                                     a))
              (equal (* (ev-times-equal
                         (binary-op_tree
                          'binary-*
                          1
                          'fix
                          fringe2)
                         a)
                        y)
                     (ev-times-equal (binary-op_tree
                                      'binary-*
                                      1
                                      'fix
                                      fringe1)
                                     a))))
    :hints (("Goal" :use cancel_equal-times-correct-lemma-1
             :in-theory (disable cancel_equal-times-correct-lemma-1))))))

(local
 (defthm acl2-numberp-ev-times-equal-again
   (acl2-numberp (ev-times-equal (cons 'binary-* x8)
                                 a))
   :rule-classes :type-prescription))

(local
 (defthm ev-times-equal-binary-op_tree-is-zero-alternate
   (implies (and (memb x fringe)
                 (equal (fix (ev-times-equal x a)) 0))
            (ev-times-equal (formal-some-zerop fringe)
                            a))))

(local
 (defthm ev-times-equal-formal-some-zerop-0
   (implies (consp fringe)
            (equal (ev-times-equal
                    (formal-some-zerop fringe)
                    a)
                   (equal
                    (fix (ev-times-equal (binary-op_tree 'binary-*
                                                         1 'fix
                                                         fringe)
                                         a))
                    0)))
   :hints (("Goal" :expand ((binary-op_tree 'binary-* 1 'fix fringe))
            :restrict ((ev-times-equal-binary-op_tree-is-zero-alternate
                        ((x (car fringe)))))))))

(local
 (defthm consp-bagint
   (iff (consp (bagint x y))
        (bagint x y))))

(local
 (defthm cancel_equal-times-correct-lemma
   (let ((int (bagint (binary-op_fringe 'binary-* x1)
                      (binary-op_fringe 'binary-* x2))))
     (implies
      (and int
           (not (ev-times-equal (formal-some-zerop int) a)))
      (equal
       (equal
        (ev-times-equal (binary-op_tree
                         'binary-*
                         1
                         'fix
                         (bagdiff (binary-op_fringe 'binary-* x1)
                                  int))
                        a)
        (ev-times-equal (binary-op_tree
                         'binary-*
                         1
                         'fix
                         (bagdiff (binary-op_fringe 'binary-* x2)
                                  int))
                        a))
       (equal (fix (ev-times-equal x1 a))
              (fix (ev-times-equal x2 a))))))
   :hints (("Goal" :use
            ((:instance cancel_equal-times-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-* x1))
                        (fringe2 (bagint (binary-op_fringe 'binary-* x1)
                                         (binary-op_fringe 'binary-* x2))))
             (:instance cancel_equal-times-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-* x2))
                        (fringe2 (bagint (binary-op_fringe 'binary-* x1)
                                         (binary-op_fringe 'binary-* x2)))))))))
(local
 (defthm formal-some-zerop-bagint-yields-0
   (implies
    (and (ev-times-equal (formal-some-zerop fringe)
                         a)
         (subbagp fringe (binary-op_fringe 'binary-*
                                           term))
         (acl2-numberp (ev-times-equal term a))
         (consp fringe))
    (equal (ev-times-equal term a)
           0))))

(defthm cancel_times-equal-correct
  (equal (ev-times-equal x a)
         (ev-times-equal (cancel_times-equal x) a))
  :rule-classes ((:meta :trigger-fns (equal)))
  :hints (("Goal" :in-theory (disable ev-times-equal-constraint-8
                                      ev-times-equal-formal-some-zerop-0))))

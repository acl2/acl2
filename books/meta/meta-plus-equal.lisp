; ACL2 books on arithmetic metafunctions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann and John Cowles
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "term-defuns")

(local (include-book "term-lemmas" :load-compiled-file nil))

(defevaluator ev-plus-equal ev-plus-equal-list
  ((binary-+ x y)
   (fix x)
   (equal x y)
   (acl2-numberp x)
   (if x y z)))

(defun cancel_plus-equal$1 (x)
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
               (eq (car (cadr x)) 'binary-+))
          (mv (caddr x) (cadr x)))
         ((and (consp (caddr x))
               (eq (car (caddr x)) 'binary-+))
          (mv (cadr x) (caddr x)))
         (t (mv nil nil)))
   (cond
    ((and elt (fringe-occur 'binary-+ elt term))
     (list 'if
           (list 'acl2-numberp elt)
           (list 'equal
                 *0*
                 (binary-op_tree 'binary-+
                                 0
                                 'fix
                                 (del elt (binary-op_fringe 'binary-+ term))))
           *nil*))
    (t x))))

(defun cancel_plus-equal (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
	   (eq (car x) 'equal))
      (cond
       ((and (consp (cadr x))
             (eq (car (cadr x)) 'binary-+)
             (consp (caddr x))
             (eq (car (caddr x)) 'binary-+))
        (let* ((lt-side (binary-op_fringe 'binary-+ (cadr x)))
               (rt-side (binary-op_fringe 'binary-+ (caddr x)))
               (int (bagint lt-side rt-side)))
          (if int
              (list 'equal
                    (binary-op_tree 'binary-+
                                    0
                                    'fix
                                    (bagdiff lt-side int))
                    (binary-op_tree 'binary-+
                                    0
                                    'fix
                                    (bagdiff rt-side int)))
            x)))
       (t (cancel_plus-equal$1 x)))
    x))

(local
 (defthm acl2-numberp-ev-plus-equal
   (acl2-numberp (ev-plus-equal (binary-op_tree 'binary-+ 0 'fix fringe) a))
   :rule-classes :type-prescription))

(local (in-theory (disable binary-op_tree)))

(local
 (defthm ev-plus-equal-binary-op_tree-append
   (equal (ev-plus-equal (binary-op_tree 'binary-+
                                         0 'fix
                                         (append fringe1 fringe2))
                         a)
          (+ (ev-plus-equal (binary-op_tree 'binary-+
                                            0 'fix
                                            fringe1)
                            a)
             (ev-plus-equal (binary-op_tree 'binary-+
                                            0 'fix
                                            fringe2)
                            a)))
   :hints (("Goal" :induct (append fringe1 fringe2)))))

(local
 (defthm ev-plus-equal-binary-op_tree-fringe
   (equal (ev-plus-equal (binary-op_tree 'binary-+
                                         0 'fix
                                         (binary-op_fringe 'binary-+ x))
                         a)
          (fix (ev-plus-equal x a)))))

(local
 (defthm plus-cancel-left
   (equal (equal (+ x y) (+ x z))
          (equal (fix y) (fix z)))))

(local
 (defthm binary-op_tree-plus-fringe-del-lemma
   (implies (memb summand fringe)
            (equal (+ (ev-plus-equal summand a)
                      (ev-plus-equal (binary-op_tree 'binary-+
                                                     0 'fix
                                                     (del summand fringe))
                                     a))
                   (ev-plus-equal (binary-op_tree 'binary-+
                                                  0 'fix
                                                  fringe)
                                  a)))
   :rule-classes nil
   :hints (("Goal" :expand ((binary-op_tree 'binary-+
                                            0 'fix
                                            (cdr fringe)))))))

(local
 (defthm binary-op_tree-plus-fringe-del
   (implies (and (memb summand fringe)
                 (acl2-numberp y))
            (equal (equal y
                          (ev-plus-equal (binary-op_tree 'binary-+
                                                         0 'fix
                                                         (del summand fringe))
                                         a))
                   (equal (+ y (ev-plus-equal summand a))
                          (ev-plus-equal (binary-op_tree 'binary-+
                                                         0 'fix
                                                         fringe)
                                         a))))
   :hints (("Goal" :use binary-op_tree-plus-fringe-del-lemma))))

(local
 (defthm cancel_plus-equal$1-property
   (implies (and (consp x)
                 (equal (car x) 'equal))
            (equal (ev-plus-equal (cancel_plus-equal$1 x) a)
                   (ev-plus-equal x a)))))

(local
 (in-theory (disable cancel_plus-equal$1)))

(local
 (encapsulate
  ()

  (local
   (defthm binary-op_tree-opener-extra-1
     (implies (and (consp fringe)
                   (not (consp (cdr fringe))))
              (equal (binary-op_tree 'binary-+ 0 op fringe)
                     (list op (car fringe))))))

  (defthm cancel_equal-plus-correct-lemma-1
    (implies (subbagp fringe2 fringe1)
             (equal
              (+ (ev-plus-equal (binary-op_tree
                                 'binary-+
                                 0
                                 'fix
                                 (bagdiff fringe1 fringe2))
                                a)
                 (ev-plus-equal (binary-op_tree
                                 'binary-+
                                 0
                                 'fix
                                 fringe2)
                                a))
              (ev-plus-equal (binary-op_tree
                              'binary-+
                              0
                              'fix
                              fringe1)
                             a)))
    :rule-classes nil)))

(local
 (defthm cancel_equal-plus-correct-lemma
   (equal
    (equal
     (ev-plus-equal (binary-op_tree
                     'binary-+
                     0
                     'fix
                     (bagdiff (binary-op_fringe 'binary-+ x1)
                              (bagint (binary-op_fringe 'binary-+ x1)
                                      (binary-op_fringe 'binary-+ x2))))
                    a)
     (ev-plus-equal (binary-op_tree
                     'binary-+
                     0
                     'fix
                     (bagdiff (binary-op_fringe 'binary-+ x2)
                              (bagint (binary-op_fringe 'binary-+ x1)
                                      (binary-op_fringe 'binary-+ x2))))
                    a))
    (equal (fix (ev-plus-equal x1 a))
           (fix (ev-plus-equal x2 a))))
   :hints (("Goal" :use
            ((:instance cancel_equal-plus-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-+ x1))
                        (fringe2 (bagint (binary-op_fringe 'binary-+ x1)
                                         (binary-op_fringe 'binary-+ x2))))
             (:instance cancel_equal-plus-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-+ x2))
                        (fringe2 (bagint (binary-op_fringe 'binary-+ x1)
                                         (binary-op_fringe 'binary-+ x2)))))))))

(defthm cancel_plus-equal-correct
  (equal (ev-plus-equal x a)
         (ev-plus-equal (cancel_plus-equal x) a))
  :rule-classes ((:meta :trigger-fns (equal))))

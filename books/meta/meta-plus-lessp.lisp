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

(defevaluator ev-plus-lessp ev-plus-lessp-list
  ((binary-+ x y)
   (< x y)
   (if x y z)))

(defun cancel_plus-lessp$1 (x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (consp x)
                              (not (equal (car x) 'quote)))
                  :guard-hints (("Goal" :expand
                                 ((pseudo-termp
                                   (list* x1 (cons 'binary-+ x6) x4)))))))
  (cond ((and (consp (cadr x))
              (eq (car (cadr x)) 'binary-+))
         (cond
          ((fringe-occur 'binary-+ (caddr x) (cadr x))
           (list '<
                 (binary-op_tree-simple
                  'binary-+
                  0
                  (del (caddr x) (binary-op_fringe 'binary-+ (cadr x))))
                 *0*))
          (t x)))
        ((and (consp (caddr x))
              (eq (car (caddr x)) 'binary-+))
         (cond
          ((fringe-occur 'binary-+ (cadr x) (caddr x))
           (list '<
                 *0*
                 (binary-op_tree-simple
                  'binary-+
                  0
                  (del (cadr x) (binary-op_fringe 'binary-+ (caddr x))))))
          (t x)))
        (t x)))

(defun cancel_plus-lessp (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
	   (eq (car x) '<))
      (cond
       ((and (consp (cadr x))
             (eq (car (cadr x)) 'binary-+)
             (consp (caddr x))
             (eq (car (caddr x)) 'binary-+))
        (let* ((lt-side (binary-op_fringe 'binary-+ (cadr x)))
               (rt-side (binary-op_fringe 'binary-+ (caddr x)))
               (int (bagint lt-side rt-side)))
          (if int
              (list '<
                    (binary-op_tree-simple 'binary-+
                                           0
                                           (bagdiff lt-side int))
                    (binary-op_tree-simple 'binary-+
                                           0
                                           (bagdiff rt-side int)))
            x)))
       (t (cancel_plus-lessp$1 x)))
    x))

(local (in-theory (disable binary-op_tree-simple)))

(local
 (defthm ev-plus-lessp-binary-op_tree-simple-append
   (implies (and (consp fringe1) (consp fringe2))
            (equal (ev-plus-lessp (binary-op_tree-simple 'binary-+
                                                         0
                                                         (append fringe1 fringe2))
                                  a)
                   (+ (ev-plus-lessp (binary-op_tree-simple 'binary-+
                                                            0
                                                            fringe1)
                                     a)
                      (ev-plus-lessp (binary-op_tree-simple 'binary-+
                                                            0
                                                            fringe2)
                                     a))))
   :hints (("Goal" :induct (append fringe1 fringe2)))))

(local
 (defthm ev-plus-lessp-binary-op_tree-simple-fringe
   (equal (ev-plus-lessp (binary-op_tree-simple
                          'binary-+
                          0
                          (binary-op_fringe 'binary-+ x))
                         a)
          (ev-plus-lessp x a))))

(local (defthm equal-iff
         (implies (and (booleanp x) (booleanp y))
                  (iff (equal x y)
                       (iff x y)))))

(local
 (defthm plus-cancel-left
   (equal (< (+ x y) (+ x z))
          (< (fix y) (fix z)))))

(local
 (defthm binary-op_tree-simple-plus-fringe-del-lemma
   (implies (memb summand fringe)
            (equal (+ (ev-plus-lessp summand a)
                      (ev-plus-lessp (binary-op_tree-simple
                                      'binary-+
                                      0
                                      (del summand fringe))
                                     a))
                   (fix (ev-plus-lessp (binary-op_tree-simple
                                        'binary-+ 0 fringe)
                                       a))))
   :rule-classes nil
   :hints (("Goal" :expand ((binary-op_tree-simple 'binary-+
                                                   0
                                                   (cdr fringe)))))))

(local
 (defthm binary-op_tree-simple-plus-fringe-del-1
   (implies (memb summand fringe)
            (equal (< y
                      (ev-plus-lessp (binary-op_tree-simple
                                      'binary-+
                                      0
                                      (del summand fringe))
                                     a))
                   (< (+ y (ev-plus-lessp summand a))
                      (ev-plus-lessp (binary-op_tree-simple
                                      'binary-+ 0 fringe)
                                     a))))
   :hints (("Goal" :use binary-op_tree-simple-plus-fringe-del-lemma))))

(local
 (defthm binary-op_tree-simple-plus-fringe-del-2
   (implies (memb summand fringe)
            (equal (< (ev-plus-lessp (binary-op_tree-simple
                                      'binary-+
                                      0
                                      (del summand fringe))
                                     a)
                      y)
                   (< (ev-plus-lessp (binary-op_tree-simple
                                      'binary-+ 0 fringe)
                                     a)
                      (+ y (ev-plus-lessp summand a)))))
   :hints (("Goal" :use binary-op_tree-simple-plus-fringe-del-lemma))))

(local
 (defthm cancel_plus-lessp$1-property
   (implies (and (consp x)
                 (equal (car x) '<))
            (equal (ev-plus-lessp (cancel_plus-lessp$1 x) a)
                   (ev-plus-lessp x a)))))

(local
 (in-theory (disable cancel_plus-lessp$1)))

(local
 (defthm binary-op_tree-simple-plus-fringe-del
   (implies (and (memb summand fringe)
                 (acl2-numberp y))
            (equal (equal y
                          (ev-plus-lessp (binary-op_tree-simple
                                          'binary-+
                                          0
                                          (del summand fringe))
                                         a))
                   (and (acl2-numberp (ev-plus-lessp (binary-op_tree-simple
                                                      'binary-+
                                                      0
                                                      (del summand fringe))
                                                     a))
                        (equal (+ y (ev-plus-lessp summand a))
                               (fix (ev-plus-lessp (binary-op_tree-simple
                                                    'binary-+ 0 fringe)
                                                   a))))))
   :hints (("Goal" :use binary-op_tree-simple-plus-fringe-del-lemma))))

(local
 (defthm binary-op_tree-simple-plus-fringe-del-not-acl2-numberp
   (implies (and (not (acl2-numberp
                       (ev-plus-lessp (binary-op_tree-simple
                                       'binary-+
                                       0
                                       (del summand fringe))
                                      a)))
                 (memb summand fringe))
            (equal (ev-plus-lessp
                    (binary-op_tree-simple
                     'binary-+
                     0
                     fringe)
                    a)
                   (fix (ev-plus-lessp summand a))))
   :hints (("Goal" :expand ((del summand fringe)
                            (del summand (cdr fringe))
                            (binary-op_tree-simple 'binary-+
                                                   0 fringe))))))

(local
 (encapsulate
  ()

  (local
   (defthm binary-op_tree-simple-opener-extra-1
     (implies (and (consp fringe)
                   (not (consp (cdr fringe))))
              (equal (binary-op_tree-simple 'binary-+ 0 fringe)
                     (car fringe)))))

  (defthm cancel_plus-lessp-correct-lemma-1
    (implies (subbagp fringe2 fringe1)
             (equal
              (+ (ev-plus-lessp (binary-op_tree-simple
                                 'binary-+
                                 0
                                 (bagdiff fringe1 fringe2))
                                a)
                 (ev-plus-lessp (binary-op_tree-simple
                                 'binary-+
                                 0
                                 fringe2)
                                a))
              (fix (ev-plus-lessp (binary-op_tree-simple
                                   'binary-+
                                   0
                                   fringe1)
                                  a))))
    :rule-classes nil)))

(local
 (defthm cancel_plus-lessp-correct-lemma
   (equal
    (<
     (ev-plus-lessp (binary-op_tree-simple
                     'binary-+
                     0
                     (bagdiff (binary-op_fringe 'binary-+ x1)
                              (bagint (binary-op_fringe 'binary-+ x1)
                                      (binary-op_fringe 'binary-+ x2))))
                    a)
     (ev-plus-lessp (binary-op_tree-simple
                     'binary-+
                     0
                     (bagdiff (binary-op_fringe 'binary-+ x2)
                              (bagint (binary-op_fringe 'binary-+ x1)
                                      (binary-op_fringe 'binary-+ x2))))
                    a))
    (< (ev-plus-lessp x1 a)
       (ev-plus-lessp x2 a)))
   :hints (("Goal" :use
            ((:instance cancel_plus-lessp-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-+ x1))
                        (fringe2 (bagint (binary-op_fringe 'binary-+ x1)
                                         (binary-op_fringe 'binary-+ x2))))
             (:instance cancel_plus-lessp-correct-lemma-1
                        (fringe1 (binary-op_fringe 'binary-+ x2))
                        (fringe2 (bagint (binary-op_fringe 'binary-+ x1)
                                         (binary-op_fringe 'binary-+ x2)))))))))

(defthm cancel_plus-lessp-correct
  (equal (ev-plus-lessp x a)
         (ev-plus-lessp (cancel_plus-lessp x) a))
  :rule-classes ((:meta :trigger-fns (<))))

;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; The output of the decrement/pass unit is either the input, or the input
;; decremented by 1.  This unit computes A - C, where A is the input vector,
;; and C is a 1-bit control signal representing 1 or 0.

(in-package "FM9001")

(include-book "de")
(include-book "macros")
(include-book "pg-theory")
(include-book "tree-number")

;; ======================================================================

;; TV-DEC-PASS is a Boolean specification for a decrement/pass unit with a
;; carry-lookahead structure specified by the TREE input.  Carry-lookahead is
;; based on a single generate bit.  The CAR of the output vector is the
;; generate bit, and the CDR of the output vector is A if C is high, else A -
;; 1.  Note that the parity of C is opposite from that specified above.

(defun tv-dec-pass (c a tree)
  (declare (xargs :guard (true-listp a)))
  (if (atom tree)
      (list (b-buf (car a))
            (b-equv (car a) c))
    (let ((lhs (tv-dec-pass c (tfirstn a tree) (car tree))))
      (let ((rhs (tv-dec-pass (b-or c (car lhs)) (trestn a tree) (cdr tree))))
        (cons (b-or (car lhs) (car rhs))
              (append (cdr lhs) (cdr rhs)))))))

(defthm len-cdr-tv-dec-pass
  (equal (len (cdr (tv-dec-pass c a tree)))
         (tree-size tree))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm len-tv-dec-pass
  (equal (len (tv-dec-pass c a tree))
         (1+ (tree-size tree))))

(defthm bvp-cdr-tv-dec-pass
  (bvp (cdr (tv-dec-pass c a tree)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-tv-dec-pass
  (bvp (tv-dec-pass c a tree))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-len-tv-dec-pass
  (equal (bvp-len (tv-dec-pass c a tree) n)
         (<= n (1+ (tree-size tree))))
  :hints (("Goal" :in-theory (enable bvp-len)))
; Matt K. mod: This was originally a linear rule, but after 6/4/2021 it is
; illegal as a linear rule.  It was presumably useless anyhow, since it
; was treated as the conjunction of
; (<= (bvp-len (tv-dec-pass c a tree) n) (<= n (1+ (tree-size tree))))
; and
; (>= (bvp-len (tv-dec-pass c a tree) n) (<= n (1+ (tree-size tree))))
  :rule-classes nil)

(defthmd tv-dec-pass-crock-1
  (implies (and (equal (len a) (tree-size tree))
                (bvp a))
           (equal (tv-adder c (v-not (nat-to-v 0 (len a))) a tree)
                  (cons t (tv-dec-pass c a tree))))
  :hints (("Goal"
           :in-theory (e/d (tv-adder
                            take-v-not
                            nthcdr-v-not
                            t-carry)
                           (v-not-take
                            v-not-nthcdr)))))

(defthm tv-dec-pass-crock-2
  (implies (and (equal (len a) (tree-size tree))
                (bvp a))
           (equal (cdr (tv-dec-pass c a tree))
                  (cdr (cdr (tv-adder c (v-not (nat-to-v 0 (len a)))
                                      a tree)))))
  :hints (("Goal" :in-theory (enable tv-dec-pass-crock-1))))

(defthm tv-dec-pass-works
  (implies (and (equal (len a) (tree-size tree))
                (bvp a))
           (equal (cdr (tv-dec-pass c a tree))
                  (if c
                      (v-buf a)
                    (v-dec a))))
  :hints (("Goal" :in-theory (enable v-dec tv-adder-as-p-g-sum))))

(in-theory (disable tv-dec-pass))

;; ======================================================================

;;   TV-DEC-PASS-NG

;; The generate bit is of no consequence at the top level.  We want to capture
;; the specification of a dec/pass unit that only produces a generate bit when
;; necessary.  TV-DEC-PASS-NG only produces a generate bit when MAKE-G is T.

(defun tv-dec-pass-ng (c a tree make-g)
  (declare (xargs :guard (true-listp a)))
  (if (atom tree)
      (if make-g
          (list (b-buf (car a)) (b-equv (car a) c))
        (list (b-equv (car a) c)))
    (let ((lhs (tv-dec-pass-ng c
                               (tfirstn a tree)
                               (car tree)
                               t)))
      (let ((rhs (tv-dec-pass-ng (b-or c (car lhs))
                                 (trestn a tree)
                                 (cdr tree)
                                 make-g)))
        (if make-g
            (cons (b-or (car lhs) (car rhs))
                  (append (cdr lhs) (cdr rhs)))
          (append (cdr lhs) rhs))))))

;; (defthm tv-dec-pass-ng-congruence
;;   (implies make-g
;;            (equal (equal (tv-dec-pass-ng c a tree make-g)
;;                          (tv-dec-pass-ng c a tree t))
;;                   t)))

(defthm len-tv-dec-pass-ng
  (equal (len (tv-dec-pass-ng c a tree make-g))
         (if make-g
             (1+ (tree-size tree))
           (tree-size tree)))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm len-cdr-tv-dec-pass-ng
  (implies make-g
           (equal (len (cdr (tv-dec-pass-ng c a tree make-g)))
                  (tree-size tree)))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm bvp-tv-dec-pass-ng
  (bvp (tv-dec-pass-ng c a tree make-g))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-cdr-tv-dec-pass-ng
  (bvp (cdr (tv-dec-pass-ng c a tree make-g)))
  :hints (("Goal"
           :use bvp-tv-dec-pass-ng
           :in-theory (e/d (bvp)
                           (bvp-tv-dec-pass-ng))))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-len-tv-dec-pass-ng
  (equal (bvp-len (tv-dec-pass-ng c a tree make-g) n)
         (if make-g
             (<= n (1+ (tree-size tree)))
           (<= n (tree-size tree))))
  :hints (("Goal" :in-theory (enable bvp-len)))
; Matt K. mod: This was originally a linear rule, but after 6/4/2021 it is
; illegal as a linear rule.  It was presumably useless anyhow, since it
; was treated as the conjunction of
;   (<= (bvp-len (tv-dec-pass-ng c a tree make-g) n)
;       (if make-g
;           (<= n (1+ (tree-size tree)))
;         (<= n (tree-size tree))))
; and
;   (>= (bvp-len (tv-dec-pass-ng c a tree make-g) n)
;       (if make-g
;           (<= n (1+ (tree-size tree)))
;         (<= n (tree-size tree)))).
  :rule-classes nil)

(defthmd tv-dec-pass-ng-is-tv-dec-pass-when-make-g
  (implies make-g
           (equal (tv-dec-pass-ng c a tree make-g)
                  (tv-dec-pass c a tree)))
  :hints (("Goal"
           :in-theory (e/d (tv-dec-pass)
                           (b-or tfirstn trestn)))))

(defthm tv-dec-pass-ng-rewrite-tv-dec-pass
  (equal (tv-dec-pass-ng c a tree make-g)
         (if make-g
             (tv-dec-pass c a tree)
           (cdr (tv-dec-pass c a tree))))
  :hints (("Goal"
           :in-theory (e/d (tv-dec-pass-ng-is-tv-dec-pass-when-make-g
                            tv-dec-pass)
                           (b-or tfirstn trestn)))))

(defthm booleanp-car-tv-dec-pass-ng
  (booleanp (car (tv-dec-pass-ng c a tree make-g)))
  :rule-classes :type-prescription)

(in-theory (disable tv-dec-pass-ng))

(defthm tv-dec-pass-ng-works-1
  (implies (and (bvp a)
                (equal (len a)
                       (tree-size tree))
                make-g)
           (equal (cdr (tv-dec-pass-ng c a tree make-g))
                  (if c
                      (v-buf a)
                    (v-dec a)))))

(defthm tv-dec-pass-ng-works-2
  (implies (and (bvp a)
                (equal (len a)
                       (tree-size tree))
                (not make-g))
           (equal (tv-dec-pass-ng c a tree make-g)
                  (if c
                      (v-buf a)
                    (v-dec a)))))

;; ======================================================================

;; F$TV-DEC-PASS-NG

;; F$TV-DEC-PASS-NG is the 4-valued equivalent of TV-DEC-PASS-NG.

(defun f$tv-dec-pass-ng (c a tree make-g)
  (declare (xargs :guard (true-listp a)))
  (if (atom tree)
      (if make-g
          (list (car a) (f-equv (car a) c))
        (list (f-equv (car a) c)))
    (let ((lhs (f$tv-dec-pass-ng c
                               (tfirstn a tree)
                               (car tree)
                               t)))
      (let ((rhs (f$tv-dec-pass-ng (f-or c (car lhs))
                                 (trestn a tree)
                                 (cdr tree)
                                 make-g)))
        (if make-g
            (cons (f-or (car lhs) (car rhs))
                  (append (cdr lhs) (cdr rhs)))
          (append (cdr lhs) rhs))))))

(defthm len-f$tv-dec-pass-ng
  (equal (len (f$tv-dec-pass-ng c a tree make-g))
         (if make-g
             (1+ (tree-size tree))
           (tree-size tree)))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm len-cdr-f$tv-dec-pass-ng
  (implies make-g
           (equal (len (cdr (f$tv-dec-pass-ng c a tree make-g)))
                  (tree-size tree)))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm f$tv-dec-pass-ng=tv-dec-pass-ng
  (implies (and (booleanp c)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (f$tv-dec-pass-ng c a tree make-g)
                  (tv-dec-pass-ng c a tree make-g)))
  :hints(("Goal"
          :in-theory (e/d (bvp
                           f-or
                           tv-dec-pass-ng)
                          (tv-dec-pass-ng-rewrite-tv-dec-pass
                           tv-dec-pass-ng-works-1
                           tv-dec-pass-ng-works-2)))))

(in-theory (disable f$tv-dec-pass-ng))

;; ======================================================================

;; TV-DEC-PASS-NG*

;; A module generator that implements TV-DEC-PASS-NG.

(defconst *dec-pass-cell*
  '((dec-pass-cell
     (c a)
     (g z)
     nil
     ((g0 (g) id (a))
      (g1 (z) b-equv (a c))))))

(defthmd dec-pass-cell-okp
  (and (net-syntax-okp *dec-pass-cell*)
       (net-arity-okp *dec-pass-cell*)))

(defund dec-pass-cell& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist dec-pass-cell))

(defthmd dec-pass-cell$value
  (implies (dec-pass-cell& netlist)
           (equal (se 'dec-pass-cell (list c a) sts netlist)
                  (list a (f-equv a c))))
  :hints (("Goal" :in-theory (enable se-rules
                                      dec-pass-cell&))))

(defund tv-dec-pass-name (tree make-g)
  (declare (xargs :guard t))
  (if make-g
      (si 'tv-dec-pass-g (tree-number tree))
      (si 'tv-dec-pass-ng (tree-number tree))))

;; Notice that while TV-DEC-PASS-NG has different specifications based on a
;; flag, here we generate different circuits based on the flag, and therefore
;; must give different names to modules that produce a generate and that do not
;; produce a generate.

(defund tv-dec-pass-ng-body (tree make-g)
  (declare (xargs :guard (listp tree)))
  (let ((a-names (sis 'a 0 (tree-size tree)))
        (z-names (sis 'z 0 (tree-size tree))))
    (let ((left-a-names (tfirstn a-names tree))
          (right-a-names (trestn a-names tree))
          (left-z-names (tfirstn z-names tree))
          (right-z-names (trestn z-names tree)))
      (if (atom tree)
          (list
           (list 'leaf (list 'g (si 'z 0))
                 'dec-pass-cell (list 'c (si 'a 0))))
        (if make-g
            (list
             (list 'left (cons 'gl left-z-names)
                   (si 'tv-dec-pass-g (tree-number (car tree)))
                   (cons 'c left-a-names))
             (list 'carry '(cx) 'b-or '(c gl))
             (list 'right (cons 'gr right-z-names)
                   (si 'tv-dec-pass-g (tree-number (cdr tree)))
                   (cons 'cx right-a-names))
             (list 'generate '(g) 'b-or '(gl gr)))
          (list
           (list 'left (cons 'gl left-z-names)
                 (si 'tv-dec-pass-g (tree-number (car tree)))
                 (cons 'c left-a-names))
           (list 'carry '(cx) 'b-or '(c gl))
           (list 'right right-z-names
                 (si 'tv-dec-pass-ng (tree-number (cdr tree)))
                 (cons 'cx right-a-names))))))))

(module-generator
 tv-dec-pass-ng* (tree make-g)
 (tv-dec-pass-name tree make-g)
 (cons 'c (sis 'a 0 (tree-size tree)))
 (if make-g
     (cons 'g (sis 'z 0 (tree-size tree)))
   (sis 'z 0 (tree-size tree)))
 nil
 (tv-dec-pass-ng-body tree make-g)
 :guard (listp tree))

(defund tv-dec-pass-ng& (netlist tree make-g)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (let ((current-tv-dec-pass (tv-dec-pass-name tree make-g)))
    (let ((xnetlist (delete-to-eq current-tv-dec-pass netlist)))

      (if (atom tree)
          (and (equal (assoc current-tv-dec-pass netlist)
                      (tv-dec-pass-ng* tree make-g))
               (dec-pass-cell& xnetlist))

        (and (equal (assoc current-tv-dec-pass netlist)
                    (tv-dec-pass-ng* tree make-g))
             (tv-dec-pass-ng& xnetlist (car tree) t)
             (tv-dec-pass-ng& xnetlist (cdr tree) make-g))))))

(defun tv-dec-pass-ng$netlist (tree make-g)
  (declare (xargs :guard (tv-guard tree)))
  (if (atom tree)
      (cons (tv-dec-pass-ng* tree make-g)
            *dec-pass-cell*)
    (cons (tv-dec-pass-ng* tree make-g)
          (union$ (tv-dec-pass-ng$netlist (car tree) t)
                  (tv-dec-pass-ng$netlist (cdr tree) make-g)
                  :test 'equal))))

(defthm check-tv-dec-pass-ng$netlist
  (implies (booleanp make-g)
           (tv-dec-pass-ng&
            (tv-dec-pass-ng$netlist '(0 . (0 . 0)) make-g)
            '(0 . (0 . 0))
            make-g))
  :hints (("Goal" :in-theory (enable tv-dec-pass-ng&
                                     tv-dec-pass-name))))

(defun tv-dec-pass-ng-induction (tree c a make-g name sts netlist)
  (let ((left-a (tfirstn a tree))
        (right-a (trestn a tree))
        (module-to-delete (tv-dec-pass-name tree make-g)))

    (if (atom tree)
        (list c a make-g name sts netlist)
      (and
       (tv-dec-pass-ng-induction
        (car tree)
        c
        left-a
        t
        (si 'tv-dec-pass-g (tree-number (car tree)))
        nil
        (delete-to-eq module-to-delete netlist))

       (tv-dec-pass-ng-induction
        (cdr tree)
        (f-or c (car (f$tv-dec-pass-ng c left-a (car tree) t)))
        right-a
        t
        (si 'tv-dec-pass-g (tree-number (cdr tree)))
        nil
        (delete-to-eq module-to-delete netlist))

       (tv-dec-pass-ng-induction
        (cdr tree)
        (f-or c (car (f$tv-dec-pass-ng c left-a (car tree) t)))
        right-a
        nil
        (si 'tv-dec-pass-ng (tree-number (cdr tree)))
        nil
        (delete-to-eq module-to-delete netlist))))))

;; (defthmd tv-dec-pass-ng-lemma-crock
;;   (implies (<= (tree-size (car tree))
;;                (nfix n))
;;            (equal (assoc-eq-values (sis 'z 0 n) bindings)
;;                   (append (assoc-eq-values (take (tree-size (car tree))
;;                                                  (sis 'z 0 n))
;;                                            bindings)
;;                           (assoc-eq-values (nthcdr (tree-size (car tree))
;;                                                    (sis 'z 0 n))
;;                                            bindings))))
;;   :hints (("Goal"
;;            :use (:instance assoc-eq-values-splitting-crock
;;                            (l (sis 'z 0 n))
;;                            (n (tree-size (car tree)))
;;                            (alist bindings)))))

(local
 (defthmd tv-dec-pass-ng$value-aux
   (implies (and (no-duplicatesp keys)
                 (disjoint keys (strip-cars z1))
                 (true-listp x)
                 (true-listp y)
                 (equal (len keys)
                        (+ (len x) (len y)))
                 (equal i
                        (len y))
                 (<= i (len keys)))
            (equal
             (assoc-eq-values keys
                              (append (pairlis$ (nthcdr i keys)
                                                x)
                                      z1
                                      (pairlis$ (take i keys)
                                                y)
                                      z2))
             (append y x)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable assoc-eq-values-splitting-crock)
            :use (:instance assoc-eq-values-splitting-crock
                            (n i)
                            (l keys)
                            (alist (append (pairlis$ (nthcdr i keys)
                                                     x)
                                           z1
                                           (pairlis$ (take i keys)
                                                     y)
                                           z2)))))))

(local
 (defthm tv-dec-pass-ng$value-aux-instance-1
   (implies (and (consp tree)
                 (equal (len a) (tree-size tree)))
            (equal
             (assoc-eq-values
              (sis 'z 0 (len a))
              (append
               (pairlis$
                (nthcdr (tree-size (car tree))
                        (sis 'z 0 (len a)))
                (cdr (f$tv-dec-pass-ng
                      (f-or c
                            (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                   (car tree)
                                                   t)))
                      (nthcdr (tree-size (car tree)) a)
                      (cdr tree)
                      t)))
               (list*
                (cons 'cx
                      (f-or c
                            (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                   (car tree)
                                                   t))))
                (cons 'gl
                      (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                             (car tree)
                                             t)))
                (append
                 (pairlis$ (take (tree-size (car tree))
                                 (sis 'z 0 (len a)))
                           (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                  (car tree)
                                                  t)))
                 (cons (cons 'c c)
                       (pairlis$ (sis 'a 0 (len a)) a))))))
             (append
              (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                     (car tree)
                                     t))
              (cdr (f$tv-dec-pass-ng
                    (f-or c
                          (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                 (car tree)
                                                 t)))
                    (nthcdr (tree-size (car tree)) a)
                    (cdr tree)
                    t)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable tree-size)
            :use (:instance tv-dec-pass-ng$value-aux
                            (keys (sis 'z 0 (len a)))
                            (i (tree-size (car tree)))
                            (x (cdr (f$tv-dec-pass-ng
                                     (f-or c
                                           (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                                  (car tree)
                                                                  t)))
                                     (nthcdr (tree-size (car tree)) a)
                                     (cdr tree)
                                     t)))
                            (y (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                      (car tree)
                                                      t)))
                            (z1 (list
                                 (cons 'cx
                                       (f-or c
                                             (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                                    (car tree)
                                                                    t))))
                                 (cons 'gl
                                       (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                              (car tree)
                                                              t)))))
                            (z2 (cons (cons 'c c)
                                      (pairlis$ (sis 'a 0 (len a)) a))))))))

(local
 (defthm tv-dec-pass-ng$value-aux-instance-2
   (implies (and (consp tree)
                 (equal (len a) (tree-size tree)))
            (equal
             (assoc-eq-values
              (sis 'z 0 (len a))
              (append
               (pairlis$
                (nthcdr (tree-size (car tree))
                        (sis 'z 0 (len a)))
                (f$tv-dec-pass-ng
                 (f-or c
                       (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                              (car tree)
                                              t)))
                 (nthcdr (tree-size (car tree)) a)
                 (cdr tree)
                 nil))
               (list*
                (cons 'cx
                      (f-or c
                            (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                   (car tree)
                                                   t))))
                (cons 'gl
                      (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                             (car tree)
                                             t)))
                (append
                 (pairlis$ (take (tree-size (car tree))
                                 (sis 'z 0 (len a)))
                           (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                  (car tree)
                                                  t)))
                 (cons (cons 'c c)
                       (pairlis$ (sis 'a 0 (len a)) a))))))
             (append (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                            (car tree)
                                            t))
                     (f$tv-dec-pass-ng
                      (f-or c
                            (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                   (car tree)
                                                   t)))
                      (nthcdr (tree-size (car tree)) a)
                      (cdr tree)
                      nil))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable tree-size)
            :use (:instance tv-dec-pass-ng$value-aux
                            (keys (sis 'z 0 (len a)))
                            (i (tree-size (car tree)))
                            (x (f$tv-dec-pass-ng
                                (f-or c
                                      (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                             (car tree)
                                                             t)))
                                (nthcdr (tree-size (car tree)) a)
                                (cdr tree)
                                nil))
                            (y (cdr (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                      (car tree)
                                                      t)))
                            (z1 (list
                                 (cons 'cx
                                       (f-or c
                                             (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                                    (car tree)
                                                                    t))))
                                 (cons 'gl
                                       (car (f$tv-dec-pass-ng c (take (tree-size (car tree)) a)
                                                              (car tree)
                                                              t)))))
                            (z2 (cons (cons 'c c)
                                      (pairlis$ (sis 'a 0 (len a)) a))))))))

(not-primp-lemma tv-dec-pass-g)
(not-primp-lemma tv-dec-pass-ng)

(defthmd tv-dec-pass-ng$value
  (implies (and (tv-dec-pass-ng& netlist tree make-g)
                (equal (len a) (tree-size tree))
                (true-listp a)
                (booleanp make-g)
                (equal name (tv-dec-pass-name tree make-g)))
           (equal (se name (cons c a) sts netlist)
                  (f$tv-dec-pass-ng c a tree make-g)))
  :hints (("Goal"
           :induct (tv-dec-pass-ng-induction tree c a make-g
                                             name sts netlist)
           :in-theory (e/d (se-rules
                             tv-dec-pass-ng&
                             tv-dec-pass-ng*$destructure
                             not-primp-tv-dec-pass-g
                             not-primp-tv-dec-pass-ng
                             tv-dec-pass-name
                             tv-dec-pass-ng-body
                             dec-pass-cell$value
                             f$tv-dec-pass-ng
                             tree-size)
                            (tv-disabled-rules)))))

;; ======================================================================

;; DEC-PASS*

;; If the control line C is high does a decrement, else passes A.

(module-generator
 dec-pass* (n)
 (si 'dec-pass n)
 (cons 'c (sis 'a 0 n))
 (sis 'z 0 n)
 nil
 (list
  (list 'm0 '(cn) 'b-not '(c))
  (list 'm1
        (sis 'z 0 n)
        (si 'tv-dec-pass-ng (tree-number (make-tree n)))
        (cons 'cn (sis 'a 0 n))))
 :guard (natp n))

(defund dec-pass& (netlist n)
  (let ((xnetlist (delete-to-eq (si 'dec-pass n) netlist)))
    (and (equal (assoc (si 'dec-pass n) netlist)
                (dec-pass* n))
         (tv-dec-pass-ng& xnetlist (make-tree n) nil))))

(defun dec-pass$netlist (n)
  (cons (dec-pass* n)
        (tv-dec-pass-ng$netlist (make-tree n) nil)))

(defthm check-dec-pass$netlist
  (dec-pass& (dec-pass$netlist 7) 7))

(defun f$dec-pass (c a)
  (declare (xargs :guard (true-listp a)))
  (f$tv-dec-pass-ng (f-not c) a (make-tree (len a)) nil))

(defthm len-f$dec-pass
  (implies (not (equal (len a) 0))
           (equal (len (f$dec-pass c a))
                  (len a))))

(defthm f$dec-pass=dec-or-pass
  (implies (and (bvp v)
                (booleanp dec)
                (not (equal (len v) 0)))
           (equal (f$dec-pass dec v)
                  (if* dec (v-dec v) v))))

(not-primp-lemma dec-pass)

(defthmd dec-pass$value
  (implies (and (dec-pass& netlist n)
                (not (zp n))
                (equal (len a) n)
                (true-listp a))
           (equal (se (si 'dec-pass n) (cons c a) sts netlist)
                  (f$dec-pass c a)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             dec-pass&
                             dec-pass*$destructure
                             not-primp-dec-pass
                             tv-dec-pass-name
                             tv-dec-pass-ng$value)
                            (tv-disabled-rules)))))

(in-theory (e/d (tv-dec-pass-name)
                (f$dec-pass)))



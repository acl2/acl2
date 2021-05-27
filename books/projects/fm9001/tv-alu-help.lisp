;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

(in-package "FM9001")

(include-book "constants")
(include-book "pg-theory")
(include-book "tree-number")
(include-book "vector-module")

;; ======================================================================

;; P-CELL

(fn-to-module
 p-cell
 (a an b pa pan pb)
 (declare (xargs :guard t))
 (b-nand3 (b-nand a pa)
          (b-nand an pan)
          (b-nand b pb)))

(defthm p-cell$value-zero
  (implies (p-cell& netlist)
           (equal (se 'p-cell (list a an b nil nil nil) sts netlist)
                  (list nil)))
  :hints (("Goal"
           :in-theory (enable p-cell$value f$p-cell f-gates))))

;; G-CELL

(fn-to-module
 g-cell
 (a an bn ga gan gbn)
 (declare (xargs :guard t))
 (b-and3 (b-nand a ga)
         (b-nand an gan)
         (b-nand bn gbn)))

(defthm g-cell$value-zero
  (implies (g-cell& netlist)
   (equal (se 'g-cell (list a an bn nil nil nil) sts netlist)
          (list t)))
  :hints (("Goal"
           :in-theory (enable g-cell$value f$g-cell f-gates))))

;; ALU-CELL

(defun alu-cell (c a b mpg)
  (declare (xargs :guard (true-listp mpg)))
  (let ((gbn (car mpg))
        (gan (cadr mpg))
        (ga  (caddr mpg))
        (pb  (cadddr mpg))
        (pan (car (cddddr mpg)))
        (pa  (cadr (cddddr mpg)))
        (m   (caddr (cddddr mpg))))
    (let ((an (b-not a))
          (bn (b-not b)))
      (let ((p (p-cell a an b pa pan pb))
            (g (g-cell a an bn ga gan gbn))
            (mc (b-nand c m)))
        (let ((z (b-equv3 mc p g)))
          (list p g z))))))

(defun f$alu-cell (c a b mpg)
  (declare (xargs :guard (true-listp mpg)))
  (let ((gbn (car mpg))
        (gan (cadr mpg))
        (ga  (caddr mpg))
        (pb  (cadddr mpg))
        (pan (car (cddddr mpg)))
        (pa  (cadr (cddddr mpg)))
        (m   (caddr (cddddr mpg))))
    (let ((an (f-not a))
          (bn (f-not b)))
      (let ((p (f$p-cell a an b pa pan pb))
            (g (f$g-cell a an bn ga gan gbn))
            (mc (f-nand c m)))
        (let ((z (f-equv3 mc p g)))
          (list p g z))))))

(defthm f$alu-cell=alu-cell
  (implies (and (booleanp c)
                (booleanp a)
                (booleanp b)
                (bvp mpg))
           (equal (f$alu-cell c a b mpg)
                  (alu-cell c a b mpg)))
  :hints (("Goal"
           :in-theory (enable bvp))))

(defconst *alu-cell*
  (cons
   '(alu-cell (c a b gbn gan ga pb pan pa m)
              (p g z)
              ()
              ((n0 (an) b-not (a))
               (n1 (bn) b-not (b))
               (p0 (p)  p-cell (a an b pa pan pb))
               (g0 (g)  g-cell (a an bn ga gan gbn))
               (m0 (mc) b-nand (c m))
               (z0 (z)  b-equv3 (mc p g))))
   (append *p-cell* *g-cell*)))

(defthmd alu-cell-okp
  (and (net-syntax-okp *alu-cell*)
       (net-arity-okp *alu-cell*)))

(defund alu-cell& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (and (netlist-hyps netlist alu-cell)
       (b* ((netlist (delete-to-eq 'alu-cell netlist)))
         (and (p-cell& netlist)
              (g-cell& netlist)))))

(defthmd alu-cell$value
  (implies (alu-cell& netlist)
           (equal (se 'alu-cell (list* c a b mpg) sts netlist)
                  (f$alu-cell c a b mpg)))
  :hints (("Goal"
           :in-theory (enable se-rules
                               alu-cell&
                               p-cell$value
                               g-cell$value))))

(defthmd alu-cell$value-zero
  (implies (and (alu-cell& netlist)
                (equal mpg *v1000000*))
           (equal (se 'alu-cell (list* t a b mpg) sts netlist)
                  (list nil t nil)))
  :hints (("Goal" :in-theory (enable alu-cell$value
                                      f$p-cell
                                      f$g-cell
                                      f-gates))))

(defthm f$alu-cell-v-threefix-mpg
  (equal (f$alu-cell c a b (v-threefix mpg))
         (f$alu-cell c a b mpg))
  :hints (("Goal" :in-theory (e/d (f$p-cell
                                   f$g-cell
                                   f-gate-3v-fix-congruence-lemmas)
                                  (3v-fix)))))

(in-theory (disable f$alu-cell))

;; ======================================================================

;; TV-ALU-HELP

;; The Boolean specification of the main component of the ALU.  The TREE
;; specifies the structure of the carry-lookahead tree of the ALU.

(defun tv-alu-help (c a b mpg tree)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b)
                              (true-listp mpg))))
  (if (atom tree)
      (alu-cell c (car a) (car b) mpg)
    (let ((a-car (tfirstn a tree))
          (b-car (tfirstn b tree))
          (a-cdr (trestn  a tree))
          (b-cdr (trestn  b tree)))
      (let ((lhs (tv-alu-help c a-car b-car mpg (car tree))))
        (let ((p-car (car lhs))
              (g-car (cadr lhs))
              (sum-car (cddr lhs)))
          (let ((c-car (t-carry c p-car g-car)))
            (let ((rhs (tv-alu-help c-car a-cdr b-cdr mpg (cdr tree))))
              (let ((p-cdr (car rhs))
                    (g-cdr (cadr rhs))
                    (sum-cdr (cddr rhs)))
                (cons (b-and p-car p-cdr)
                      (cons (t-carry g-car p-cdr g-cdr)
                            (append sum-car sum-cdr)))))))))))

(defthm len-cddr-tv-alu-help
  (equal (len (cddr (tv-alu-help c a b mpg tree)))
         (tree-size tree))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm len-tv-alu-help
  (equal (len (tv-alu-help c a b mpg tree))
         (+ 2 (tree-size tree)))
  :hints (("Goal" :in-theory (enable tree-size))))

(defthm bvp-cddr-tv-alu-help
  (bvp (cddr (tv-alu-help c a b mpg tree)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-tv-alu-help
  (bvp (tv-alu-help c a b mpg tree))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-len-tv-alu-help
  (equal (bvp-len (tv-alu-help c a b mpg tree) n)
         (<= n (+ 2 (tree-size tree))))
  :hints (("Goal" :in-theory (enable bvp-len)))
  :rule-classes :linear)

;; Proofs that TV-ALU-HELP "does the right thing."

;; ZERO

(defthmd tv-alu-help-zero
  (implies (and (equal mpg *v1000000*)
                (equal (len a) (tree-size tree))
                (equal c t))
           (equal (tv-alu-help c a b mpg tree)
                  (list* nil t (make-list (len a)))))
  :hints (("Goal"
           :in-theory (enable p-cell g-cell))))

;; V-AND

(defthmd tv-alu-help-v-and-works
  (implies (and (bv2p a b)
                (equal (len a) (tree-size tree))
                (equal mpg *v0000011*))
           (equal (cddr (tv-alu-help c a b mpg tree))
                  (v-and a b)))
  :hints (("Goal"
           :in-theory (enable bvp v-and))))

;; V-OR

(defthmd tv-alu-help-v-or-works
  (implies (and (equal mpg *v0101110*)
                (bv2p a b)
                (equal (len a) (tree-size tree)))
           (equal (cddr (tv-alu-help c a b mpg tree))
                  (v-or a b)))
  :hints (("Goal"
           :in-theory (enable bvp v-or))))

;; V-XOR

(defthmd tv-alu-help-v-xor-works
  (implies (and (equal mpg *v0100001*)
                (bv2p a b)
                (equal (len a) (tree-size tree)))
           (equal (cddr (tv-alu-help c a b mpg tree))
                  (v-xor a b)))
  :hints (("Goal"
           :in-theory (enable bvp v-xor))))

;; V-NOT

(defthmd tv-alu-help-v-not-works
  (implies (and (equal mpg *v0010110*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (cddr (tv-alu-help c a b mpg tree))
                  (v-not a)))
  :hints (("Goal"
           :in-theory (enable bvp p-cell v-not))))

;; V-BUF

(defthmd tv-alu-help-v-buf-works
  (implies (and (equal mpg *v0100110*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (cddr (tv-alu-help c a b mpg tree))
                  (v-buf a)))
  :hints (("Goal"
           :in-theory (enable bvp p-cell v-buf))))

;; TV-ADDER

(defthmd tv-alu-help-tv-adder-works
  (implies (and (equal mpg *v1101011*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c a b tree)))
  :hints (("Goal"
           :in-theory (enable bvp p-cell tv-adder))))

;; Subtracter

(defthmd tv-alu-help-tv-subtracter-works
  (implies (and (equal mpg *v1011101*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c (v-not a) b tree)))
  :hints (("Goal"
           :in-theory (enable bvp p-cell tv-adder v-not))))

;; INC a

(defthmd tv-alu-help-tv-inc-a-works
  (implies (and (equal mpg *v1100110*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c a (nat-to-v 0 (len a)) tree)))
  :hints (("Goal"
           :in-theory (enable p-cell g-cell tv-adder))))

;; INC b

(defthmd tv-alu-help-tv-inc-b-works
  (implies (and (equal mpg *v1001110*)
                (bvp b)
                (equal (len b) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c b (nat-to-v 0 (len b)) tree)))
  :hints (("Goal"
           :in-theory (enable p-cell g-cell tv-adder))))

;; DEC a

(defthmd tv-alu-help-tv-dec-a-works
  (implies (and (equal mpg *v1110010*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c (v-not (nat-to-v 0 (len a))) a tree)))
  :hints (("Goal"
           :in-theory (e/d (bvp
                            take-v-not
                            nthcdr-v-not
                            p-cell tv-adder)
                           (v-not-take
                            v-not-nthcdr)))))

;; DEC b

(defthmd tv-alu-help-tv-dec-b-works
  (implies (and (equal mpg *v1110001*)
                (bvp b)
                (equal (len b) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c (v-not (nat-to-v 0 (len b))) b tree)))
  :hints (("Goal"
           :in-theory (e/d (take-v-not
                            nthcdr-v-not
                            p-cell g-cell tv-adder)
                           (v-not-take
                            v-not-nthcdr)))))

;; NEG

(defthmd tv-alu-help-tv-neg-works
  (implies (and (equal mpg *v1010110*)
                (bvp a)
                (equal (len a) (tree-size tree)))
           (equal (tv-alu-help c a b mpg tree)
                  (tv-adder c (v-not a) (nat-to-v 0 (len a)) tree)))
  :hints (("Goal"
           :in-theory (enable p-cell g-cell tv-adder v-not))))

(in-theory (disable tv-alu-help))

;; ======================================================================

;; F$TV-ALU-HELP

;; The 4-valued ALU specification equivalent to TV-ALU-HELP.

(defun f$tv-alu-help (c a b mpg tree)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b)
                              (true-listp mpg))))
  (if (atom tree)
      (f$alu-cell c (car a) (car b) mpg)
    (let ((a-car (tfirstn a tree))
          (b-car (tfirstn b tree))
          (a-cdr (trestn  a tree))
          (b-cdr (trestn  b tree)))
      (let ((lhs (f$tv-alu-help c a-car b-car mpg (car tree))))
        (let ((p-car (car lhs))
              (g-car (cadr lhs))
              (sum-car (cddr lhs)))
          (let ((c-car (f$t-carry c p-car g-car)))
            (let ((rhs (f$tv-alu-help c-car a-cdr b-cdr mpg (cdr tree))))
              (let ((p-cdr (car rhs))
                    (g-cdr (cadr rhs))
                    (sum-cdr (cddr rhs)))
                (cons (f-and p-car p-cdr)
                      (cons (f$t-carry g-car p-cdr g-cdr)
                            (append sum-car sum-cdr)))))))))))

(defthm len-cddr-f$tv-alu-help
  (equal (len (cddr (f$tv-alu-help c a b mpg tree)))
         (tree-size tree))
  :hints (("Goal"
           :in-theory (enable f$alu-cell tree-size))))

(defthm len-f$tv-alu-help
  (equal (len (f$tv-alu-help c a b mpg tree))
         (+ 2 (tree-size tree)))
  :hints (("Goal"
           :in-theory (enable f$alu-cell tree-size))))

(defthm bvp-f$tv-alu-help
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (bvp mpg))
           (bvp (f$tv-alu-help c a b mpg tree)))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-car-f$tv-alu-help
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (bvp mpg))
           (booleanp (car (f$tv-alu-help c a b mpg tree))))
  :rule-classes (:rewrite :type-prescription))

(defthm booleanp-cadr-f$tv-alu-help
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (bvp mpg))
           (booleanp (cadr (f$tv-alu-help c a b mpg tree))))
  :hints (("Goal"
           :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm bvp-cddr-f$tv-alu-help
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (bvp mpg))
           (bvp (cddr (f$tv-alu-help c a b mpg tree))))
  :hints (("Goal"
           :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm f$tv-alu-help=tv-alu-help
  (implies (and (booleanp c)
                (bvp a) (equal (len a) (tree-size tree))
                (bvp b) (equal (len b) (tree-size tree))
                (bvp mpg))
           (equal (f$tv-alu-help c a b mpg tree)
                  (tv-alu-help c a b mpg tree)))
  :hints (("Goal"
           :in-theory (e/d (bvp tv-alu-help)
                            (alu-cell)))))

(in-theory (disable f$tv-alu-help))

;; ======================================================================

;; TV-ALU-HELP-BODY

;; The hardware version of TV-ALU-HELP.

(defun tv-alu-help-body (tree)
  (declare (xargs :guard (listp tree)))
  (let ((a-names (sis 'a 0 (tree-size tree)))
        (b-names (sis 'b 0 (tree-size tree)))
        (out-names (sis 'out 0 (tree-size tree)))
        (mpgnames (sis 'mpg 0 7))
        (mpgnames- (sis 'mpg- 0 7)))
    (let ((left-a-names (tfirstn a-names tree))
          (right-a-names (trestn a-names tree))
          (left-b-names (tfirstn b-names tree))
          (right-b-names (trestn b-names tree))
          (left-out-names (tfirstn out-names tree))
          (right-out-names (trestn out-names tree)))
      (let ((buffer? (equal (mod (1- (tree-height tree)) 3) 0)))
        (let ((mpgnames? (if buffer? mpgnames- mpgnames)))
          (if (atom tree)
              (list
               (list 'leaf
                     (list 'p 'g (si 'out 0))
                     'alu-cell
                     (cons 'c (cons (si 'a 0)
                                    (cons (si 'b 0) mpgnames)))))
            ;;  We buffer MPG whenever appropriate.
            (append
             (if buffer?
                 (list
                  (list 'buffermpg mpgnames- (si 'v-buf 7) mpgnames))
               nil)
             (list
              ;;  The LHS ALU result.
              (list 'lhs
                    (cons 'pl (cons 'gl left-out-names))
                    (si 'tv-alu-help (tree-number (car tree)))
                    (cons 'c
                          (append left-a-names
                                  (append left-b-names
                                          mpgnames?))))
              ;;  The LHS carry.
              '(lhs-carry (cl) t-carry (c pl gl))
              ;;  The RHS ALU result.
              (list 'rhs
                    (cons 'pr (cons 'gr right-out-names))
                    (si 'tv-alu-help (tree-number (cdr tree)))
                    (cons 'cl
                          (append right-a-names
                                  (append right-b-names
                                          mpgnames?))))
              ;;  The propagate output.
              '(p (p) b-and (pl pr))
              ;;  The generate output.
              '(g (g) t-carry (gl pr gr))))))))))

(destructuring-lemma
 tv-alu-help* (tree)
 (declare (xargs :guard (listp tree)))
 ;; Bindings
 ((a-names (sis 'a 0 (tree-size tree)))
  (b-names (sis 'b 0 (tree-size tree)))
  (out-names (sis 'out 0 (tree-size tree)))
  (mpgnames (sis 'mpg 0 7)))
 ;; Name
 (si 'tv-alu-help (tree-number tree))
 ;; Inputs
 (cons 'c (append a-names (append b-names mpgnames)))
 ;; Outputs
 (cons 'p (cons 'g out-names))
 ;; States
 nil
 ;; Occurrences
 (tv-alu-help-body tree))

(defund tv-alu-help& (netlist tree)
  (declare (xargs :guard (and (alistp netlist)
                              (tv-guard tree))))
  (if (atom tree)
      (and (equal (assoc (si 'tv-alu-help (tree-number tree))
                         netlist)
                  (tv-alu-help* tree))
           (alu-cell& (delete-to-eq (si 'tv-alu-help (tree-number tree))
                                    netlist)))
    (and (equal (assoc (si 'tv-alu-help (tree-number tree)) netlist)
                (tv-alu-help* tree))
         (t-carry& (delete-to-eq (si 'tv-alu-help (tree-number tree))
                                 netlist))
         (v-buf& (delete-to-eq (si 'tv-alu-help (tree-number tree))
                               netlist)
                 7)
         (tv-alu-help& (delete-to-eq (si 'tv-alu-help (tree-number tree))
                                     netlist)
                       (car tree))
         (tv-alu-help& (delete-to-eq (si 'tv-alu-help (tree-number tree))
                                     netlist)
                       (cdr tree)))))

(defun tv-alu-help$netlist (tree)
  (declare (xargs :guard (tv-guard tree)))
  (if (atom tree)
      (cons (tv-alu-help* tree) *alu-cell*)
    (cons (tv-alu-help* tree)
          (union$ (tv-alu-help$netlist (car tree))
                  (tv-alu-help$netlist (cdr tree))
                  *t-carry*
                  (v-buf$netlist 7)
                  :test 'equal))))

(defun tv-alu-help-induction (tree c a b mpg sts netlist)
  (let ((left-a (tfirstn a tree))
        (left-b (tfirstn b tree))
        (right-a (trestn a tree))
        (right-b (trestn b tree))
        (buffer? (equal (mod (1- (tree-height tree)) 3) 0)))
    (let ((mpg (if buffer? (v-threefix mpg) mpg)))
      (if (atom tree)
          (list c a b mpg sts netlist)
        (and
         (tv-alu-help-induction
          (car tree)
          c
          left-a
          left-b
          mpg
          nil
          (delete-to-eq (si 'tv-alu-help (tree-number tree)) netlist))
         (tv-alu-help-induction
          (cdr tree)
          (f$t-carry c
                     (car (f$tv-alu-help c left-a left-b mpg (car tree)))
                     (cadr (f$tv-alu-help c left-a left-b mpg (car tree))))
          right-a
          right-b
          mpg
          nil
          (delete-to-eq (si 'tv-alu-help (tree-number tree)) netlist)))))))

;; (defthmd tv-alu-help-lemma-crock
;;   (implies (<= (tree-size (car tree))
;;                     (nfix n))
;;            (equal (assoc-eq-values (sis 'out 0 n) bindings)
;;                   (append (assoc-eq-values (take (tree-size (car tree))
;;                                                  (sis 'out 0 n))
;;                                            bindings)
;;                           (assoc-eq-values (nthcdr (tree-size (car tree))
;;                                                    (sis 'out 0 n))
;;                                            bindings))))
;;   :hints (("Goal"
;;            :use (:instance assoc-eq-values-splitting-crock
;;                            (l (sis 'out 0 n))
;;                            (n (tree-size (car tree)))
;;                            (alist bindings)))))

(not-primp-lemma tv-alu-help)

(defthmd tv-alu-help$value-base-case
  (implies (and (atom tree)
                (tv-alu-help& netlist tree)
                (equal (len a) 1)
                (equal (len b) 1))
           (equal (se (si 'tv-alu-help (tree-number tree))
                      (cons c (append a (append b mpg)))
                      sts netlist)
                  (f$tv-alu-help c a b mpg tree)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                             tv-alu-help&
                             tv-alu-help*$destructure
                             not-primp-tv-alu-help
                             f$tv-alu-help
                             f$alu-cell
                             alu-cell$value)
                            (tv-disabled-rules)))))

(defthm f$tv-alu-help-v-threefix-mpg
  (equal (f$tv-alu-help c a b (v-threefix mpg) tree)
         (f$tv-alu-help c a b mpg tree))
  :hints (("Goal"
           :in-theory (enable f$tv-alu-help))))

(local
 (defthmd tv-alu-help$value-aux
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
 (defthm tv-alu-help$value-aux-instance-1
   (implies (and (consp tree)
                 (equal (len a) (tree-size tree)))
            (equal
             (assoc-eq-values
              (sis 'out 0 (len a))
              (append
               (pairlis$
                (nthcdr (tree-size (car tree))
                        (sis 'out 0 (len a)))
                (cddr
                 (f$tv-alu-help
                  (f$t-carry c
                             (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                 (take (tree-size (car tree)) b)
                                                 mpg (car tree)))
                             (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                  (take (tree-size (car tree)) b)
                                                  mpg (car tree))))
                  (nthcdr (tree-size (car tree)) a)
                  (nthcdr (tree-size (car tree)) b)
                  mpg (cdr tree))))
               (list*
                (cons 'cl
                      (f$t-carry c
                                 (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                     (take (tree-size (car tree)) b)
                                                     mpg (car tree)))
                                 (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                      (take (tree-size (car tree)) b)
                                                      mpg (car tree)))))
                (cons 'pl
                      (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                          (take (tree-size (car tree)) b)
                                          mpg (car tree))))
                (cons 'gl
                      (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                           (take (tree-size (car tree)) b)
                                           mpg (car tree))))
                (append (pairlis$ (take (tree-size (car tree))
                                        (sis 'out 0 (len a)))
                                  (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                       (take (tree-size (car tree)) b)
                                                       mpg (car tree))))
                        (cons (cons 'c c)
                              (append (pairlis$ (sis 'a 0 (len a)) a)
                                      (pairlis$ (sis 'b 0 (len a)) b)
                                      (pairlis$ (sis 'mpg 0 7) mpg)))))))
             (append
              (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                   (take (tree-size (car tree)) b)
                                   mpg (car tree)))
              (cddr
               (f$tv-alu-help
                (f$t-carry c
                           (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                               (take (tree-size (car tree)) b)
                                               mpg (car tree)))
                           (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                (take (tree-size (car tree)) b)
                                                mpg (car tree))))
                (nthcdr (tree-size (car tree)) a)
                (nthcdr (tree-size (car tree)) b)
                mpg (cdr tree))))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable tree-size)
            :use (:instance tv-alu-help$value-aux
                            (keys (sis 'out 0 (len a)))
                            (i (tree-size (car tree)))
                            (x (cddr
                                (f$tv-alu-help
                                 (f$t-carry c
                                            (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                (take (tree-size (car tree)) b)
                                                                mpg (car tree)))
                                            (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                 (take (tree-size (car tree)) b)
                                                                 mpg (car tree))))
                                 (nthcdr (tree-size (car tree)) a)
                                 (nthcdr (tree-size (car tree)) b)
                                 mpg (cdr tree))))
                            (y (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                    (take (tree-size (car tree)) b)
                                                    mpg (car tree))))
                            (z1 (list
                                 (cons 'cl
                                       (f$t-carry c
                                                  (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                      (take (tree-size (car tree)) b)
                                                                      mpg (car tree)))
                                                  (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                       (take (tree-size (car tree)) b)
                                                                       mpg (car tree)))))
                                 (cons 'pl
                                       (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                           (take (tree-size (car tree)) b)
                                                           mpg (car tree))))
                                 (cons 'gl
                                       (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                            (take (tree-size (car tree)) b)
                                                            mpg (car tree))))))
                            (z2 (cons (cons 'c c)
                                      (append (pairlis$ (sis 'a 0 (len a)) a)
                                              (pairlis$ (sis 'b 0 (len a)) b)
                                              (pairlis$ (sis 'mpg 0 7)
                                                        mpg)))))))))

(local
 (defthm tv-alu-help$value-aux-instance-2
   (implies (and (consp tree)
                 (equal (len a) (tree-size tree)))
            (equal
             (assoc-eq-values
              (sis 'out 0 (len a))
              (append
               (pairlis$
                (nthcdr (tree-size (car tree))
                        (sis 'out 0 (len a)))
                (cddr
                 (f$tv-alu-help
                  (f$t-carry c
                             (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                 (take (tree-size (car tree)) b)
                                                 mpg (car tree)))
                             (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                  (take (tree-size (car tree)) b)
                                                  mpg (car tree))))
                  (nthcdr (tree-size (car tree)) a)
                  (nthcdr (tree-size (car tree)) b)
                  mpg (cdr tree))))
               (list*
                (cons 'cl
                      (f$t-carry c
                                 (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                     (take (tree-size (car tree)) b)
                                                     mpg (car tree)))
                                 (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                      (take (tree-size (car tree)) b)
                                                      mpg (car tree)))))
                (cons 'pl
                      (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                          (take (tree-size (car tree)) b)
                                          mpg (car tree))))
                (cons 'gl
                      (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                           (take (tree-size (car tree)) b)
                                           mpg (car tree))))
                (append (pairlis$ (take (tree-size (car tree))
                                        (sis 'out 0 (len a)))
                                  (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                       (take (tree-size (car tree)) b)
                                                       mpg (car tree))))
                        (pairlis$ (sis 'mpg- 0 7)
                                  (v-threefix mpg))
                        (cons (cons 'c c)
                              (append (pairlis$ (sis 'a 0 (len a)) a)
                                      (pairlis$ (sis 'b 0 (len a)) b)
                                      (pairlis$ (sis 'mpg 0 7) mpg)))))))
             (append
              (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                   (take (tree-size (car tree)) b)
                                   mpg (car tree)))
              (cddr
               (f$tv-alu-help
                (f$t-carry c
                           (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                               (take (tree-size (car tree)) b)
                                               mpg (car tree)))
                           (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                (take (tree-size (car tree)) b)
                                                mpg (car tree))))
                (nthcdr (tree-size (car tree)) a)
                (nthcdr (tree-size (car tree)) b)
                mpg (cdr tree))))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable tree-size)
            :use (:instance tv-alu-help$value-aux
                            (keys (sis 'out 0 (len a)))
                            (i (tree-size (car tree)))
                            (x (cddr
                                (f$tv-alu-help
                                 (f$t-carry c
                                            (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                (take (tree-size (car tree)) b)
                                                                mpg (car tree)))
                                            (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                 (take (tree-size (car tree)) b)
                                                                 mpg (car tree))))
                                 (nthcdr (tree-size (car tree)) a)
                                 (nthcdr (tree-size (car tree)) b)
                                 mpg (cdr tree))))
                            (y (cddr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                    (take (tree-size (car tree)) b)
                                                    mpg (car tree))))
                            (z1 (list
                                 (cons 'cl
                                       (f$t-carry c
                                                  (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                      (take (tree-size (car tree)) b)
                                                                      mpg (car tree)))
                                                  (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                                       (take (tree-size (car tree)) b)
                                                                       mpg (car tree)))))
                                 (cons 'pl
                                       (car (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                           (take (tree-size (car tree)) b)
                                                           mpg (car tree))))
                                 (cons 'gl
                                       (cadr (f$tv-alu-help c (take (tree-size (car tree)) a)
                                                            (take (tree-size (car tree)) b)
                                                            mpg (car tree))))))
                            (z2 (append (pairlis$ (sis 'mpg- 0 7)
                                                  (v-threefix mpg))
                                        (cons (cons 'c c)
                                              (append (pairlis$ (sis 'a 0 (len a)) a)
                                                      (pairlis$ (sis 'b 0 (len a)) b)
                                                      (pairlis$ (sis 'mpg 0 7) mpg))))))))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthmd tv-alu-help$value
  (implies (and (tv-alu-help& netlist tree)
                (true-listp a) (equal (len a) (tree-size tree))
                (true-listp b) (equal (len b) (tree-size tree))
                (true-listp mpg) (equal (len mpg) 7))
           (equal (se (si 'tv-alu-help (tree-number tree))
                      (cons c (append a (append b mpg)))
                      sts netlist)
                  (f$tv-alu-help c a b mpg tree)))
  :hints (("Goal"
           :induct (tv-alu-help-induction tree c a b mpg sts netlist)
           :in-theory (e/d (se-rules
                             tv-alu-help&
                             tv-alu-help*$destructure
                             not-primp-tv-alu-help
                             tv-alu-help$value-base-case
                             tree-size
                             f$tv-alu-help
                             t-carry$value
                             v-buf$value)
                            (tv-disabled-rules
                             f$t-carry=t-carry
                             f-gates=b-gates
                             (si)
                             (sis))))))

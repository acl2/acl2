;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; August 2016

;; A SUM/CARRY/GENERATE/PROPAGATE theory of addition, and the tree-based adder
;; TV-ADDER.

(in-package "FM9001")

(include-book "de")
(include-book "macros")

;; ======================================================================

;; SUM

(defun v-sum (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (b-xor c (b-xor (car a) (car b)))
          (v-sum (b-or3 (b-and (car a) (car b))
                        (b-and (car a) c)
                        (b-and (car b) c))
                 (cdr a)
                 (cdr b)))))

(defthm bvp-sum
  (bvp (v-sum c a b))
  :hints (("Goal" :in-theory (enable bvp)))
  :rule-classes (:rewrite :type-prescription))

(defthm len-sum
  (equal (len (v-sum c a b))
         (len a)))

(defthm v-sum-congruence
  (implies c
           (equal (equal (v-sum c a b)
                         (v-sum t a b))
                  t)))

(defthm a-1+1=a
  (implies (and (bvp a) c)
           (equal (v-sum c (v-not (nat-to-v 0 (len a))) a)
                  a))
  :hints (("Goal" :in-theory (enable bvp v-not nat-to-v))))

(in-theory (disable v-sum))

;; V-CARRY

(defun v-carry (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      (bool-fix c)
    (let ((a-bit (car a))
          (b-bit (car b)))
      (let ((p (or a-bit b-bit))
            (g (and a-bit b-bit)))
        (v-carry (or g (and p c)) (cdr a) (cdr b))))))

(defthm v-carry-congruence
  (implies c
           (equal (equal (v-carry c a b)
                         (v-carry t a b))
                  t)))

(in-theory (disable v-carry))

;; V-PROPAGATE

(defund v-propagate (a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      t
    (let ((a-bit (car a))
          (b-bit (car b)))
      (and (or a-bit b-bit)
           (v-propagate (cdr a) (cdr b))))))

;; V-GENERATE

(defund v-generate (a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (let ((a-bit (car a))
          (b-bit (car b)))
      (or (v-generate (cdr a) (cdr b))
          (and a-bit b-bit (v-propagate (cdr a) (cdr b)))))))

;; T-CARRY

;; We keep this non-recursive definition disabled because we are usually
;; interested in the logical properties of T-CARRY with respect to V-CARRY,
;; V-PROPAGATE, and V-GENERATE.

(defun f$t-carry (c prop gen)
  (declare (xargs :guard t))
  (f-or (f-and c prop) gen))

(defun t-carry (c prop gen)
  (declare (xargs :guard t))
  (b-not (ao6 c prop gen)))

(defthm f$t-carry=t-carry
  (implies (and (booleanp c)
                (booleanp prop)
                (booleanp gen))
           (equal (f$t-carry c prop gen)
                  (t-carry c prop gen))))

(in-theory (disable f$t-carry))

(defthm t-carry-congruence
  (implies x
           (equal (equal (t-carry x p g)
                         (t-carry t p g))
                  t)))

(in-theory (disable t-carry))

(defconst *t-carry*
  '((t-carry
     (c prop gen)
     (z)
     ()
     ((g0 (z-) ao6 (c prop gen))
      (g1 (z) b-not (z-))))))

(defthmd t-carry-okp
  (and (net-syntax-okp *t-carry*)
       (net-arity-okp *t-carry*)))

(defund t-carry& (netlist)
  (declare (xargs :guard (alistp netlist)))
  (netlist-hyps netlist t-carry))

(defthmd t-carry$value
  (implies (t-carry& netlist)
           (equal (se 't-carry (list c prop gen) sts netlist)
                  (list (f$t-carry c prop gen))))
  :hints (("Goal"
           :in-theory (enable se-rules t-carry& f$t-carry f-gates))))

;; Lemmas

(defthm v-append-propagate
  (implies (equal (len a) (len c))
           (equal (v-propagate (append a b) (append c d))
                  (and (v-propagate a c)
                       (v-propagate b d))))
  :hints (("Goal"
           :in-theory (enable v-propagate))))

(defthmd v-propagate-append
  (implies (equal (len a) (len c))
           (equal (b-and (v-propagate a c)
                         (v-propagate b d))
                  (v-propagate (append a b) (append c d)))))

(defthm generate-append
  (implies (equal (len a) (len c))
           (equal (t-carry (v-generate a c)
                           (v-propagate b d)
                           (v-generate b d))
                  (v-generate (append a b) (append c d))))
  :hints (("Goal"
           :in-theory (enable t-carry v-generate v-propagate))))

(defthm append-sum
  (implies (and (equal (len a) (len b))
                (equal c2 (v-carry c1 a b)))
           (equal (append (v-sum c1 a b) (v-sum c2 c d))
                  (v-sum c1 (append a c) (append b d))))
  :hints (("Goal"
           :in-theory (enable v-sum v-carry))))

(defthm t-carry-p-g-carry
  (equal (t-carry c (v-propagate a b) (v-generate a b))
         (v-carry c a b))
  :hints (("Goal"
           :in-theory (enable t-carry v-propagate v-generate v-carry))))

;; Show that V-ADDER-OUTPUT == V-SUM, and V-ADDER-CARRY-OUT = V-CARRY

(defthm v-adder-output=v-sum
  (equal (v-adder-output c a b)
         (v-sum c a b))
  :hints (("Goal"
           :in-theory (enable v-adder v-sum))))

(defthm v-adder-carry-out=v-carry
   (equal (v-adder-carry-out c a b)
          (v-carry c a b))
   :hints (("Goal"
           :in-theory (enable v-adder v-carry))))

;; TV-ADDER is a propagate-generate adder specification. C is the carry-in, A
;; and B are bit-vector addends, and TREE specifies the carry-lookahead
;; structure of the adder.  TV-ADDER conceptually returns 3 results:  The CAR
;; is (V-PROPAGATE A B), the CADR is (V-GENERATE A B), and the CDDR is
;; (V-SUM C A B).

(defun tv-adder (c a b tree)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b))))
  (if (atom tree)
      (list (b-or (car a) (car b))
            (b-and (car a) (car b))
            (b-xor (car a) (b-xor (car b) c)))
    (let ((lhs (tv-adder c
                         (tfirstn a tree)
                         (tfirstn b tree)
                         (car tree))))
      (let ((lhs-p (car lhs))
            (lhs-g (cadr lhs))
            (lhs-sum (cddr lhs)))
        (let ((rhs-c (t-carry c lhs-p lhs-g)))
          (let ((rhs (tv-adder rhs-c
                               (trestn a tree)
                               (trestn b tree)
                               (cdr tree))))
            (let ((rhs-p (car rhs))
                  (rhs-g (cadr rhs))
                  (rhs-sum (cddr rhs)))
              (let ((p (b-and lhs-p rhs-p))
                    (g (t-carry lhs-g rhs-p rhs-g)))
                (cons p (cons g (append lhs-sum rhs-sum)))))))))))

;; The proofs that TV-ADDER = (P . (G . SUM)).

(defthm car-tv-adder-as-p
  (implies (and (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree)))
           (equal (car (tv-adder c a b tree))
                  (v-propagate a b)))
  :hints (("Goal"
           :in-theory (e/d (v-propagate
                            v-propagate-append)
                           (b-and
                            v-append-propagate)))))

(defthm cadr-tv-adder-as-g
  (implies (and (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree)))
           (equal (cadr (tv-adder c a b tree))
                  (v-generate a b)))
  :hints (("Goal"
           :in-theory (e/d (v-generate
                            v-propagate)
                           (t-carry-p-g-carry)))))

(defthm cddr-tv-adder-as-sum
  (implies (and (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree)))
           (equal (cddr (tv-adder c a b tree))
                  (v-sum c a b)))
  :hints (("Goal"
           :in-theory (e/d (v-sum)
                           ()))))

(local
 (defthm equality-of-three-element-lists
   (implies (not (equal z nil))
            (equal (equal w (cons x (cons y z)))
                   (and (equal (car w) x)
                        (equal (cadr w) y)
                        (equal (cddr w) z))))))

(in-theory (disable tv-adder))

(defthmd tv-adder-as-p-g-sum
  (implies (and (equal (len a) (tree-size tree))
                (equal (len b) (tree-size tree)))
           (equal (tv-adder c a b tree)
                  (cons (v-propagate a b)
                        (cons (v-generate a b)
                              (v-sum c a b)))))
  :hints (("Goal"
           :in-theory (e/d (v-sum)
                           ()))))

(in-theory (disable car-tv-adder-as-p
                    cadr-tv-adder-as-g
                    cddr-tv-adder-as-sum))


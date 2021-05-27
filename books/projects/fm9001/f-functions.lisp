;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; October 2016

;; Definitions of basic 3- and 4-valued specifications for DE.
;; This file also includes some 3- and 4-valued vector specifications.

(in-package "FM9001")

(include-book "hard-spec")

;; ======================================================================

;; We begin by introducing primitive functions for 4-state logic.

(defun f-buf (a)
  (declare (xargs :guard t))
  (3v-fix a))

(defun f-and (a b)
  (declare (xargs :guard t))
  (if (or (equal a nil) (equal b nil))
      nil
    (if (and (equal a t) (equal b t))
        t
      *x*)))

(defun f-and3 (a b c)
  (declare (xargs :guard t))
  (f-and a (f-and b c)))

(defun f-and4 (a b c d)
  (declare (xargs :guard t))
  (f-and a (f-and b (f-and c d))))

(defun f-not (a)
  (declare (xargs :guard t))
  (if (booleanp a)
      (not a)
    *x*))

(defun f-nand (a b)
  (declare (xargs :guard t))
  (f-not (f-and a b)))

(defun f-nand3 (a b c)
  (declare (xargs :guard t))
  (f-not (f-and a (f-and b c))))

(defun f-nand4 (a b c d)
  (declare (xargs :guard t))
  (f-not (f-and a (f-and b (f-and c d)))))

(defun f-nand5 (a b c d e)
  (declare (xargs :guard t))
  (f-not (f-and a (f-and b (f-and c (f-and d e))))))

(defun f-nand6 (a b c d e g)
  (declare (xargs :guard t))
  (f-not (f-and a (f-and b (f-and c (f-and d (f-and e g)))))))

(defun f-nand8 (a b c d e g h i)
  (declare (xargs :guard t))
  (f-not
   (f-and a (f-and b (f-and c (f-and d (f-and e (f-and g (f-and h i)))))))))

(defun f-or (a b)
  (declare (xargs :guard t))
  (if (or (equal a t) (equal b t))
      t
    (if (and (equal a nil) (equal b nil))
        nil
      *x*)))

(defthm 3vp-f-or
  (3vp (f-or a b))
  :rule-classes (:rewrite :type-prescription))

(defun f-or3 (a b c)
  (declare (xargs :guard t))
  (f-or a (f-or b c)))

(defun f-or4 (a b c d)
  (declare (xargs :guard t))
  (f-or a (f-or b (f-or c d))))

(defun f-nor (a b)
  (declare (xargs :guard t))
  (f-not (f-or a b)))

(defun f-nor3 (a b c)
  (declare (xargs :guard t))
  (f-not (f-or a (f-or b c))))

(defun f-nor4 (a b c d)
  (declare (xargs :guard t))
  (f-not (f-or a (f-or b (f-or c d)))))

(defun f-nor5 (a b c d e)
  (declare (xargs :guard t))
  (f-not (f-or a (f-or b (f-or c (f-or d e))))))

(defun f-nor6 (a b c d e g)
  (declare (xargs :guard t))
  (f-not (f-or a (f-or b (f-or c (f-or d (f-or e g)))))))

(defun f-nor8 (a b c d e g h i)
  (declare (xargs :guard t))
  (f-not
   (f-or a (f-or b (f-or c (f-or d (f-or e (f-or g (f-or h i)))))))))

(defun f-xor (a b)
  (declare (xargs :guard t))
  (if (equal a t)
      (f-not b)
    (if (equal a nil)
        (3v-fix b)
      *x*)))

(defun f-xor3 (a b c)
  (declare (xargs :guard t))
  (f-xor a (f-xor b c)))

(defun f-equv (a b)
  (declare (xargs :guard t))
  (if (equal a t)
      (3v-fix b)
    (if (equal a nil)
        (f-not b)
      *x*)))

(defun f-equv3 (a b c)
  (declare (xargs :guard t))
  (f-equv a (f-xor b c)))

(defun f-if (c a b)
  (declare (xargs :guard t))
  (if (equal c t)
      (3v-fix a)
    (if (equal c nil)
        (3v-fix b)
      *x*)))

(defthm 3vp-f-if
  (3vp (f-if c a b))
  :rule-classes (:rewrite :type-prescription))

(defun ft-buf (c a)
  (declare (xargs :guard t))
  (if (equal c t)
      (3v-fix a)
    (if (equal c nil)
        *z*
      *x*)))

(defun ft-wire (a b)
  (declare (xargs :guard t))
  (if (equal a b)
     (4v-fix a)
    (if (equal a *z*)
        (4v-fix b)
      (if (equal b *z*)
          (4v-fix a)
        *x*))))

(defun f-pullup (a)
  (declare (xargs :guard t))
  (if (equal a *z*)
      t
    (3v-fix a)))

;; We need this because we later use DEFUN-TO-MODULE to generate modules
;; containing references to AO2.

(defun f$ao2 (a b c d)
  (declare (xargs :guard t))
  (f-nor (f-and a b) (f-and c d)))

;; These two lemmas allow us to use F-BUF as a no-op.

(defthm f-buf-of-3vp
  (implies (3vp x)
           (equal (f-buf x)
                  x)))

(defthm f-buf-of-not-booleanp
  (implies (not (booleanp x))
           (equal (f-buf x)
                  *X*))
  :hints (("Goal" :in-theory (enable 3vp))))

;;  Some facts for those times when various "F-functions" are disabled.

(defthm f-and-rewrite
  (and (not (f-and nil x))
       (not (f-and x nil))
       (equal (f-and x t)
              (f-buf x))
       (equal (f-and t x)
              (f-buf x))
       (equal (f-and t t)
              t))
  :hints (("Goal" :in-theory (enable 3vp))))

(defthm f-or-rewrite
  (and (equal (f-or nil nil)
              nil)
       (equal (f-or t y) t)
       (equal (f-or x t) t)))

(defthm f-not-rewrite
  (and
   (equal (f-not t) nil)
   (equal (f-not nil) t)))

(defthm f-nand-rewrite
  (and (equal (f-nand nil x) t)
       (equal (f-nand x nil) t)
       (equal (f-nand x t)
              (f-not x))
       (equal (f-nand t x)
              (f-not x))
       (not (f-nand t t))))

(defthm ft-buf-rewrite
  (and
   (equal (ft-buf t x)
          (3v-fix x))
   (equal (ft-buf nil x)
          *z*)
   (equal (ft-buf c (3v-fix x))
          (ft-buf c x))
   (equal (ft-buf *x* x)
          *x*)))

(defthm f-if-rewrite
  (and
   (equal (f-if t a b)
          (f-buf a))
   (equal (f-if nil a b)
          (f-buf b))))

(defthm ft-wire-rewrite
  (and
   (equal (ft-wire *x* x)
          *x*)
   (equal (ft-wire x *x*)
          *x*)
   (equal (ft-wire x *z*)
          (4v-fix x))
   (equal (ft-wire *z* x)
          (4v-fix x))))

(defthm f-pullup-rewrite
  (and
   (equal (f-pullup t) t)
   (equal (f-pullup nil) nil)
   (equal (f-pullup *x*) *x*)
   (equal (f-pullup *z*) t)))

;; Leading up to a rewrite rule to get rid of extra F-BUF's.

(defthmd 3v-fix-help-lemma
  (and
   (equal (3v-fix nil) nil)
   (equal (3v-fix t) t)
   (equal (3v-fix *x*) *x*)
   (equal (3v-fix (f-buf x))    (3v-fix x))
   (equal (3v-fix (f-not x))    (f-not x))
   (equal (3v-fix (f-and x y))  (f-and x y))
   (equal (3v-fix (f-or x y))   (f-or x y))
   (equal (3v-fix (f-xor x y))  (f-xor x y))
   (equal (3v-fix (f-equv x y)) (f-equv x y))))

(defthmd f-not-f-not=f-buf
  (equal (f-not (f-not x))
         (f-buf x))
  :hints (("Goal" :in-theory (enable 3vp))))

(defthmd f-not-f-buf=f-not
  (equal (f-not (f-buf x))
         (f-not x)))

(defthmd f-buf-delete-lemmas
  (and
   (equal (f-buf (f-buf a))
          (f-buf a))
   (equal (f-buf (f-not a))
          (f-not a))
   (equal (f-buf (f-nand a b))
          (f-nand a b))
   (equal (f-buf (f-nand3 a b c))
          (f-nand3 a b c))
   (equal (f-buf (f-nand4 a b c d))
          (f-nand4 a b c d))
   (equal (f-buf (f-nand5 a b c d e))
          (f-nand5 a b c d e))
   (equal (f-buf (f-nand6 a b c d e g))
          (f-nand6 a b c d e g))
   (equal (f-buf (f-nand8 a b c d e g h i))
          (f-nand8 a b c d e g h i))
   (equal (f-buf (f-or a b))
          (f-or a b))
   (equal (f-buf (f-or3 a b c))
          (f-or3 a b c))
   (equal (f-buf (f-or4 a b c d))
          (f-or4 a b c d))
   (equal (f-buf (f-xor a b))
          (f-xor a b))
   (equal (f-buf (f-xor3 a b c))
          (f-xor3 a b c))
   (equal (f-buf (f-equv a b))
          (f-equv a b))
   (equal (f-buf (f-equv3 a b c))
          (f-equv3 a b c))
   (equal (f-buf (f-and a b))
          (f-and a b))
   (equal (f-buf (f-and3 a b c))
          (f-and3 a b c))
   (equal (f-buf (f-and4 a b c d))
          (f-and4 a b c d))
   (equal (f-buf (f-nor a b))
          (f-nor a b))
   (equal (f-buf (f-nor3 a b c))
          (f-nor3 a b c))
   (equal (f-buf (f-nor4 a b c d))
          (f-nor4 a b c d))
   (equal (f-buf (f-nor5 a b c d e))
          (f-nor5 a b c d e))
   (equal (f-buf (f-nor6 a b c d e g))
          (f-nor6 a b c d e g))
   (equal (f-buf (f-nor8 a b c d e g h i))
          (f-nor8 a b c d e g h i))
   (equal (f-buf (f-if c a b))
          (f-if c a b))))

(defthmd f-gate-3v-fix-congruence-lemmas$help
  (and
   (equal (f-buf (3v-fix a))
          (f-buf a))
   (equal (f-not (3v-fix a))
          (f-not a))
   (equal (f-or (3v-fix a) b)
          (f-or a b))
   (equal (f-or a (3v-fix b))
          (f-or a b))
   (equal (f-xor (3v-fix a) b)
          (f-xor a b))
   (equal (f-xor a (3v-fix b))
          (f-xor a b))
   (equal (f-equv (3v-fix a) b)
          (f-equv a b))
   (equal (f-equv a (3v-fix b))
          (f-equv a b))
   (equal (f-and (3v-fix a) b)
          (f-and a b))
   (equal (f-and a (3v-fix b))
          (f-and a b))
   (equal (f-if (3v-fix c) a b)
          (f-if c a b))
   (equal (f-if c (3v-fix a) b)
          (f-if c a b))
   (equal (f-if c a (3v-fix b))
          (f-if c a b))))

(defthmd f-gate-3v-fix-congruence-lemmas
  (and
   (equal (f-buf (3v-fix a))
          (f-buf a))

   (equal (f-not (3v-fix a))
          (f-not a))

   (equal (f-nand (3v-fix a) b)
          (f-nand a b))
   (equal (f-nand a (3v-fix b))
          (f-nand a b))

   (equal (f-nand3 (3v-fix a) b c)
          (f-nand3 a b c))
   (equal (f-nand3 a (3v-fix b) c)
          (f-nand3 a b c))
   (equal (f-nand3 a (3v-fix b) c)
          (f-nand3 a b c))

   (equal (f-nand4 (3v-fix a) b c d)
          (f-nand4 a b c d))
   (equal (f-nand4 a (3v-fix b) c d)
          (f-nand4 a b c d))
   (equal (f-nand4 a b (3v-fix c) d)
          (f-nand4 a b c d))
   (equal (f-nand4 a b c (3v-fix d))
          (f-nand4 a b c d))

   (equal (f-nand5 (3v-fix a) b c d e)
          (f-nand5 a b c d e))
   (equal (f-nand5 a (3v-fix b) c d e)
          (f-nand5 a b c d e))
   (equal (f-nand5 a b (3v-fix c) d e)
          (f-nand5 a b c d e))
   (equal (f-nand5 a b c (3v-fix d) e)
          (f-nand5 a b c d e))
   (equal (f-nand5 a b c d (3v-fix e))
          (f-nand5 a b c d e))

   (equal (f-nand6 (3v-fix a) b c d e g)
          (f-nand6 a b c d e g))
   (equal (f-nand6 a (3v-fix b) c d e g)
          (f-nand6 a b c d e g))
   (equal (f-nand6 a b (3v-fix c) d e g)
          (f-nand6 a b c d e g))
   (equal (f-nand6 a b c (3v-fix d) e g)
          (f-nand6 a b c d e g))
   (equal (f-nand6 a b c d (3v-fix e) g)
          (f-nand6 a b c d e g))
   (equal (f-nand6 a b c d e (3v-fix g))
          (f-nand6 a b c d e g))

   (equal (f-nand8 (3v-fix a) b c d e g h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a (3v-fix b) c d e g h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b (3v-fix c) d e g h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b c (3v-fix d) e g h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b c d (3v-fix e) g h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b c d e (3v-fix g) h i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b c d e g (3v-fix h) i)
          (f-nand8 a b c d e g h i))
   (equal (f-nand8 a b c d e g h (3v-fix i))
          (f-nand8 a b c d e g h i))

   (equal (f-or (3v-fix a) b)
          (f-or a b))
   (equal (f-or a (3v-fix b))
          (f-or a b))

   (equal (f-or3 (3v-fix a) b c)
          (f-or3 a b c))
   (equal (f-or3 a (3v-fix b) c)
          (f-or3 a b c))
   (equal (f-or3 a (3v-fix b) c)
          (f-or3 a b c))

   (equal (f-or4 (3v-fix a) b c d)
          (f-or4 a b c d))
   (equal (f-or4 a (3v-fix b) c d)
          (f-or4 a b c d))
   (equal (f-or4 a b (3v-fix c) d)
          (f-or4 a b c d))
   (equal (f-or4 a b c (3v-fix d))
          (f-or4 a b c d))

   (equal (f-xor (3v-fix a) b)
          (f-xor a b))
   (equal (f-xor a (3v-fix b))
          (f-xor a b))

   (equal (f-xor3 (3v-fix a) b c)
          (f-xor3 a b c))
   (equal (f-xor3 a (3v-fix b) c)
          (f-xor3 a b c))
   (equal (f-xor3 a (3v-fix b) c)
          (f-xor3 a b c))

   (equal (f-equv (3v-fix a) b)
          (f-equv a b))
   (equal (f-equv a (3v-fix b))
          (f-equv a b))

   (equal (f-equv3 (3v-fix a) b c)
          (f-equv3 a b c))
   (equal (f-equv3 a (3v-fix b) c)
          (f-equv3 a b c))
   (equal (f-equv3 a (3v-fix b) c)
          (f-equv3 a b c))

   (equal (f-and (3v-fix a) b)
          (f-and a b))
   (equal (f-and a (3v-fix b))
          (f-and a b))

   (equal (f-and3 (3v-fix a) b c)
          (f-and3 a b c))
   (equal (f-and3 a (3v-fix b) c)
          (f-and3 a b c))
   (equal (f-and3 a (3v-fix b) c)
          (f-and3 a b c))

   (equal (f-and4 (3v-fix a) b c d)
          (f-and4 a b c d))
   (equal (f-and4 a (3v-fix b) c d)
          (f-and4 a b c d))
   (equal (f-and4 a b (3v-fix c) d)
          (f-and4 a b c d))
   (equal (f-and4 a b c (3v-fix d))
          (f-and4 a b c d))

   (equal (f-nor (3v-fix a) b)
          (f-nor a b))
   (equal (f-nor a (3v-fix b))
          (f-nor a b))

   (equal (f-nor3 (3v-fix a) b c)
          (f-nor3 a b c))
   (equal (f-nor3 a (3v-fix b) c)
          (f-nor3 a b c))
   (equal (f-nor3 a (3v-fix b) c)
          (f-nor3 a b c))

   (equal (f-nor4 (3v-fix a) b c d)
          (f-nor4 a b c d))
   (equal (f-nor4 a (3v-fix b) c d)
          (f-nor4 a b c d))
   (equal (f-nor4 a b (3v-fix c) d)
          (f-nor4 a b c d))
   (equal (f-nor4 a b c (3v-fix d))
          (f-nor4 a b c d))

   (equal (f-nor5 (3v-fix a) b c d e)
          (f-nor5 a b c d e))
   (equal (f-nor5 a (3v-fix b) c d e)
          (f-nor5 a b c d e))
   (equal (f-nor5 a b (3v-fix c) d e)
          (f-nor5 a b c d e))
   (equal (f-nor5 a b c (3v-fix d) e)
          (f-nor5 a b c d e))
   (equal (f-nor5 a b c d (3v-fix e))
          (f-nor5 a b c d e))

   (equal (f-nor6 (3v-fix a) b c d e g)
          (f-nor6 a b c d e g))
   (equal (f-nor6 a (3v-fix b) c d e g)
          (f-nor6 a b c d e g))
   (equal (f-nor6 a b (3v-fix c) d e g)
          (f-nor6 a b c d e g))
   (equal (f-nor6 a b c (3v-fix d) e g)
          (f-nor6 a b c d e g))
   (equal (f-nor6 a b c d (3v-fix e) g)
          (f-nor6 a b c d e g))
   (equal (f-nor6 a b c d e (3v-fix g))
          (f-nor6 a b c d e g))

   (equal (f-nor8 (3v-fix a) b c d e g h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a (3v-fix b) c d e g h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b (3v-fix c) d e g h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b c (3v-fix d) e g h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b c d (3v-fix e) g h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b c d e (3v-fix g) h i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b c d e g (3v-fix h) i)
          (f-nor8 a b c d e g h i))
   (equal (f-nor8 a b c d e g h (3v-fix i))
          (f-nor8 a b c d e g h i))

   (equal (f-if (3v-fix c) a b)
          (f-if c a b))
   (equal (f-if c (3v-fix a) b)
          (f-if c a b))
   (equal (f-if c a (3v-fix b))
          (f-if c a b))))

;; A 4-valued gate theory

(deftheory f-gates
  '(f-buf
    f-not
    f-nand f-nand3 f-nand4 f-nand5 f-nand6 f-nand8
    f-or f-or3 f-or4
    f-xor f-xor3
    f-equv f-equv3
    f-and f-and3 f-and4
    f-nor f-nor3 f-nor4 f-nor5 f-nor6 f-nor8
    f-if ft-buf ft-wire f-pullup))

;; When the F-GATES theory is disabled, the following lemma lets us substitute
;; a B-GATE for each F-GATE under assumptions that the inputs are Boolean.

(defthm f-gates=b-gates
  (and
   (implies (booleanp a) (equal (f-buf a) (b-buf a)))
   (implies (booleanp a) (equal (f-not a) (b-not a)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-nand a b) (b-nand a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-nand3 a b c) (b-nand3 a b c)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d))
            (equal (f-nand4 a b c d) (b-nand4 a b c d)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e))
            (equal (f-nand5 a b c d e) (b-nand5 a b c d e)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e)
                 (booleanp g))
            (equal (f-nand6 a b c d e g) (b-nand6 a b c d e g)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e)
                 (booleanp g) (booleanp h) (booleanp i))
            (equal (f-nand8 a b c d e g h i) (b-nand8 a b c d e g h i)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-or a b) (b-or a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-or3 a b c) (b-or3 a b c)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d))
            (equal (f-or4 a b c d) (b-or4 a b c d)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-xor a b) (b-xor a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-xor3 a b c) (b-xor3 a b c)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-equv a b) (b-equv a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-equv3 a b c) (b-equv3 a b c)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-and a b) (b-and a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-and3 a b c) (b-and3 a b c)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d))
            (equal (f-and4 a b c d) (b-and4 a b c d)))
   (implies (and (booleanp a) (booleanp b)) (equal (f-nor a b) (b-nor a b)))
   (implies (and (booleanp a) (booleanp b) (booleanp c))
            (equal (f-nor3 a b c) (b-nor3 a b c)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d))
            (equal (f-nor4 a b c d) (b-nor4 a b c d)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e))
            (equal (f-nor5 a b c d e) (b-nor5 a b c d e)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e)
                 (booleanp g))
            (equal (f-nor6 a b c d e g) (b-nor6 a b c d e g)))
   (implies (and (booleanp a) (booleanp b) (booleanp c) (booleanp d) (booleanp e)
                 (booleanp g) (booleanp h) (booleanp i))
            (equal (f-nor8 a b c d e g h i) (b-nor8 a b c d e g h i)))
   (implies (and (booleanp c) (booleanp a) (booleanp b))
            (equal (f-if c a b) (b-if c a b)))))

;; FV-OR

(defun fv-or (a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (f-or (car a) (car b))
          (fv-or (cdr a) (cdr b)))))

(defthm len-fv-or
  (equal (len (fv-or a b))
         (len a)))

(defthm fv-or=v-or
  (implies (and (bvp a)
                (bvp b)
                (equal (len a) (len b)))
           (equal (fv-or a b)
                  (v-or a b)))
  :hints (("Goal" :in-theory (enable bvp v-or))))

(in-theory (disable fv-or))

;; FV-XOR

(defun fv-xor (a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (f-xor (car a) (car b))
          (fv-xor (cdr a) (cdr b)))))

(defthm len-fv-xor
  (equal (len (fv-xor a b))
         (len a)))

(defthm fv-xor=v-xor
  (implies (and (bvp a)
                (bvp b)
                (equal (len a) (len b)))
           (equal (fv-xor a b)
                  (v-xor a b)))
  :hints (("Goal" :in-theory (enable bvp v-xor))))

(in-theory (disable fv-xor))

;; FV-IF

(defun fv-if (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (f-if c (car a) (car b))
          (fv-if c (cdr a) (cdr b)))))

(defthm len-fv-if
  (equal (len (fv-if c a b))
         (len a)))

(defthm v-threefix-fv-if
  (equal (v-threefix (fv-if c a b))
         (fv-if c a b)))

(defthm fv-if-when-booleanp-c
  (implies (equal (len a) (len b))
           (and
            (equal (fv-if t a b)
                   (v-threefix a))
            (equal (fv-if nil a b)
                   (v-threefix b)))))

(defthm fv-if-when-bvp
  (implies (and (booleanp c)
                (bvp a)
                (bvp b)
                (equal (len a) (len b)))
           (equal (fv-if c a b)
                  (if* c a b)))
  :hints (("Goal" :in-theory (enable bvp))))

;; Usually disabled to reduce splitting.
(defthmd fv-if-rewrite
  (implies (equal (len a) (len b))
           (equal (fv-if c a b)
                  (if (booleanp c)
                      (if c (v-threefix a) (v-threefix b))
                    (make-list (len a) :initial-element *x*))))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm fv-if-v-threefix
  (and
   (equal (fv-if c (v-threefix a) b)
          (fv-if c a b))
   (equal (fv-if c a (v-threefix b))
          (fv-if c a b))))

(in-theory (disable fv-if))

;; V-WIRE

(defun v-wire (a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      nil
    (cons (ft-wire (car a) (car b))
          (v-wire (cdr a) (cdr b)))))

(defthm v-wire-x-x=x
  (equal (v-wire x x)
         (v-fourfix x))
  :hints (("Goal" :in-theory (enable v-fourfix))))

(defthm v-wire-make-list-z-1
  (implies (equal (len v) n)
           (equal (v-wire (make-list n :initial-element *z*) v)
                  (v-fourfix v)))
  :hints (("Goal" :in-theory (enable v-fourfix))))

(defthm v-wire-make-list-z-2
  (implies (equal (len v) n)
           (equal (v-wire v (make-list n :initial-element *z*))
                  (v-fourfix v)))
  :hints (("Goal" :in-theory (enable v-fourfix))))

(defthm len-v-wire
  (equal (len (v-wire a b))
         (len a)))

(defthm v-wire-make-list-x
  (implies (equal n (len x))
           (equal (v-wire x (make-list n :initial-element *x*))
                  (make-list n :initial-element *x*)))
  :hints (("Goal" :in-theory (enable repeat))))

(in-theory (disable v-wire))

;; V-PULLUP

(defun v-pullup (v)
  (declare (xargs :guard t))
  (if (atom v)
      nil
    (cons (f-pullup (car v))
          (v-pullup (cdr v)))))

(defthm len-v-pullup
  (equal (len (v-pullup v))
         (len v)))

(defthm v-pullup-bvp
  (implies (bvp v)
           (equal (v-pullup v)
                  v))
  :hints (("Goal" :in-theory (enable bvp))))

(defthm v-pullup-make-list-z
   (equal (v-pullup (make-list n :initial-element *z*))
          (make-list n :initial-element t))
  :hints (("Goal" :in-theory (enable repeat))))

(in-theory (disable v-pullup))

;; FV-SHIFT-RIGHT

(defun fv-shift-right (a si)
  (declare (xargs :guard t))
  (if (atom a)
      nil
    (append (v-threefix (cdr a))
            (list (3v-fix si)))))

(defthm fv-shift-right=v-shift-right
  (implies (and (booleanp si)
                (bvp a))
           (equal (fv-shift-right a si)
                  (v-shift-right a si)))
  :hints (("Goal" :in-theory (enable bvp v-shift-right))))

(defthm len-fv-shift-right
  (equal (len (fv-shift-right a si))
         (len a)))

(defthm v-threefix-fv-shift-right
  (equal (v-threefix (fv-shift-right a si))
         (fv-shift-right a si))
  :hints (("Goal" :in-theory (e/d (v-threefix-append)
                                  (append-v-threefix)))))

(in-theory (disable fv-shift-right))

;; VFT-BUF - Vector tristate buffer.

(defun vft-buf (c a)
  (declare (xargs :guard t))
  (if (atom a)
      nil
    (cons (ft-buf c (car a))
          (vft-buf c (cdr a)))))

(defthm len-vft-buf
  (equal (len (vft-buf c a))
         (len a)))

(defthm vft-buf-lemmas
  (and
   (equal (vft-buf t a)
          (v-threefix a))
   (equal (vft-buf nil a)
          (make-list (len a) :initial-element *z*)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthmd vft-buf-rewrite
  (equal (vft-buf c a)
         (if (equal c t)
             (v-threefix a)
           (if (equal c nil)
               (make-list (len a) :initial-element *z*)
             (make-list (len a) :initial-element *x*))))
  :hints (("Goal" :in-theory (enable repeat))))

(in-theory (disable vft-buf))

;; FV-ADDER

(defun fv-adder (c a b)
  (declare (xargs :guard (true-listp b)))
  (if (atom a)
      (list (3v-fix c))
    (cons (f-xor3 c (car a) (car b))
          (fv-adder (f-or (f-and (car a) (car b))
                          (f-and (f-xor (car a) (car b))
                                 c))
                    (cdr a)
                    (cdr b)))))

(defthm len-fv-adder
  (equal (len (fv-adder c a b))
         (1+ (len a))))

(defthm v-threefix-fv-adder
  (equal (v-threefix (fv-adder c a b))
         (fv-adder c a b)))

(defthm fv-adder=v-adder
  (implies (and (booleanp c)
                (bvp a)
                (bvp b))
           (equal (fv-adder c a b)
                  (v-adder c a b)))
  :hints (("Goal" :in-theory (enable bvp v-adder))))

(in-theory (disable fv-adder f-gates))

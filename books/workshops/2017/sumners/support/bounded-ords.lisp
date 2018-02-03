; Copyright (C) 2017, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; bounded-ords.lisp

(in-package "ACL2")

(local (include-book "arithmetic/top-with-meta" :dir :system))

#|

We define here a book of "bounded-ordinals" in support of the definitions in
"trans-theory.lisp".

Acronyms:

bnl  -- bounded natural list  (all naturals and last cdr is natural)
bpl  -- bounded positive list (all naturals but last cdr is positive)
bnll -- a list of bnl's
bpll -- a list of bpl's

At the base, we have bounded-length ((len x) = b) lists of natural numbers where
the last cdr is either a natural number (bnlp x b) or a positive number (bplp x b).

We define an ordering (bnl< x y b) and a mapping to ordinals (bnl->o x b) and prove
(roughly) that (o-p (bnl->o x b)) and (iff (o< (bnl->o x b) (bnl->o y b)) 
(bnl< x y b)). With these definitions, we can use bnl< (a lexicographic ordering over
the bounded lists) and get a well-ordering through bnl->o.

Similar to bnl, we do something similar bnll.. we define an ordering (bnll< x y
b) and a mapping to ordinals (bnll->o x b) and prove (again roughly)
that (o-p (bnll-> x b)) and (iff (o< (bnll->o x b) (bnll->o y b)) (bnll< x y b)).

We also define all of the necessary arithmetic (but not necessarily complete)
for these operations.. primarily relating a summation operator bnl+ to bnl< and
bnl<= with some properties about a zero value bnl0 as well..

|#

(defun bplp (x b)
  (if (zp b) (posp x)
    (and (consp x)
         (natp (car x))
         (bplp (cdr x) (1- b)))))

(defun bnlp (x b)
  (if (zp b) (natp x)
    (and (consp x)
         (natp (car x))
         (bnlp (cdr x) (1- b)))))

(defun bnl< (x y b)
  (declare (xargs :measure (nfix b)))
  (if (zp b) (< x y)
    (or (< (car x) (car y))
        (and (= (car x) (car y))
             (bnl< (cdr x) (cdr y) (1- b))))))

(defun bnl<= (x y b)
  (declare (xargs :measure (nfix b)))
  (if (zp b) (<= x y)
    (or (< (car x) (car y))
        (and (= (car x) (car y))
             (bnl<= (cdr x) (cdr y) (1- b))))))

(defun bnl0 (b)
  (if (zp b) 0 (cons 0 (bnl0 (1- b)))))

(defun bnl1 (b)
  (if (zp b) 1 (cons 0 (bnl1 (1- b)))))

(defun bnl+ (x y b)
  (declare (xargs :measure (nfix b)))
  (if (zp b) (+ x y)
    (cons (+ (car x) (car y))
          (bnl+ (cdr x) (cdr y) (1- b)))))

(defthm bplp-bnlp
  (implies (bplp x b) (bnlp x b)))

(defthm bnl0-bnlp
  (bnlp (bnl0 b) b))

(defthm bnl1-bplp
  (bplp (bnl1 b) b))

(defthm bnl<-trans
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b)
                (bnl< x y b)
                (bnl< y z b))
           (bnl< x z b)))

(defthm bnl<-bnl+
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b)
                (bnl< x y b))
           (bnl< (bnl+ x z b)
                 (bnl+ y z b)
                 b)))

(defthm bnl<-bnl+-2
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b)
                (bnl< x y b))
           (bnl< (bnl+ z x b)
                 (bnl+ z y b)
                 b)))

(defthm bnl<-bnl+-3
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (bnl< (bnl+ z x b)
                        (bnl+ z y b)
                        b)
                  (bnl< x y b))))

(defthm bnl<-bnl+-4
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (bnl< (bnl+ x z b)
                        (bnl+ y z b)
                        b)
                  (bnl< x y b))))

(defthm bnl<-bnl+-5
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp m b)
                (bnlp n b)
                (or (and (bnl<= x m b)
                         (bnl<= y n b))
                    (and (bnl<= x n b)
                         (bnl<= y m b))))
           (bnl<= (bnl+ x y b)
                  (bnl+ m n b)
                  b)))

(defthm bnl<-bnl+-6
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp m b)
                (bnlp n b)
                (or (and (bnl< x m b)
                         (bnl<= y n b))
                    (and (bnl< x n b)
                         (bnl<= y m b))))
           (bnl< (bnl+ x y b)
                 (bnl+ m n b)
                 b)))

(defthm bnl<-bnl+-7
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp m b)
                (bnlp n b)
                (or (and (bnl<= x m b)
                         (bnl< y n b))
                    (and (bnl<= x n b)
                         (bnl< y m b))))
           (bnl< (bnl+ x y b)
                 (bnl+ m n b)
                 b)))

(defthm bnl<-bnl+-8
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (bnl<= (bnl+ z x b)
                         (bnl+ z y b)
                         b)
                  (bnl<= x y b))))

(defthm bnl<-bnl+-9
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (bnl<= (bnl+ x z b)
                         (bnl+ y z b)
                         b)
                  (bnl<= x y b))))

(defthm bnl+-equal-redx1
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (equal (bnl+ x z b)
                         (bnl+ y z b))
                  (equal x y))))

(defthm bnl+-equal-redx2
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (equal (bnl+ z x b)
                         (bnl+ z y b))
                  (equal x y))))

(defthm bnl+-equal-redx3
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (equal (bnl+ x z b)
                         (bnl+ z y b))
                  (equal x y))))

(defthm bnl+-equal-redx4
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (equal (bnl+ z x b)
                         (bnl+ y z b))
                  (equal x y))))

(defthm bpl-never-equal-bnl0
  (implies (bplp x b)
           (not (equal x (bnl0 b)))))

(defthm bnl+-bnl0-redx1
  (implies (bnlp x b)
           (equal (bnl+ (bnl0 b) x b) x)))

(defthm bnl+-bnl0-redx2
  (implies (bnlp x b)
           (equal (bnl+ x (bnl0 b) b) x)))

(defthm bnl<-impl-bnl<=
  (implies (bnl< x y b)
           (bnl<= x y b)))

(defthm bnl<=-total
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnl<= x y b)
                (not (equal x y)))
           (not (bnl<= y x b))))

(defthm bnl<=-bnl+-bnllp
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnl<= x y b)
                (bnlp z b))
           (bnl<= x (bnl+ y z b) b)))

(defthm bnl<-bnl+-bpllp
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnl<= x y b)
                (bplp z b))
           (bnl< x (bnl+ y z b) b)))

(defthm equal-bnl+-same-redx1
  (implies (and (bnlp x b)
                (bnlp y b))
           (equal (equal (bnl+ x y b) x)
                  (equal y (bnl0 b)))))

(defthm equal-bnl+-same-redx2
  (implies (and (bnlp x b)
                (bnlp y b))
           (equal (equal (bnl+ y x b) x)
                  (equal y (bnl0 b)))))

(defthm bnl<=-idempotent
  (bnl<= x x b))

(defthm bnl<-total
  (implies (and (bnlp x b)
                (bnlp y b)
                (not (bnl< x y b))
                (not (equal x y)))
           (bnl< y x b)))

(defthm bnl<-assym
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnl< x y b))
           (not (bnl< y x b))))

(defthm bnl<-irref
  (not (bnl< x x b)))

(defthm bnlp-bnl0
  (bnlp (bnl0 b) b))

(defthm bplp-bnl0
  (implies (bplp x b)
           (bnl< (bnl0 b) x b)))

(defthm bnl+-bnl0
  (implies (bnlp x b)
           (equal (bnl+ x (bnl0 b) b) x)))

(defthm bnl+-comm
  (implies (and (bnlp x b)
                (bnlp y b))
           (equal (bnl+ x y b)
                  (bnl+ y x b)))
  :rule-classes ((:rewrite :loop-stopper ((x y bnl+)))))

(defthm bnl+-assoc
  (implies (and (bnlp x b)
                (bnlp y b)
                (bnlp z b))
           (equal (bnl+ (bnl+ x y b) z b)
                  (bnl+ x (bnl+ y z b) b))))

(defthm bnl+-bplp1
  (implies (and (natp b)
                (bplp x b)
                (bnlp y b))
           (bplp (bnl+ x y b) b)))


(defthm bnl+-bplp2
  (implies (and (natp b)
                (bnlp x b)
                (bplp y b))
           (bplp (bnl+ x y b) b)))

;(defthm bnl+-bplp
;  (implies (and (

(defun bnll< (x y b)
  (and (consp y)
       (or (atom x)
           (bnl< (car x) (car y) b)
           (and (equal (car x) (car y))
                (bnll< (cdr x) (cdr y) b)))))

(defun bnll<= (x y b)
  (or (atom x)
      (and (consp y)
           (or (bnl< (car x) (car y) b)
               (and (equal (car x) (car y))
                    (bnll<= (cdr x) (cdr y) b))))))

(defun bpllp (x b)
  (or (null x)
      (and (consp x)
           (bplp (car x) b)
           (bpllp (cdr x) b))))

(defun bnllp (x b)
  (or (null x)
      (and (consp x)
           (bnlp (car x) b)
           (bnllp (cdr x) b))))

(defthm bnll<=-bnll<-check
  (implies (and (bnllp x b) (bnllp y b))
           (iff (not (bnll< x y b)) (bnll<= y x b)))
  :rule-classes nil)

(defun bnl->o (l b)
  (if (zp b) l
    (make-ord b (1+ (car l))
              (bnl->o (cdr l) (1- b)))))

(defun bnll->o (n l b)
  (cond ((zp n) 0)
        ((atom l)
         (make-ord (make-ord (+ n b) 1
                             (bnl->o (bnl0 b) b))
                   1 (bnll->o (1- n) () b)))
        (t
         (make-ord (make-ord (+ n b) 1
                             (bnl->o (car l) b))
                   1 (bnll->o (1- n) (cdr l) b)))))

(defthm bnl->o-caar
  (implies (and (consp (bnl->o l b)) (bnlp l b))
           (equal (car (car (bnl->o l b))) b)))

(defthm bnl->o-cdar
  (implies (and (consp l) (bnlp l b))
           (equal (cdr (car (bnl->o l b))) (1+ (car l)))))

(defthm bnl->o-consp
  (implies (not (zp b))
           (consp (bnl->o l b)))
  :rule-classes :type-prescription)

(defthm bnll->o-caar1
  (implies (and (consp (bnll->o n l b))
                (consp l))
           (equal (car (car (bnll->o n l b)))
                  (make-ord (+ n b) 1 (bnl->o (car l) b)))))

(defthm bnll->o-caar2
  (implies (and (consp (bnll->o n l b))
                (atom l))
           (equal (car (car (bnll->o n l b)))
                  (make-ord (+ n b) 1 (bnl->o (bnl0 b) b)))))

(defthm bnll->o-cdar
  (implies (not (zp n))
           (equal (cdr (car (bnll->o n l b))) 1)))

(defthm bnll->o-consp
  (implies (not (zp n))
           (consp (bnll->o n l b)))
  :rule-classes :type-prescription)

(defthm bnl->o-is-ord
  (implies (bnlp l b)
           (o-p (bnl->o l b)))
  :hints (("Goal" :in-theory (enable o-p o<))
          ("Subgoal *1/3" :in-theory (disable bnl->o-caar)
           :use ((:instance bnl->o-caar
                            (l (cdr l))
                            (b (+ -1 b)))))))

(defthm bnll->o-is-ord
  (implies (and (bnllp l b) (natp n) (natp b))
           (o-p (bnll->o n l b)))
  :hints (("Goal" :in-theory (enable o-p o<))
          ("Subgoal *1/7" :cases ((consp (cdr l))))))

(defthm bnl->o-bplp
  (implies (bplp y b)
           (o< (bnl->o (bnl0 b) b)
               (bnl->o y b))))

(defthm bpllp-bnllp
  (implies (bpllp x b) (bnllp x b)))

(defthm bnll->o-bpllp
  (implies (and (consp y)
                (not (zp n))
                (bpllp y b))
           (o< (bnll->o n nil b)
               (bnll->o n y b)))
    :hints (("Goal" :in-theory (enable o<))))

(defthm bnl<-implies-o<-bnl->o
  (implies (and (bnlp x b)
                (bnlp y b)
                (natp b)
                (bnl< x y b))
           (o< (bnl->o x b) (bnl->o y b)))
  :hints (("Goal" :in-theory (enable o<))))

(local
(defthm implies-op<-not-equal
  (implies (and (o-p x)
                (o-p y)
                (o< x y))
           (not (equal x y)))))

(defthm bnll->o-cdr
  (implies (not (zp n))
           (equal (cdr (bnll->o n x b))
                  (bnll->o (1- n) (cdr x) b))))

(defthm bnll<-implies-o<-bnll->o
  (implies (and (bpllp x b)
                (bpllp y b)
                (natp b)
                (natp n)
                (<= (len y) n)
                (<= (len x) n)
                (bnll< x y b))
           (o< (bnll->o n x b) (bnll->o n y b)))
  :hints (("Goal" :in-theory (enable o<))))

(defthm o<-implies-o<=
  (implies (o< x y) (o<= x y)))

(defthm o-p-o<=-idemp
  (implies (o-p x) (o<= x x)))

(defthm bnll<=-implies-o<=-bnll->o
  (implies (and (bpllp x b)
                (bpllp y b)
                (natp b)
                (natp n)
                (<= (len y) n)
                (<= (len x) n)
                (bnll<= x y b))
           (o<= (bnll->o n x b) (bnll->o n y b)))
  :hints (("Goal" :in-theory (enable o<))
          ("Subgoal *1/13"
           :in-theory (disable bnl<-implies-o<-bnl->o
                               implies-op<-not-equal
                               bnl->o-is-ord)
           :use ((:instance implies-op<-not-equal
                            (x (bnl->o (car y) b))
                            (y (bnl->o (car x) b)))
                 (:instance bnl<-implies-o<-bnl->o
                            (x (car x))
                            (y (car y)))
                 (:instance bnl->o-is-ord
                            (l (car x)))
                 (:instance bnl->o-is-ord
                            (l (car y)))))))

(defun induct-2-n (x y n)
  (cond ((zp n) t)
        ((and (atom x) (atom y)) t)
        ((atom x) (induct-2-n x (cdr y) (1- n)))
        ((atom y) (induct-2-n (cdr x) y (1- n)))
        (t (induct-2-n (cdr x) (cdr y) (1- n)))))

(defthm =-bnll->o-implies-equal
  (implies (and (bpllp x b)
                (bpllp y b)
                (natp b)
                (natp n)
                (<= (len y) n)
                (<= (len x) n)
                (equal (bnll->o n x b) (bnll->o n y b)))
           (equal x y))
  :hints (("Goal" :induct (induct-2-n x y n)
           :in-theory (enable o<)))
  :rule-classes nil)


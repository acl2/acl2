; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; bounded-ords.lisp

(in-package "ACL2")

(include-book "std/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

#|

We define here a book of "bounded-ordinals" in support of wfo-thry and cycle-check:

Acronyms:

bnl  -- bounded natural list  (all naturals and last cdr is natural)
bpl  -- bounded positive list (all naturals but last cdr is positive)
        -- important subset of bnl which excludes a bottom element of all-0s
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
  
(define bplp (x (b natp))
  :enabled t
  (if (zp b) (posp x)
    (and (consp x)
         (natp (car x))
         (bplp (cdr x) (1- b)))))

(define bnlp (x (b natp))
  :enabled t
  (if (zp b) (natp x)
    (and (consp x)
         (natp (car x))
         (bnlp (cdr x) (1- b)))))

(define bnl< (x y (b natp))
  :measure (nfix b)
  :guard (and (bnlp x b) (bnlp y b))
  :enabled t
  (if (zp b) (< x y)
    (or (< (car x) (car y))
        (and (= (car x) (car y))
             (bnl< (cdr x) (cdr y) (1- b))))))

(define bnl<= (x y (b natp))
  :measure (nfix b)
  :guard (and (bnlp x b) (bnlp y b))
  :enabled t
  (if (zp b) (<= x y)
    (or (< (car x) (car y))
        (and (= (car x) (car y))
             (bnl<= (cdr x) (cdr y) (1- b))))))

(define bnl0 ((b natp))
  :enabled t
  :returns (r (bnlp r b))
  (if (zp b) 0 (cons 0 (bnl0 (1- b)))))

(define bnl1 ((b natp))
  :enabled t
  :returns (r (bplp r b))
  (if (zp b) 1 (cons 0 (bnl1 (1- b)))))

(define bnl+ (x y (b natp))
  :measure (nfix b)
  :guard (and (bnlp x b) (bnlp y b))
  :enabled t
  :returns (r (bnlp r b) :hyp :guard)
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

(define bpllp (x (b natp))
  :enabled t
  (or (null x)
      (and (consp x)
           (bplp (car x) b)
           (bpllp (cdr x) b))))

(define bnllp (x (b natp))
  :enabled t
  (or (null x)
      (and (consp x)
           (bnlp (car x) b)
           (bnllp (cdr x) b))))

(define bnll< (x y (b natp))
  :guard (and (bnllp x b) (bnllp y b))
  :enabled t
  (and (consp y)
       (or (atom x)
           (bnl< (car x) (car y) b)
           (and (equal (car x) (car y))
                (bnll< (cdr x) (cdr y) b)))))

(define bnll<= (x y (b natp))
  :guard (and (bnllp x b) (bnllp y b))
  :enabled t
  (or (atom x)
      (and (consp y)
           (or (bnl< (car x) (car y) b)
               (and (equal (car x) (car y))
                    (bnll<= (cdr x) (cdr y) b))))))

(defthm bnll<=-bnll<-check
  (implies (and (bnllp x b) (bnllp y b))
           (iff (not (bnll< x y b)) (bnll<= y x b)))
  :rule-classes nil)

(define bnl->o (l (b natp))
  :guard (bnlp l b)
  :enabled t
  :verify-guards nil
  (if (zp b) l
    (make-ord b (1+ (car l))
              (bnl->o (cdr l) (1- b)))))

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

(defthm bnl->o-is-ord
  (implies (bnlp l b)
           (o-p (bnl->o l b)))
  :hints (("Goal" :in-theory (enable o-p o<))
          ("Subgoal *1/3" :in-theory (disable bnl->o-caar)
           :use ((:instance bnl->o-caar
                            (l (cdr l))
                            (b (+ -1 b)))))))

(verify-guards bnl->o)

;;;

(define bnll->o ((n natp) l (b natp))
  :guard (bnllp l b)
  :enabled t
  :verify-guards nil
  (cond ((zp n) 0)
        ((atom l)
         (make-ord (make-ord (+ n b) 1
                             (bnl->o (bnl0 b) b))
                   1 (bnll->o (1- n) () b)))
        (t
         (make-ord (make-ord (+ n b) 1
                             (bnl->o (car l) b))
                   1 (bnll->o (1- n) (cdr l) b)))))


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

(defthm bnll->o-is-ord
  (implies (and (bnllp l b) (natp n) (natp b))
           (o-p (bnll->o n l b)))
  :hints (("Goal" :in-theory (enable o-p o<))
          ("Subgoal *1/7" :cases ((consp (cdr l))))))

(verify-guards bnll->o)

;;;

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

;;;;;;;;;;;;;;;;;;;
; we add a conversion from bpll's (bounded in len) to bpl's..
; .. this is important for proving allowing compositions of bplls
; .. to be reintroduced as bnlls (with suitable bounds) and connects
; .. these two together in the obvious hierarchy.. use bplls in contexts
; .. where it isn't clear beforehand what the length of the lists should be
; .. but once the lists have been determined and a maximum length can be
; .. calculated, you can then convert into bpls which can be used in composing
; .. bplls at a higher level, repeat..
;;;;;;

(define nat->bpl ((a natp) (b natp))
  :returns (r (bplp r b))
  :enabled t
  (if (zp b) (1+ (lnfix a)) (cons 0 (nat->bpl a (1- b)))))

(defthm nat->bpl-bpl<-redux
  (implies (and (natp x) (natp y))
           (iff (bnl< (nat->bpl x b) (nat->bpl y b) b)
                (< x y))))

(define app-bpl (x y)
  :enabled t
  (if (atom x) (cons x y)
    (cons (first x) (app-bpl (rest x) y))))

(local 
 (defthm len-app-bpl
   (equal (len (app-bpl x y))
          (+ (1+ (len x)) (len y)))))

(defthm app-bpl-equal-preserve
  (iff (equal (app-bpl x y)
              (app-bpl x z))
       (equal y z)))

(defthm bplp-app-bpl
  (implies (and (natp b)
                (natp c)
                (bnlp x b)
                (bplp y c))
           (bplp (app-bpl x y)
                 (+ (1+ b) c)))
  :hints (("Goal" :in-theory (enable bplp)))
  :rule-classes nil)

(defthm app-bpl-bnl<-transfer
  (implies (and (natp b)
                (natp c)
                (bnlp w b)
                (bnlp x b)
                (bplp y c)
                (bplp z c))
           (equal (bnl< (app-bpl w y)
                        (app-bpl x z)
                        (+ (1+ b) c))
                  (or (bnl< w x b)
                      (and (equal w x)
                           (bnl< y z c)))))
  :hints (("Goal" :in-theory (enable bnl< bplp)))
  :rule-classes nil)

(define bpll->bpl (x (n natp) (b natp))
  :guard (bpllp x b)
  (if (zp n) 1
    (app-bpl (if (atom x) (bnl0 b) (first x))
             (bpll->bpl (rest x) (1- n) b))))

(local 
 (defthm dumb-linear-fact1
   (implies (and (natp n) (natp b)
                 (< 0 n))
            (<= b (* b n)))
   :rule-classes :linear))

;; We need to prove that bpll->bpl produces a bplp of a suitable size
;; and that bnll< transfers to bnl< on the result..

(encapsulate 
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm bpll->bpl-is-bplp
   (implies (and (natp n) 
                 (natp b)
                 (bpllp x b))
            (bplp (bpll->bpl x n b)
                  (* n (1+ b))))
   :hints (("Goal" :in-theory (enable bpll->bpl))
           ("Subgoal *1/5" :use ((:instance bplp-app-bpl
                                            (x (car x))
                                            (y (bpll->bpl (cdr x) (1- n) b))
                                            (b b)
                                            (c (+ -1 (- b) n (* b n))))
                                 (:instance bplp-app-bpl
                                            (x (bnl0 b))
                                            (y (bpll->bpl (cdr x) (1- n) b))
                                            (b b)
                                            (c (+ -1 (- b) n (* b n)))))))
   :rule-classes nil)
 )

(defthm app-bpl-bnl-first
  (implies (and (natp b)
                (posp c)
                (bnlp w b)
                (bnlp x b)
                (bnl< w x b))
           (bnl< (app-bpl w y)
                 (app-bpl x z)
                 (+ b c)))
  :hints (("Goal" :in-theory (enable app-bpl bnl<)))
  ;; This rule can't match on (+ b c) :( -- so we need to disable and
  ;; instantiate it below..
  :rule-classes nil)

(defthm bpll->bpl-bnll<-transfer
  (implies (and (natp n) 
                (natp b)
                (bpllp x b) 
                (bpllp y b)
                (<= (len x) n)
                (<= (len y) n)
                (bnll< x y b))
           (bnl< (bpll->bpl x n b)
                 (bpll->bpl y n b)
                 (* n (1+ b))))
  :hints (("Goal" :in-theory (enable bpllp bpll->bpl bnll<))
          ("Subgoal *1/8" :use ((:instance app-bpl-bnl<-transfer
                                           (b b)
                                           (c (+ -1 (- b) n (* b n)))
                                           (w (car x))
                                           (x (car y))
                                           (y (bpll->bpl (cdr x) (1- n) b))
                                           (z (bpll->bpl (cdr y) (1- n) b)))
                                (:instance app-bpl-bnl-first
                                           (b b)
                                           (c (+ (- b) n (* b n)))
                                           (w (bnl0 b))
                                           (x (car y))
                                           (y (bpll->bpl (cdr x) (1- n) b))
                                           (z (bpll->bpl (cdr y) (1- n) b)))
                                (:instance bpll->bpl-is-bplp
                                           (x (cdr x)) (n (1- n)))
                                (:instance bpll->bpl-is-bplp
                                           (x (cdr y)) (n (1- n)))))
          ("Subgoal *1/7" :use ((:instance app-bpl-bnl-first
                                           (b b)
                                           (c (+ (- b) n (* b n)))
                                           (w (bnl0 b))
                                           (x (car y))
                                           (y (bpll->bpl (cdr x) (1- n) b))
                                           (z (bpll->bpl (cdr y) (1- n) b)))
                                (:instance app-bpl-bnl-first
                                           (b b)
                                           (c (+ (- b) n (* b n)))
                                           (w (car x))
                                           (x (car y))
                                           (y (bpll->bpl (cdr x) (1- n) b))
                                           (z (bpll->bpl (cdr y) (1- n) b))))))
  :rule-classes nil)
                                           
;;;;
;; Finally, we add a function which zero-extends a bpl to a larger length while preserving
;; bnl< and bplp:
;;;;

(define bpl-pad (x (b natp) (c natp))
  :guard (>= c b)
  :measure (nfix (- c b))
  (if (zp (- c b)) x (cons 0 (bpl-pad x b (1- c)))))

(defthm bpl-pad-bplp
  (implies (and (natp b)
                (natp c)
                (<= b c)
                (bplp x b))
           (bplp (bpl-pad x b c) c))
  :hints (("Goal" :in-theory (enable bpl-pad bplp))))

(defthm bpl-pad-bnl-<-transfer
  (implies (and (natp b)
                (natp c)
                (<= b c)
                (bplp x b)
                (bplp y b))
           (equal (bnl< (bpl-pad x b c) (bpl-pad y b c) c)
                  (bnl< x y b)))
  :hints (("Goal" :in-theory (enable bpl-pad bnl< bplp))))

(defthm bpl-pad-=-transfer
  (implies (and (natp b)
                (natp c)
                (<= b c)
                (bplp x b)
                (bplp y b))
           (iff (equal (bpl-pad x b c) (bpl-pad y b c))
                (equal x y)))
  :hints (("Goal" :in-theory (enable bpl-pad bplp))))

  

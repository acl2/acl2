; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "HOL")

(include-book "../acl2/theories")

(open-theory eval-poly)

; Here is the translator input, from a comment in ../hol/eval-poly.sml.

#|
val basis_defs =
   [⊢ (∀x y. (if T then x else y) = x) ∧ ∀x y. (if F then x else y) = y,
    ⊢ ∀x y. COMMA x y = (x,y),
    ⊢ ∀h t. HD (h::t) = h,
    ⊢ (NULL [] ⇔ T) ∧ ∀h t. NULL (h::t) ⇔ F,
    ⊢ ∀m. SUC m = 1 + m,
    ⊢ ∀x y. x ≤ y ⇔ x < y ∨ x = y,
    ⊢ ∀x y. FST (x,y) = x,
    ⊢ ∀x y. SND (x,y) = y,
    ⊢ (∀m. m ** 0 = 1) ∧ ∀m n. m ** SUC n = m * m ** n,
    ⊢ (polyp [] ⇔ T) ∧
      ∀r e c.
        polyp ((c,e)::r) ⇔
        polyp r ∧ c ≠ 0 ∧ 0 ≤ e ∧ (NULL r ∨ SND (HD r) < e),
    ⊢ (∀v. eval_poly [] v = 0) ∧
      ∀v r e c. eval_poly ((c,e)::r) v = c * v ** e + eval_poly r v,
    ⊢ sum_polys [] [] = [] ∧ (∀v7 v6. sum_polys [] (v6::v7) = v6::v7) ∧
      (∀v3 v2. sum_polys (v2::v3) [] = v2::v3) ∧
      ∀r2 r1 e2 e1 c2 c1.
        sum_polys ((c1,e1)::r1) ((c2,e2)::r2) =
        if e1 = e2 then (c1 + c2,e1)::sum_polys r1 r2
        else if e1 < e2 then (c2,e2)::sum_polys ((c1,e1)::r1) r2
        else (c1,e1)::sum_polys r1 ((c2,e2)::r2)]: thm list

val goals =
   [mk_named_goal "eval_sum_poly_distrib"
     ``∀x y v.
         polyp x ∧ polyp y ⇒
           eval_poly (sum_polys x y) v
           =
           eval_poly x v + eval_poly y v``];
|#

; ("COND",
(defhol
  :fns ((cond (:arrow* :bool a a a)))
  :defs ((:forall ((x a) (y a))
                  (equal (hap* (cond (typ (:arrow* :bool a a a))) (hp-true) x y) x))
         (:forall ((x a) (y a))
                  (equal (hap* (cond (typ (:arrow* :bool a a a))) (hp-false) x y) y))))
; ),
; ("COMMA",
(defhol
  :fns ((comma (:arrow* a b (:hash a b))))
  :defs ((:forall ((x a) (y b))
                  (equal (hap* (comma (typ (:arrow* a b (:hash a b)))) x y)
                         (hp-comma x y)))))
; ),
; ("HD",
(defhol
  :fns ((hd (:arrow* (:list a) a)))
  :defs ((:forall ((h a) (t (:list a)))
                  (equal (hap* (hd (typ (:arrow* (:list a) a))) (hp-cons h t)) h))))
; ),
; ("NULL",
(defhol
  :fns ((null (:arrow* (:list a) :bool)))
  :defs ((equal
          (hap* (null (typ (:arrow* (:list a) :bool))) (hp-nil (typ a)))
          (hp-true))
         (:forall ((h a) (t (:list a)))
                  (equal (hap* (null (typ (:arrow* (:list a) :bool))) (hp-cons h t))
                         (hp-false)))))
; ),
; ("SUC",
(defhol
  :fns ((suc (:arrow* :num :num)))
  :defs ((:forall ((m :num))
                  (equal (hap* (suc (typ (:arrow* :num :num))) m)
                         (hp+ (hp-num 1) m)))))
; ),
; ("<=",
(defhol
  :fns ((<= (:arrow* :num :num :bool)))
  :defs ((:forall ((x :num) (y :num))
                  (equal (hap* (<= (typ (:arrow* :num :num :bool))) x y)
                         (hp-or (hp< x y) (hp= x y))))))
; ),
; ("FST",
(defhol
  :fns ((fst (:arrow* (:hash a b) a)))
  :defs ((:forall ((x a) (y b))
                  (equal (hap* (fst (typ (:arrow* (:hash a b) a))) (hp-comma x y))
                         x))))
; ),
; ("SND",
(defhol
  :fns ((snd (:arrow* (:hash a b) b)))
  :defs ((:forall ((x a) (y b))
                  (equal (hap* (snd (typ (:arrow* (:hash a b) b))) (hp-comma x y))
                         y))))
; ),
; ("EXP",
(defhol
  :fns ((exp (:arrow* :num :num :num)))
  :defs ((:forall ((m :num))
                  (equal (hap* (exp (typ (:arrow* :num :num :num))) m (hp-num 0))
                         (hp-num 1)))
         (:forall ((m :num) (n :num))
                  (equal
                   (hap* (exp (typ (:arrow* :num :num :num))) m
                         (hap* (suc (typ (:arrow* :num :num))) n))
                   (hp* m (hap* (exp (typ (:arrow* :num :num :num))) m n))))))
; ),
; ("polyp",
(defhol
  :fns ((polyp (:arrow* (:list (:hash :num :num)) :bool)))
  :defs ((equal
          (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool)))
                (hp-nil (typ (:hash :num :num)))) (hp-true))
         (:forall ((r (:list (:hash :num :num))) (e :num) (c :num))
                  (equal
                   (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool)))
                         (hp-cons (hp-comma c e) r))
                   (hp-and
                    (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) r)
                    (hp-and (hp-not (hp= c (hp-num 0)))
                            (hp-and
                             (hap* (<= (typ (:arrow* :num :num :bool))) (hp-num 0) e)
                             (hp-or
                              (hap* (null (typ (:arrow* (:list (:hash :num :num)) :bool)))
                                    r)
                              (hp<
                               (hap* (snd (typ (:arrow* (:hash :num :num) :num)))
                                     (hap*
                                      (hd
                                       (typ
                                        (:arrow* (:list (:hash :num :num)) (:hash :num :num))))
                                      r)) e)))))))))
; ),
; ("eval_poly",
(defhol
  :fns ((eval_poly (:arrow* (:list (:hash :num :num)) :num :num)))
  :defs ((:forall ((v :num))
                  (equal
                   (hap*
                    (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
                    (hp-nil (typ (:hash :num :num))) v) (hp-num 0)))
         (:forall ((v :num) (r (:list (:hash :num :num))) (e :num) (c :num))
                  (equal
                   (hap*
                    (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
                    (hp-cons (hp-comma c e) r) v)
                   (hp+ (hp* c (hap* (exp (typ (:arrow* :num :num :num))) v e))
                        (hap*
                         (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
                         r v))))))
; ),
; ("sum_polys",
(defhol
  :fns ((sum_polys
         (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                  (:list (:hash :num :num)))))
  :defs ((equal
          (hap*
           (sum_polys
            (typ
             (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                      (:list (:hash :num :num))))) (hp-nil (typ (:hash :num :num)))
           (hp-nil (typ (:hash :num :num))))
          (hp-nil (typ (:hash :num :num))))
         (:forall ((v7 (:list (:hash :num :num))) (v6 (:hash :num :num)))
                  (equal
                   (hap*
                    (sum_polys
                     (typ
                      (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                               (:list (:hash :num :num))))) (hp-nil (typ (:hash :num :num)))
                    (hp-cons v6 v7)) (hp-cons v6 v7)))
         (:forall ((v3 (:list (:hash :num :num))) (v2 (:hash :num :num)))
                  (equal
                   (hap*
                    (sum_polys
                     (typ
                      (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                               (:list (:hash :num :num))))) (hp-cons v2 v3)
                    (hp-nil (typ (:hash :num :num)))) (hp-cons v2 v3)))
         (:forall
          ((r2 (:list (:hash :num :num))) (r1 (:list (:hash :num :num)))
           (e2 :num) (e1 :num) (c2 :num) (c1 :num))
          (equal
           (hap*
            (sum_polys
             (typ
              (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                       (:list (:hash :num :num))))) (hp-cons (hp-comma c1 e1) r1)
            (hp-cons (hp-comma c2 e2) r2))
           (hap*
            (cond
             (typ
              (:arrow* :bool (:list (:hash :num :num))
                       (:list (:hash :num :num)) (:list (:hash :num :num)))))
            (hp= e1 e2)
            (hp-cons (hp-comma (hp+ c1 c2) e1)
                     (hap*
                      (sum_polys
                       (typ
                        (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                                 (:list (:hash :num :num))))) r1 r2))
            (hap*
             (cond
              (typ
               (:arrow* :bool (:list (:hash :num :num))
                        (:list (:hash :num :num)) (:list (:hash :num :num)))))
             (hp< e1 e2)
             (hp-cons (hp-comma c2 e2)
                      (hap*
                       (sum_polys
                        (typ
                         (:arrow* (:list (:hash :num :num))
                                  (:list (:hash :num :num)) (:list (:hash :num :num)))))
                       (hp-cons (hp-comma c1 e1) r1) r2))
             (hp-cons (hp-comma c1 e1)
                      (hap*
                       (sum_polys
                        (typ
                         (:arrow* (:list (:hash :num :num))
                                  (:list (:hash :num :num)) (:list (:hash :num :num))))) r1
                       (hp-cons (hp-comma c2 e2) r2)))))))))
; ),
; ("eval_sum_poly_distrib",
(defhol
  :name eval_sum_poly_distrib
  :goal (:forall
         ((x (:list (:hash :num :num))) (y (:list (:hash :num :num)))
          (v :num))
         (hp-implies
          (hp-and
           (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) x)
           (hap* (polyp (typ (:arrow* (:list (:hash :num :num)) :bool))) y))
          (hp=
           (hap*
            (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
            (hap*
             (sum_polys
              (typ
               (:arrow* (:list (:hash :num :num)) (:list (:hash :num :num))
                        (:list (:hash :num :num))))) x y) v)
           (hp+
            (hap*
             (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
             x v)
            (hap*
             (eval_poly (typ (:arrow* (:list (:hash :num :num)) :num :num)))
             y v))))))
; )

(close-theory)

(set-enforce-redundancy acl2::t)

; Standing in "HOL" package we can evaluate
; (zf::hol-theory-print acl2::*standard-co* acl2::state)
; to get the following.

; Axioms:

(DEFTHM HOL{COND}0
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP A))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (COND (TYP (:ARROW* :BOOL A A A)))
                        (HP-TRUE)
                        X Y)
                  X)))

(DEFTHM HOL{COND}1
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP A))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (COND (TYP (:ARROW* :BOOL A A A)))
                        (HP-FALSE)
                        X Y)
                  Y)))

(DEFTHM HOL{COMMA}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (COMMA (TYP (:ARROW* A B (:HASH A B))))
                        X Y)
                  (HP-COMMA X Y))))

(DEFTHM HOL{HD}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP H HTA)
                (EQUAL (HP-TYPE H) (TYP A))
                (HPP T HTA)
                (EQUAL (HP-TYPE T) (TYP (:LIST A)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (HD (TYP (:ARROW* (:LIST A) A)))
                        (HP-CONS H T))
                  H)))

(DEFTHM HOL{NULL}0
  (IMPLIES (FORCE (EVAL-POLY$PROP))
           (EQUAL (HAP* (NULL (TYP (:ARROW* (:LIST A) :BOOL)))
                        (HP-NIL (TYP A)))
                  (HP-TRUE))))

(DEFTHM HOL{NULL}1
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP H HTA)
                (EQUAL (HP-TYPE H) (TYP A))
                (HPP T HTA)
                (EQUAL (HP-TYPE T) (TYP (:LIST A)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (NULL (TYP (:ARROW* (:LIST A) :BOOL)))
                        (HP-CONS H T))
                  (HP-FALSE))))

(DEFTHM HOL{SUC}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUC (TYP (:ARROW* :NUM :NUM))) M)
                  (HP+ (HP-NUM 1) M))))

(DEFTHM HOL{<=}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP :NUM))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (<= (TYP (:ARROW* :NUM :NUM :BOOL)))
                        X Y)
                  (HP-OR (HP< X Y) (HP= X Y)))))

(DEFTHM HOL{FST}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (FST (TYP (:ARROW* (:HASH A B) A)))
                        (HP-COMMA X Y))
                  X)))

(DEFTHM HOL{SND}
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SND (TYP (:ARROW* (:HASH A B) B)))
                        (HP-COMMA X Y))
                  Y)))

(DEFTHM HOL{EXP}0
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                        M (HP-NUM 0))
                  (HP-NUM 1))))

(DEFTHM HOL{EXP}1
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (HPP N HTA)
                (EQUAL (HP-TYPE N) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                        M
                        (HAP* (SUC (TYP (:ARROW* :NUM :NUM)))
                              N))
                  (HP* M
                       (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                             M N)))))

(DEFTHM HOL{POLYP}0
  (IMPLIES (FORCE (EVAL-POLY$PROP))
           (EQUAL (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             :BOOL)))
                        (HP-NIL (TYP (:HASH :NUM :NUM))))
                  (HP-TRUE))))

(DEFTHM HOL{POLYP}1
 (IMPLIES
  (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
       (HPP R HTA)
       (EQUAL (HP-TYPE R)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP E HTA)
       (EQUAL (HP-TYPE E) (TYP :NUM))
       (HPP C HTA)
       (EQUAL (HP-TYPE C) (TYP :NUM))
       (FORCE (EVAL-POLY$PROP)))
  (EQUAL
   (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                              :BOOL)))
         (HP-CONS (HP-COMMA C E) R))
   (HP-AND
    (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                               :BOOL)))
          R)
    (HP-AND
     (HP-NOT (HP= C (HP-NUM 0)))
     (HP-AND
          (HAP* (<= (TYP (:ARROW* :NUM :NUM :BOOL)))
                (HP-NUM 0)
                E)
          (HP-OR (HAP* (NULL (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                           :BOOL)))
                       R)
                 (HP< (HAP* (SND (TYP (:ARROW* (:HASH :NUM :NUM) :NUM)))
                            (HAP* (HD (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                    (:HASH :NUM :NUM))))
                                  R))
                      E))))))))

(DEFTHM HOL{EVAL_POLY}0
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP V HTA)
                (EQUAL (HP-TYPE V) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 :NUM :NUM)))
                        (HP-NIL (TYP (:HASH :NUM :NUM)))
                        V)
                  (HP-NUM 0))))

(DEFTHM HOL{EVAL_POLY}1
  (IMPLIES
       (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
            (HPP V HTA)
            (EQUAL (HP-TYPE V) (TYP :NUM))
            (HPP R HTA)
            (EQUAL (HP-TYPE R)
                   (TYP (:LIST (:HASH :NUM :NUM))))
            (HPP E HTA)
            (EQUAL (HP-TYPE E) (TYP :NUM))
            (HPP C HTA)
            (EQUAL (HP-TYPE C) (TYP :NUM))
            (FORCE (EVAL-POLY$PROP)))
       (EQUAL (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             :NUM :NUM)))
                    (HP-CONS (HP-COMMA C E) R)
                    V)
              (HP+ (HP* C
                        (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                              V E))
                   (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                  :NUM :NUM)))
                         R V)))))

(DEFTHM HOL{SUM_POLYS}0
  (IMPLIES (FORCE (EVAL-POLY$PROP))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        (HP-NIL (TYP (:HASH :NUM :NUM)))
                        (HP-NIL (TYP (:HASH :NUM :NUM))))
                  (HP-NIL (TYP (:HASH :NUM :NUM))))))

(DEFTHM HOL{SUM_POLYS}1
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP V7 HTA)
                (EQUAL (HP-TYPE V7)
                       (TYP (:LIST (:HASH :NUM :NUM))))
                (HPP V6 HTA)
                (EQUAL (HP-TYPE V6)
                       (TYP (:HASH :NUM :NUM)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        (HP-NIL (TYP (:HASH :NUM :NUM)))
                        (HP-CONS V6 V7))
                  (HP-CONS V6 V7))))

(DEFTHM HOL{SUM_POLYS}2
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP V3 HTA)
                (EQUAL (HP-TYPE V3)
                       (TYP (:LIST (:HASH :NUM :NUM))))
                (HPP V2 HTA)
                (EQUAL (HP-TYPE V2)
                       (TYP (:HASH :NUM :NUM)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        (HP-CONS V2 V3)
                        (HP-NIL (TYP (:HASH :NUM :NUM))))
                  (HP-CONS V2 V3))))

(DEFTHM HOL{SUM_POLYS}3
 (IMPLIES
  (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
       (HPP R2 HTA)
       (EQUAL (HP-TYPE R2)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP R1 HTA)
       (EQUAL (HP-TYPE R1)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP E2 HTA)
       (EQUAL (HP-TYPE E2) (TYP :NUM))
       (HPP E1 HTA)
       (EQUAL (HP-TYPE E1) (TYP :NUM))
       (HPP C2 HTA)
       (EQUAL (HP-TYPE C2) (TYP :NUM))
       (HPP C1 HTA)
       (EQUAL (HP-TYPE C1) (TYP :NUM))
       (FORCE (EVAL-POLY$PROP)))
  (EQUAL
   (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                  (:LIST (:HASH :NUM :NUM))
                                  (:LIST (:HASH :NUM :NUM)))))
         (HP-CONS (HP-COMMA C1 E1) R1)
         (HP-CONS (HP-COMMA C2 E2) R2))
   (HAP*
    (COND (TYP (:ARROW* :BOOL (:LIST (:HASH :NUM :NUM))
                        (:LIST (:HASH :NUM :NUM))
                        (:LIST (:HASH :NUM :NUM)))))
    (HP= E1 E2)
    (HP-CONS (HP-COMMA (HP+ C1 C2) E1)
             (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                            (:LIST (:HASH :NUM :NUM))
                                            (:LIST (:HASH :NUM :NUM)))))
                   R1 R2))
    (HAP*
         (COND (TYP (:ARROW* :BOOL (:LIST (:HASH :NUM :NUM))
                             (:LIST (:HASH :NUM :NUM))
                             (:LIST (:HASH :NUM :NUM)))))
         (HP< E1 E2)
         (HP-CONS (HP-COMMA C2 E2)
                  (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        (HP-CONS (HP-COMMA C1 E1) R1)
                        R2))
         (HP-CONS (HP-COMMA C1 E1)
                  (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        R1 (HP-CONS (HP-COMMA C2 E2) R2))))))))


; Theorems:  none.

; Goals:

#|
; Note that we can see a pretty version of the HP-IMPLIES call in the defthm
; below by evaluating (hol-pprint '(HP-IMPLIES ...)) after a suitable set-up,
; as follows.

; (include-book "eval-poly-thy")
; (include-book "../acl2/hol-pprint")
; (in-package "HOL")
; (hol-pprint '(HP-IMPLIES ...))

; Here is the result:

; (IMPLIES (AND (POLYP X) (POLYP Y))
;          (= (EVAL_POLY (SUM_POLYS X Y) V)
;             (+ (EVAL_POLY X V) (EVAL_POLY Y V))))

(DEFTHM HOL{EVAL_SUM_POLY_DISTRIB}
 (IMPLIES
  (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
       (HPP X HTA)
       (EQUAL (HP-TYPE X)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP Y HTA)
       (EQUAL (HP-TYPE Y)
              (TYP (:LIST (:HASH :NUM :NUM))))
       (HPP V HTA)
       (EQUAL (HP-TYPE V) (TYP :NUM))
       (FORCE (EVAL-POLY$PROP)))
  (EQUAL
   (HP-IMPLIES
       (HP-AND (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     X)
               (HAP* (POLYP (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                          :BOOL)))
                     Y))
       (HP= (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                           :NUM :NUM)))
                  (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        X Y)
                  V)
            (HP+ (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       X V)
                 (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       Y V))))
   (HP-TRUE))))
|#

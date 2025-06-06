; Copyright (C) 2025, Matt Kaufmann and Konrad Slind
; Written by Matt Kaufmann and Konrad Slind
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "HOL")

(include-book "../acl2/theories")

(open-theory ex1)

; Thanks to Konrad Slind for supplying the HOL4 examples in the comments below.

; See the forms after (set-enforce-redundancy t) below to see the main theorems
; generated.  But there are also "type theorems" generated; to see everything
; generated, include this book and issue the following command.

; :pe ex1$prop

; Here is the input to the translator.

#|
val thms =
   [⊢ ∀m. SUC m = 1 + m,
    ⊢ PRE 0 = 0 ∧ ∀m. PRE (SUC m) = m,
    ⊢ ∀x. I x = x,
    ⊢ ∀f x y. flip f x y = f y x,
    ⊢ ∀x y. K x y = x,
    ⊢ ∀f g x. (f ∘ g) x = f (g x),
    ⊢ ∀x y. COMMA x y = (x,y),
    ⊢ ∀x y. FST (x,y) = x,
    ⊢ ∀x y. SND (x,y) = y,
    ⊢ ∀f x y. UNCURRY f (x,y) = f x y,
    ⊢ (∀f. OPTION_BIND NONE f = NONE) ∧ ∀x f. OPTION_BIND (SOME x) f = f x,
    ⊢ (∀f x. OPTION_MAP f (SOME x) = SOME (f x)) ∧ ∀f. OPTION_MAP f NONE = NONE,
    ⊢ (∀v f. list_CASE [] v f = v) ∧
      ∀a0 a1 v f. list_CASE (a0::a1) v f = f a0 a1,
    ⊢ (∀f. list_size f [] = 0) ∧
      ∀f a0 a1. list_size f (a0::a1) = 1 + (f a0 + list_size f a1),
    ⊢ (∀f. MAP f [] = []) ∧ ∀f h t. MAP f (h::t) = f h::MAP f t,
    ⊢ (∀f e. FOLDR f e [] = e) ∧
      ∀f e x l. FOLDR f e (x::l) = f x (FOLDR f e l),
    ⊢ (∀f e. FOLDL f e [] = e) ∧
      ∀f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l,
    ⊢ SPEC (consts $DIV $MOD)
           (∀n k. 0 < n ⇒ k = k DIV n * n + k MOD n ∧ k MOD n < n ⇔ T)
    ⊢ (Even 0 ⇔ T) ∧
      (∀n. Even (SUC n) ⇔ Odd n) ∧
      (Odd 0 ⇔ F) ∧
      (∀n. Odd (SUC n) ⇔ Even n),
    ⊢ (∀m. m ** 0 = 1) ∧ ∀m n. m ** SUC n = m * m ** n,
    ⊢ THM MAP_ID_I (MAP I = I),
    ⊢ THM MAP_o (∀f g. MAP (f ∘ g) = MAP f ∘ MAP g)
    ]: thm list
|#

; And here is the corresponding output, with modifications made only to
; whitespace and by commenting out the parts we don't want.

; [("SUC",
(defhol
   :fns ((suc (:arrow* :num :num)))
   :defs ((:forall ((m :num))
      (equal (hap* (suc (typ (:arrow* :num :num))) m)
       (hp+ (hp-num 1) m)))))
;  ),
; ("PRE",
(defhol
   :fns ((pre (:arrow* :num :num)))
   :defs ((equal (hap* (pre (typ (:arrow* :num :num))) (hp-num 0))
      (hp-num 0))
     (:forall ((m :num))
      (equal
       (hap* (pre (typ (:arrow* :num :num)))
        (hap* (suc (typ (:arrow* :num :num))) m)) m))))
;  ),
; ("I",
(defhol
   :fns ((i (:arrow* a a)))
   :defs ((:forall ((x a)) (equal (hap* (i (typ (:arrow* a a))) x) x))))
;  ),
; ("C",
(defhol
   :fns ((c (:arrow* (:arrow* a b c) b a c)))
   :defs ((:forall ((f (:arrow* a b c)) (x b) (y a))
      (equal (hap* (c (typ (:arrow* (:arrow* a b c) b a c))) f x y)
       (hap* f y x)))))
;  ),
; ("K",
(defhol
   :fns ((k (:arrow* a b a)))
   :defs ((:forall ((x a) (y b))
      (equal (hap* (k (typ (:arrow* a b a))) x y) x))))
;  ),
; ("o",
(defhol
   :fns ((o (:arrow* (:arrow* a b) (:arrow* c a) c b)))
   :defs ((:forall ((f (:arrow* a b)) (g (:arrow* c a)) (x c))
      (equal
       (hap* (o (typ (:arrow* (:arrow* a b) (:arrow* c a) c b))) f g x)
       (hap* f (hap* g x))))))
;  ),
; ("COMMA",
(defhol
   :fns ((comma (:arrow* a b (:hash a b))))
   :defs ((:forall ((x a) (y b))
      (equal (hap* (comma (typ (:arrow* a b (:hash a b)))) x y)
       (hp-comma x y)))))
;  ),
; ("FST",
(defhol
   :fns ((fst (:arrow* (:hash a b) a)))
   :defs ((:forall ((x a) (y b))
      (equal (hap* (fst (typ (:arrow* (:hash a b) a))) (hp-comma x y))
       x))))
;  ),
; ("SND",
(defhol
   :fns ((snd (:arrow* (:hash a b) b)))
   :defs ((:forall ((x a) (y b))
      (equal (hap* (snd (typ (:arrow* (:hash a b) b))) (hp-comma x y))
       y))))
;  ),
; ("UNCURRY",
(defhol
   :fns ((uncurry (:arrow* (:arrow* a b c) (:hash a b) c)))
   :defs ((:forall ((f (:arrow* a b c)) (x a) (y b))
      (equal
       (hap* (uncurry (typ (:arrow* (:arrow* a b c) (:hash a b) c))) f
        (hp-comma x y)) (hap* f x y)))))
;  ),
; ("OPTION_BIND",
(defhol
   :fns ((option_bind
         (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
   :defs ((:forall ((f (:arrow* b (:option a))))
      (equal
       (hap*
        (option_bind
         (typ (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
        (hp-none (typ b))
        f)
       (hp-none (typ a))))
     (:forall ((x b) (f (:arrow* b (:option a))))
      (equal
       (hap*
        (option_bind
         (typ (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
        (hp-some x)
        f)
       (hap* f x)))))
;  ),
; ("OPTION_MAP",
(defhol
   :fns ((option_map (:arrow* (:arrow* a b) (:option a) (:option b))))
   :defs ((:forall ((f (:arrow* a b)) (x a))
      (equal
       (hap*
        (option_map
         (typ (:arrow* (:arrow* a b) (:option a) (:option b))))
        f
        (hp-some x))
       (hp-some (hap* f x))))
     (:forall ((f (:arrow* a b)))
      (equal
       (hap*
        (option_map
         (typ (:arrow* (:arrow* a b) (:option a) (:option b))))
        f
        (hp-none (typ a)))
       (hp-none (typ b))))))
;  ),
; ("list_CASE",
(defhol
   :fns ((list_case (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
   :defs ((:forall ((v b) (f (:arrow* a (:list a) b)))
      (equal
       (hap*
        (list_case
         (typ (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
        (hp-nil (typ a))
        v f) v))
     (:forall ((a0 a) (a1 (:list a)) (v b) (f (:arrow* a (:list a) b)))
      (equal
       (hap*
        (list_case
         (typ (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
        (hp-cons a0 a1)
        v
        f)
       (hap* f a0 a1)))))
;  ),
; ("list_size",
(defhol
   :fns ((list_size (:arrow* (:arrow* a :num) (:list a) :num)))
   :defs ((:forall ((f (:arrow* a :num)))
      (equal
       (hap* (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num)))
             f
             (hp-nil (typ a)))
       (hp-num 0)))
     (:forall ((f (:arrow* a :num)) (a0 a) (a1 (:list a)))
      (equal
       (hap* (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num)))
        f
        (hp-cons a0 a1))
       (hp+ (hp-num 1)
        (hp+ (hap* f a0)
         (hap*
          (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num))) f
          a1)))))))
;  ),
; ("MAP",
(defhol
   :fns ((map (:arrow* (:arrow* a b) (:list a) (:list b))))
   :defs ((:forall ((f (:arrow* a b)))
      (equal
       (hap* (map (typ (:arrow* (:arrow* a b) (:list a) (:list b)))) f
        (hp-nil (typ a))) (hp-nil (typ b))))
     (:forall ((f (:arrow* a b)) (h a) (t (:list a)))
      (equal
       (hap* (map (typ (:arrow* (:arrow* a b) (:list a) (:list b)))) f
        (hp-cons h t))
       (hp-cons (hap* f h)
        (hap* (map (typ (:arrow* (:arrow* a b) (:list a) (:list b)))) f
         t))))))
;  ),
; ("FOLDR",
(defhol
   :fns ((foldr (:arrow* (:arrow* a b b) b (:list a) b)))
   :defs ((:forall ((f (:arrow* a b b)) (e b))
      (equal
       (hap* (foldr (typ (:arrow* (:arrow* a b b) b (:list a) b))) f e
        (hp-nil (typ a))) e))
     (:forall ((f (:arrow* a b b)) (e b) (x a) (l (:list a)))
      (equal
       (hap* (foldr (typ (:arrow* (:arrow* a b b) b (:list a) b))) f e
        (hp-cons x l))
       (hap* f x
        (hap* (foldr (typ (:arrow* (:arrow* a b b) b (:list a) b))) f e
         l))))))
;  ),
; ("FOLDL",
(defhol
   :fns ((foldl (:arrow* (:arrow* b a b) b (:list a) b)))
   :defs ((:forall ((f (:arrow* b a b)) (e b))
      (equal
       (hap* (foldl (typ (:arrow* (:arrow* b a b) b (:list a) b))) f e
        (hp-nil (typ a))) e))
     (:forall ((f (:arrow* b a b)) (e b) (x a) (l (:list a)))
      (equal
       (hap* (foldl (typ (:arrow* (:arrow* b a b) b (:list a) b))) f e
        (hp-cons x l))
       (hap* (foldl (typ (:arrow* (:arrow* b a b) b (:list a) b))) f
        (hap* f e x) l)))))
;  ),
; ("DIV",
(defhol
   :fns ((div (:arrow* :num :num :num)) (mod (:arrow* :num :num :num)))
   :defs ((:forall ((n :num) (k :num))
      (equal
       (hp-implies (hp< (hp-num 0) n)
        (hp-and
         (hp= k
          (hp+ (hp* (hap* (div (typ (:arrow* :num :num :num))) k n) n)
           (hap* (mod (typ (:arrow* :num :num :num))) k n)))
         (hp< (hap* (mod (typ (:arrow* :num :num :num))) k n) n)))
       (hp-true)))))
;  ),
; ("Even",
(defhol
   :fns ((even (:arrow* :num :bool)) (odd (:arrow* :num :bool)))
   :defs ((equal (hap* (even (typ (:arrow* :num :bool))) (hp-num 0))
      (hp-true))
     (:forall ((n :num))
      (equal
       (hap* (even (typ (:arrow* :num :bool)))
        (hap* (suc (typ (:arrow* :num :num))) n))
       (hap* (odd (typ (:arrow* :num :bool))) n)))
     (equal (hap* (odd (typ (:arrow* :num :bool))) (hp-num 0))
      (hp-false))
     (:forall ((n :num))
      (equal
       (hap* (odd (typ (:arrow* :num :bool)))
        (hap* (suc (typ (:arrow* :num :num))) n))
       (hap* (even (typ (:arrow* :num :bool))) n)))))
;  )
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
;  ),
; ("MAP_ID_I",
(defhol
   :name map_id_i
   :thm (hp=
     (hap* (map (typ (:arrow* (:arrow* a a) (:list a) (:list a))))
      (i (typ (:arrow* a a)))) (i (typ (:arrow* (:list a) (:list a))))))
;  ),
; ("MAP_o",
(defhol
   :name map_o
   :thm (:forall ((f (:arrow* b c)) (g (:arrow* a b)))
     (hp=
      (hap* (map (typ (:arrow* (:arrow* a c) (:list a) (:list c))))
       (hap* (o (typ (:arrow* (:arrow* b c) (:arrow* a b) a c))) f g))
      (hap*
       (o
        (typ
         (:arrow* (:arrow* (:list b) (:list c))
          (:arrow* (:list a) (:list b)) (:list a) (:list c))))
       (hap* (map (typ (:arrow* (:arrow* b c) (:list b) (:list c)))) f)
       (hap* (map (typ (:arrow* (:arrow* a b) (:list a) (:list b)))) g)))))
;  )]

;;; Added manually; see defgoal form for fst-comma at the end, which
;;; corresponds to the defhol form just below.

; FST (x,y) = x

(defhol
   :name fst-comma
   :goal (:forall
          ((x a) (y b))
          (hp= (hap*
                (fst (typ (:arrow* (:hash a b) a)))
                (hap* (comma (typ (:arrow* a b (:hash a b)))) x y))
               x)))

(close-theory)

(set-enforce-redundancy acl2::t)

; From (table :hol-theory 'ex1):

(DEFTHM HOL{SUC}
  (IMPLIES (AND (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (SUC (TYP (:ARROW* :NUM :NUM))) M)
                  (HP+ (HP-NUM 1) M))))
(DEFTHM HOL{PRE}0
  (IMPLIES (FORCE (EX1$PROP))
           (EQUAL (HAP* (PRE (TYP (:ARROW* :NUM :NUM))) (HP-NUM 0))
                  (HP-NUM 0))))
(DEFTHM HOL{PRE}1
  (IMPLIES (AND (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (PRE (TYP (:ARROW* :NUM :NUM)))
                        (HAP* (SUC (TYP (:ARROW* :NUM :NUM))) M))
                  M)))
(DEFTHM HOL{I}
  (IMPLIES (AND (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (I (TYP (:ARROW* A A))) X) X)))
(DEFTHM HOL{C}
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B C)))
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP B))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP A))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (C (TYP (:ARROW* (:ARROW* A B C) B A C))) F X Y)
                  (HAP* F Y X))))
(DEFTHM HOL{K}
  (IMPLIES (AND (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (K (TYP (:ARROW* A B A))) X Y) X)))
(DEFTHM HOL{O}
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B)))
                (HPP G HTA)
                (EQUAL (HP-TYPE G) (TYP (:ARROW* C A)))
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP C))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (O (TYP (:ARROW* (:ARROW* A B) (:ARROW* C A) C B)))
                        F G X)
                  (HAP* F (HAP* G X)))))
(DEFTHM HOL{COMMA}
  (IMPLIES
   (AND (HPP X HTA)
        (EQUAL (HP-TYPE X) (TYP A))
        (HPP Y HTA)
        (EQUAL (HP-TYPE Y) (TYP B))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HAP* (COMMA (TYP (:ARROW* A B (:HASH A B)))) X Y)
          (HP-COMMA X Y))))
(DEFTHM HOL{FST}
  (IMPLIES (AND (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (FST (TYP (:ARROW* (:HASH A B) A)))
                        (HP-COMMA X Y))
                  X)))

(DEFTHM HOL{SND}
  (IMPLIES (AND (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (SND (TYP (:ARROW* (:HASH A B) B)))
                        (HP-COMMA X Y))
                  Y)))
(DEFTHM HOL{UNCURRY}
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B C)))
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (HPP Y HTA)
                (EQUAL (HP-TYPE Y) (TYP B))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (UNCURRY (TYP (:ARROW* (:ARROW* A B C) (:HASH A B) C)))
                        F
                        (HP-COMMA X Y))
                  (HAP* F X Y))))
(DEFTHM HOL{OPTION_BIND}0
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* B (:OPTION A))))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (OPTION_BIND
                         (TYP (:ARROW* (:OPTION B)
                                       (:ARROW* B (:OPTION A))
                                       (:OPTION A))))
                        (HP-NONE (TYP B))
                        F)
                  (HP-NONE (TYP A)))))
(DEFTHM HOL{OPTION_BIND}1
  (IMPLIES (AND (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP B))
                (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* B (:OPTION A))))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (OPTION_BIND
                         (TYP (:ARROW* (:OPTION B)
                                       (:ARROW* B (:OPTION A))
                                       (:OPTION A))))
                        (HP-SOME X)
                        F)
                  (HAP* F X))))
(DEFTHM HOL{OPTION_MAP}0
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B)))
                (HPP X HTA)
                (EQUAL (HP-TYPE X) (TYP A))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (OPTION_MAP
                         (TYP (:ARROW* (:ARROW* A B) (:OPTION A) (:OPTION B))))
                        F
                        (HP-SOME X))
                  (HP-SOME (HAP* F X)))))
(DEFTHM HOL{OPTION_MAP}1
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (OPTION_MAP
                         (TYP (:ARROW* (:ARROW* A B) (:OPTION A) (:OPTION B))))
                        F
                        (HP-NONE (TYP A)))
                  (HP-NONE (TYP B)))))
(DEFTHM HOL{LIST_CASE}0
  (IMPLIES (AND (HPP V HTA)
                (EQUAL (HP-TYPE V) (TYP B))
                (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A (:LIST A) B)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (LIST_CASE
                         (TYP (:ARROW* (:LIST A) B (:ARROW* A (:LIST A) B) B)))
                        (HP-NIL (TYP A))
                        V F)
                  V)))
(DEFTHM HOL{LIST_CASE}1
  (IMPLIES (AND (HPP A0 HTA)
                (EQUAL (HP-TYPE A0) (TYP A))
                (HPP A1 HTA)
                (EQUAL (HP-TYPE A1) (TYP (:LIST A)))
                (HPP V HTA)
                (EQUAL (HP-TYPE V) (TYP B))
                (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A (:LIST A) B)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (LIST_CASE
                         (TYP (:ARROW* (:LIST A) B (:ARROW* A (:LIST A) B) B)))
                        (HP-CONS A0 A1)
                        V F)
                  (HAP* F A0 A1))))
(DEFTHM HOL{LIST_SIZE}0
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A :NUM)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (LIST_SIZE (TYP (:ARROW* (:ARROW* A :NUM)
                                                 (:LIST A)
                                                 :NUM)))
                        F
                        (HP-NIL (TYP A)))
                  (HP-NUM 0))))
(DEFTHM HOL{LIST_SIZE}1
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A :NUM)))
                (HPP A0 HTA)
                (EQUAL (HP-TYPE A0) (TYP A))
                (HPP A1 HTA)
                (EQUAL (HP-TYPE A1) (TYP (:LIST A)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (LIST_SIZE (TYP (:ARROW* (:ARROW* A :NUM)
                                                 (:LIST A)
                                                 :NUM)))
                        F (HP-CONS A0 A1))
                  (HP+ (HP-NUM 1)
                       (HP+ (HAP* F A0)
                            (HAP* (LIST_SIZE (TYP (:ARROW* (:ARROW* A :NUM)
                                                           (:LIST A)
                                                           :NUM)))
                                  F A1))))))
(DEFTHM HOL{FOLDR}0
  (IMPLIES
   (AND (HPP F HTA)
        (EQUAL (HP-TYPE F) (TYP (:ARROW* A B B)))
        (HPP E HTA)
        (EQUAL (HP-TYPE E) (TYP B))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HAP* (FOLDR (TYP (:ARROW* (:ARROW* A B B) B (:LIST A) B)))
                F E
                (HP-NIL (TYP A)))
          E)))
(DEFTHM HOL{FOLDR}1
  (IMPLIES
   (AND (HPP F HTA)
        (EQUAL (HP-TYPE F) (TYP (:ARROW* A B B)))
        (HPP E HTA)
        (EQUAL (HP-TYPE E) (TYP B))
        (HPP X HTA)
        (EQUAL (HP-TYPE X) (TYP A))
        (HPP L HTA)
        (EQUAL (HP-TYPE L) (TYP (:LIST A)))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HAP* (FOLDR (TYP (:ARROW* (:ARROW* A B B) B (:LIST A) B)))
                F E (HP-CONS X L))
          (HAP* F X (HAP* (FOLDR (TYP (:ARROW* (:ARROW* A B B) B (:LIST A) B)))
                          F E L)))))
(DEFTHM HOL{FOLDL}0
  (IMPLIES
   (AND (HPP F HTA)
        (EQUAL (HP-TYPE F) (TYP (:ARROW* B A B)))
        (HPP E HTA)
        (EQUAL (HP-TYPE E) (TYP B))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HAP* (FOLDL (TYP (:ARROW* (:ARROW* B A B) B (:LIST A) B)))
                F E
                (HP-NIL (TYP A)))
          E)))
(DEFTHM HOL{FOLDL}1
  (IMPLIES
   (AND (HPP F HTA)
        (EQUAL (HP-TYPE F) (TYP (:ARROW* B A B)))
        (HPP E HTA)
        (EQUAL (HP-TYPE E) (TYP B))
        (HPP X HTA)
        (EQUAL (HP-TYPE X) (TYP A))
        (HPP L HTA)
        (EQUAL (HP-TYPE L) (TYP (:LIST A)))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HAP* (FOLDL (TYP (:ARROW* (:ARROW* B A B) B (:LIST A) B)))
                F E (HP-CONS X L))
          (HAP* (FOLDL (TYP (:ARROW* (:ARROW* B A B) B (:LIST A) B)))
                F (HAP* F E X) L))))
(DEFTHM HOL{EVEN}0
  (IMPLIES (FORCE (EX1$PROP))
           (EQUAL (HAP* (EVEN (TYP (:ARROW* :NUM :BOOL))) (HP-NUM 0))
                  (HP-TRUE))))
(DEFTHM HOL{EVEN}1
  (IMPLIES (AND (HPP N HTA)
                (EQUAL (HP-TYPE N) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (EVEN (TYP (:ARROW* :NUM :BOOL)))
                        (HAP* (SUC (TYP (:ARROW* :NUM :NUM))) N))
                  (HAP* (ODD (TYP (:ARROW* :NUM :BOOL))) N))))
(DEFTHM HOL{EVEN}2
  (IMPLIES (FORCE (EX1$PROP))
           (EQUAL (HAP* (ODD (TYP (:ARROW* :NUM :BOOL))) (HP-NUM 0))
                  (HP-FALSE))))
(DEFTHM HOL{EVEN}3
  (IMPLIES (AND (HPP N HTA)
                (EQUAL (HP-TYPE N) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (ODD (TYP (:ARROW* :NUM :BOOL)))
                        (HAP* (SUC (TYP (:ARROW* :NUM :NUM))) N))
                  (HAP* (EVEN (TYP (:ARROW* :NUM :BOOL))) N))))
(DEFTHM HOL{DIV}
  (IMPLIES
   (AND (HPP N HTA)
        (EQUAL (HP-TYPE N) (TYP :NUM))
        (HPP K HTA)
        (EQUAL (HP-TYPE K) (TYP :NUM))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL
    (HP-IMPLIES
     (HP< (HP-NUM 0) N)
     (HP-AND (HP= K
                  (HP+ (HP* (HAP* (DIV (TYP (:ARROW* :NUM :NUM :NUM))) K N) N)
                       (HAP* (MOD (TYP (:ARROW* :NUM :NUM :NUM))) K N)))
             (HP< (HAP* (MOD (TYP (:ARROW* :NUM :NUM :NUM))) K N) N)))
    (HP-TRUE))))
(DEFTHM HOL{MAP}0
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (MAP (TYP (:ARROW* (:ARROW* A B)
                                           (:LIST A)
                                           (:LIST B))))
                        F
                        (HP-NIL (TYP A)))
                  (HP-NIL (TYP B)))))
(DEFTHM HOL{MAP}1
  (IMPLIES (AND (HPP F HTA)
                (EQUAL (HP-TYPE F) (TYP (:ARROW* A B)))
                (HPP H HTA)
                (EQUAL (HP-TYPE H) (TYP A))
                (HPP T HTA)
                (EQUAL (HP-TYPE T) (TYP (:LIST A)))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (MAP (TYP (:ARROW* (:ARROW* A B)
                                           (:LIST A)
                                           (:LIST B))))
                        F
                        (HP-CONS H T))
                  (HP-CONS (HAP* F H)
                           (HAP* (MAP (TYP (:ARROW* (:ARROW* A B)
                                                    (:LIST A)
                                                    (:LIST B))))
                                 F
                                 T)))))
(DEFTHM HOL{EXP}0
  (IMPLIES (AND (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                        M (HP-NUM 0))
                  (HP-NUM 1))))
(DEFTHM HOL{EXP}1
  (IMPLIES (AND (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (HPP N HTA)
                (EQUAL (HP-TYPE N) (TYP :NUM))
                (ALIST-SUBSETP (EX1$HTA) HTA)
                (FORCE (EX1$PROP)))
           (EQUAL (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                        M
                        (HAP* (SUC (TYP (:ARROW* :NUM :NUM)))
                              N))
                  (HP* M
                       (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                             M N)))))
(DEFTHM HOL{MAP_ID_I}
  (IMPLIES (FORCE (EX1$PROP))
           (EQUAL (HP= (HAP* (MAP (TYP (:ARROW* (:ARROW* A A)
                                                (:LIST A)
                                                (:LIST A))))
                             (I (TYP (:ARROW* A A))))
                       (I (TYP (:ARROW* (:LIST A) (:LIST A)))))
                  (HP-TRUE))))
(DEFTHM HOL{MAP_O}
  (IMPLIES
   (AND (HPP F HTA)
        (EQUAL (HP-TYPE F) (TYP (:ARROW* B C)))
        (HPP G HTA)
        (EQUAL (HP-TYPE G) (TYP (:ARROW* A B)))
        (ALIST-SUBSETP (EX1$HTA) HTA)
        (FORCE (EX1$PROP)))
   (EQUAL (HP= (HAP* (MAP (TYP (:ARROW* (:ARROW* A C)
                                        (:LIST A)
                                        (:LIST C))))
                     (HAP* (O (TYP (:ARROW* (:ARROW* B C)
                                            (:ARROW* A B)
                                            A
                                            C)))
                           F
                           G))
               (HAP* (O (TYP (:ARROW* (:ARROW* (:LIST B) (:LIST C))
                                      (:ARROW* (:LIST A) (:LIST B))
                                      (:LIST A)
                                      (:LIST C))))
                     (HAP* (MAP (TYP (:ARROW* (:ARROW* B C)
                                              (:LIST B)
                                              (:LIST C))))
                           F)
                     (HAP* (MAP (TYP (:ARROW* (:ARROW* A B)
                                              (:LIST A)
                                              (:LIST B))))
                           G)))
          (HP-TRUE))))

(set-enforce-redundancy acl2::nil)

(defgoal fst-comma ; generates (DEFTHM HOL{FST-COMMA} ...):
  (implies
   (and (hpp x hta)
        (equal (hp-type x) (typ a))
        (hpp y hta)
        (equal (hp-type y) (typ b))
        (alist-subsetp (hol::ex1$hta) hta)
        (force (hol::ex1$prop)))
   (equal (hp= (hap*
                (hol::fst (typ (:arrow* (:hash a b) a)))
                (hap* (hol::comma (typ (:arrow* a b (:hash a b)))) x y))
               x)
          (hp-true)))
  :hints (("Goal" :in-theory (disable hp-comma))))

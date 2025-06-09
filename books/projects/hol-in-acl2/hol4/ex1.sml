(*---------------------------------------------------------------------------*)
(* Example                                                                  *)
(*---------------------------------------------------------------------------*)

use "translator.sml";

open prim_recTheory arithmeticTheory
     pairTheory combinTheory optionTheory listTheory;

Theorem suc_thm:
  ∀m. SUC m = 1 + m
Proof
  decide_tac
QED

Definition COMMA_def:
  COMMA x y = (x,y)
End

Definition Even_Odd_def:
  Even 0 = T ∧
  Even (SUC n) = Odd n ∧
  Odd 0 = F ∧
  Odd (SUC n) = Even n
End

val DIVISION_FOR_ACL2 =
    DIVISION
     |> SIMP_RULE bool_ss [PULL_FORALL]
     |> SPEC_ALL
     |> EQT_INTRO
     |> GEN_ALL;

val thms =  (* following ex1.lisp plus a few others *)
  [suc_thm,
   PRE,
   I_THM,
   C_THM,
   K_THM,
   o_THM,
   COMMA_def,
   FST,
   SND,
   UNCURRY_DEF,
   OPTION_BIND_def,
   OPTION_MAP_DEF,
   list_case_def,
   list_size_def,
   MAP,
   FOLDR,
   FOLDL,
   mk_spec [``(DIV)``, ``(MOD)``] DIVISION_FOR_ACL2,
   Even_Odd_def,
   EXP,
   mk_named_thm "MAP_ID_I" MAP_ID_I,
   mk_named_thm "MAP_o" MAP_o
  ];

val goals =
  [mk_named_goal "BOOL_CASES_AX" (concl BOOL_CASES_AX)];

val acl2_defs = map hol_sexp (thms @ goals)

(*---------------------------------------------------------------------------

Output:

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


val goals =
   [⊢ GOAL BOOL_CASES_AX (∀t. (t ⇔ T) ∨ (t ⇔ F))
   ]: thm list

val acl2_defs =
   [("SUC",
     (defhol
        :fns ((suc (:arrow* :num :num)))
        :defs ((:forall ((m :num))
           (equal (hap* (suc (typ (:arrow* :num :num))) m)
            (hp+ (hp-num 1) m)))))),
    ("PRE",
     (defhol
        :fns ((pre (:arrow* :num :num)))
        :defs ((equal (hap* (pre (typ (:arrow* :num :num))) (hp-num 0))
           (hp-num 0))
          (:forall ((m :num))
           (equal
            (hap* (pre (typ (:arrow* :num :num)))
             (hap* (suc (typ (:arrow* :num :num))) m)) m))))),
    ("I",
     (defhol
        :fns ((i (:arrow* a a)))
        :defs ((:forall ((x a)) (equal (hap* (i (typ (:arrow* a a))) x) x))))),
    ("C",
     (defhol
        :fns ((c (:arrow* (:arrow* a b c) b a c)))
        :defs ((:forall ((f (:arrow* a b c)) (x b) (y a))
           (equal (hap* (c (typ (:arrow* (:arrow* a b c) b a c))) f x y)
            (hap* f y x)))))),
    ("K",
     (defhol
        :fns ((k (:arrow* a b a)))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (k (typ (:arrow* a b a))) x y) x))))),
    ("o",
     (defhol
        :fns ((o (:arrow* (:arrow* a b) (:arrow* c a) c b)))
        :defs ((:forall ((f (:arrow* a b)) (g (:arrow* c a)) (x c))
           (equal
            (hap* (o (typ (:arrow* (:arrow* a b) (:arrow* c a) c b))) f g x)
            (hap* f (hap* g x))))))),
    ("COMMA",
     (defhol
        :fns ((comma (:arrow* a b (:hash a b))))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (comma (typ (:arrow* a b (:hash a b)))) x y)
            (hp-comma x y)))))),
    ("FST",
     (defhol
        :fns ((fst (:arrow* (:hash a b) a)))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (fst (typ (:arrow* (:hash a b) a))) (hp-comma x y))
            x))))),
    ("SND",
     (defhol
        :fns ((snd (:arrow* (:hash a b) b)))
        :defs ((:forall ((x a) (y b))
           (equal (hap* (snd (typ (:arrow* (:hash a b) b))) (hp-comma x y))
            y))))),
    ("UNCURRY",
     (defhol
        :fns ((uncurry (:arrow* (:arrow* a b c) (:hash a b) c)))
        :defs ((:forall ((f (:arrow* a b c)) (x a) (y b))
           (equal
            (hap* (uncurry (typ (:arrow* (:arrow* a b c) (:hash a b) c))) f
             (hp-comma x y)) (hap* f x y)))))),
    ("OPTION_BIND",
     (defhol
        :fns ((option_bind
           (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
        :defs ((:forall ((f (:arrow* b (:option a))))
           (equal
            (hap*
             (option_bind
              (typ (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
             (hp-none (typ b)) f) (hp-none (typ a))))
          (:forall ((x b) (f (:arrow* b (:option a))))
           (equal
            (hap*
             (option_bind
              (typ (:arrow* (:option b) (:arrow* b (:option a)) (:option a))))
             (hp-some x) f) (hap* f x)))))),
    ("OPTION_MAP",
     (defhol
        :fns ((option_map (:arrow* (:arrow* a b) (:option a) (:option b))))
        :defs ((:forall ((f (:arrow* a b)) (x a))
           (equal
            (hap*
             (option_map
              (typ (:arrow* (:arrow* a b) (:option a) (:option b)))) f
             (hp-some x)) (hp-some (hap* f x))))
          (:forall ((f (:arrow* a b)))
           (equal
            (hap*
             (option_map
              (typ (:arrow* (:arrow* a b) (:option a) (:option b)))) f
             (hp-none (typ a))) (hp-none (typ b))))))),
    ("list_CASE",
     (defhol
        :fns ((list_case (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
        :defs ((:forall ((v b) (f (:arrow* a (:list a) b)))
           (equal
            (hap*
             (list_case
              (typ (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
             (hp-nil (typ a)) v f) v))
          (:forall ((a0 a) (a1 (:list a)) (v b) (f (:arrow* a (:list a) b)))
           (equal
            (hap*
             (list_case
              (typ (:arrow* (:list a) b (:arrow* a (:list a) b) b)))
             (hp-cons a0 a1) v f) (hap* f a0 a1)))))),
    ("list_size",
     (defhol
        :fns ((list_size (:arrow* (:arrow* a :num) (:list a) :num)))
        :defs ((:forall ((f (:arrow* a :num)))
           (equal
            (hap* (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num)))
             f (hp-nil (typ a))) (hp-num 0)))
          (:forall ((f (:arrow* a :num)) (a0 a) (a1 (:list a)))
           (equal
            (hap* (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num)))
             f (hp-cons a0 a1))
            (hp+ (hp-num 1)
             (hp+ (hap* f a0)
              (hap*
               (list_size (typ (:arrow* (:arrow* a :num) (:list a) :num))) f
               a1)))))))),
    ("MAP",
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
              t))))))),
    ("FOLDR",
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
              l))))))),
    ("FOLDL",
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
             (hap* f e x) l)))))),
    ("DIV",
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
            (hp-true)))))),
    ("Even",
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
            (hap* (even (typ (:arrow* :num :bool))) n)))))),
    ("EXP",
     (defhol
        :fns ((exp (:arrow* :num :num :num)))
        :defs ((:forall ((m :num))
           (equal (hap* (exp (typ (:arrow* :num :num :num))) m (hp-num 0))
            (hp-num 1)))
          (:forall ((m :num) (n :num))
           (equal
            (hap* (exp (typ (:arrow* :num :num :num))) m
             (hap* (suc (typ (:arrow* :num :num))) n))
            (hp* m (hap* (exp (typ (:arrow* :num :num :num))) m n))))))),
    ("MAP_ID_I",
     (defhol
        :name map_id_i
        :thm (hp=
          (hap* (map (typ (:arrow* (:arrow* a a) (:list a) (:list a))))
           (i (typ (:arrow* a a)))) (i (typ (:arrow* (:list a) (:list a))))))),
    ("MAP_o",
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
            (hap* (map (typ (:arrow* (:arrow* a b) (:list a) (:list b)))) g))))))]:
   (string * t) list
*)

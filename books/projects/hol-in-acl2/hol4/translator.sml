(*---------------------------------------------------------------------------*)
(* Copyright (C) 2025, Konrad Slind                                          *)
(* Written by Konrad Slind                                                   *)
(* License: A 3-clause BSD license;                                          *)
(*          See the LICENSE file distributed with ACL2.                      *)
(*---------------------------------------------------------------------------*)

open HOLsexp List;

val ERR = Feedback.mk_HOL_ERR "HOL-->ACL2";

(*---------------------------------------------------------------------------*)
(* Types                                                                     *)
(*---------------------------------------------------------------------------*)

fun tyvar_name tyv =
 let val s = dest_vartype tyv
 in String.substring(s,1,String.size s - 1)
 end

fun tyop_dict s =
  case s
   of "fun" => ":arrow*"
    | "prod" => ":hash"
    | otherwise => ":"^s

(*---------------------------------------------------------------------------*)
(* A HOL type is essentially a first order term: either a variable or a      *)
(* type operator applied to a list of types.                                 *)
(*---------------------------------------------------------------------------*)

fun ty_sexp ty =
 if is_vartype ty then
   Symbol (tyvar_name ty)
 else
  case dest_type ty
   of (s,[]) => Symbol (tyop_dict s)
    | ("fun",_) =>
        let val tylist = (op@ o (I ## single) o strip_fun) ty
	in Cons(Symbol(tyop_dict "fun"),List (map ty_sexp tylist))
        end
    | (s,args) => Cons(Symbol(tyop_dict s),List (map ty_sexp args))
;

(*---------------------------------------------------------------------------*)
(* example type s-expressions                                                *)
(*---------------------------------------------------------------------------*)

map ty_sexp [bool, alpha --> beta, bool --> alpha --> beta, ``:num list``];

(*---------------------------------------------------------------------------*)
(* Terms                                                                     *)
(*---------------------------------------------------------------------------*)

fun bvar_sexp v =
 let val (s,ty) = dest_var v
 in List[Symbol s,ty_sexp ty]
 end

fun strip_cond tm =
  if not (is_cond tm) then
    ([],tm)
  else
    let val (t1,t2,t3) = dest_cond tm
        val (pairs,tn) = strip_cond t3
    in ((t1,t2)::pairs,tn)
    end

(*---------------------------------------------------------------------------*)
(* Current rule: look to see if the constant is a built-in. If it is then no *)
(* need to do a hap*. If it isn't then do a (hap* (name (ty <ty>)) a1 ... an)*)
(*---------------------------------------------------------------------------*)

val builtin_const_map =
  [(“(=)”, "hp="),
   (“(,)”, "hp-comma"),
   (“NIL”, "hp-nil"),
   (“CONS”, "hp-cons"),
   (“NONE”, "hp-none"),
   (“SOME”, "hp-some"),
   (“T”, "hp-true"),
   (“F”, "hp-false"),
   (“(~):bool->bool”, "hp-not"),
   (“(/\)”, "hp-and"),
   (“(\/)”, "hp-or"),
   (“(==>)”, "hp-implies"),
   (“(!)”, "hp-forall"),
   (“(?)”, "hp-exists"),
   (“(+):num->num->num”, "hp+"),
   (“$* :num->num->num”, "hp*"),
   (“(<):num->num->bool”, "hp<")
  ];

fun lookup_const_name c = total (op_assoc same_const c) builtin_const_map;

fun mk_typ ty = Cons(Symbol "typ", List [ty_sexp ty])

(*---------------------------------------------------------------------------*)
(* Nullary polymorphic constructors need special treatment to find the type  *)
(* argument. TODO: think about what happens when the generic type has >1     *)
(* type variables in it.                                                     *)
(*---------------------------------------------------------------------------*)

fun const_sexp c =
  let val {Name,Ty,Thy} = dest_thy_const c
      val generic_const = prim_mk_const{Name=Name,Thy=Thy}
      val is_ground = null o type_vars_in_term
  in case lookup_const_name c
      of NONE => Cons(Symbol Name, List [mk_typ Ty])
       | SOME acl2_name =>
           let val tylist =
               if is_ground generic_const then
	          [] else
               if same_const c listSyntax.nil_tm then
                  [mk_typ (listSyntax.dest_list_type Ty)] else
               if same_const c optionSyntax.none_tm then
                  [mk_typ (optionSyntax.dest_option Ty)]
               else [mk_typ Ty]
           in
              Cons(Symbol acl2_name, List tylist)
           end
  end

(*---------------------------------------------------------------------------*)
(* NB: 0 is a constant but needs to be treated as a literal, so the          *)
(* "is_numeral" check has to come before the "is_const" check.               *)
(*---------------------------------------------------------------------------*)

fun tm_sexp t =
  if is_var t then
     Symbol (fst(dest_var t)) else
  if numSyntax.is_numeral t then
     let open numSyntax
         val n = dest_numeral t
         val ns = Arbnum.toString n
     in List [Symbol "hp-num", Symbol ns]
     end else
  if is_const t then
     const_sexp t else
  let val (f,args) = strip_comb t
  in if is_abs f then String "<!!lambda abstraction!!>"
     else
     (* args are non-null at this point *)
     if is_var f then
        Cons(Symbol "hap*", List (map tm_sexp (f::args))) else
     if is_const f then
        let val {Name,Thy,Ty} = dest_thy_const f
        in case lookup_const_name f
            of NONE => Cons(Symbol "hap*", List (map tm_sexp (f::args)))
             | SOME acl2_name => Cons(Symbol acl2_name, List (map tm_sexp args))
        end
     else
     String "<!unexpected term structure!>"
  end

(* TODO
 if is_cond t then
    let val (pairs,last_tm) = strip_cond t
        val pair_sexps = map (fn (t1,t2) => List [tm_sexp t1, tm_sexp t2]) pairs
        val last_pair = List[Symbol"T", tm_sexp last_tm]
    in Cons (Symbol"cond",List (pair_sexps @ [last_pair]))
    end else
*)

fun fns_entry c =
   let val {Name,Thy,Ty} = dest_thy_const c
   in List [Symbol Name, ty_sexp Ty]
   end

fun list_mk_forall_sexp vs sexp =
  if null vs then
     sexp
  else Cons(Symbol":forall", List [List (map bvar_sexp vs), sexp])

fun list_mk_forall_term vs = list_mk_forall_sexp vs o tm_sexp

(*---------------------------------------------------------------------------*)
(* Theorems come with a name                                                 *)
(*---------------------------------------------------------------------------*)

Definition THM_def:
  THM (x:bool) (y:bool) = y
End

fun mk_named_thm name thm =
 let val v = mk_var(name,bool)
 in
   THM_def |> SPEC v |> SPEC (concl thm) |> GSYM |> C EQ_MP thm
 end

fun dest_named_thm thm =
 let val (c,[v,th]) = strip_comb $ concl thm
 in if same_const ``THM`` c then
       (fst $ dest_var v,th)
    else failwith ""
 end
 handle _ => failwith "dest_named_thm";

fun thm_sexp thm =
 let val (name,tm) = dest_named_thm thm
     val (vs,body) = strip_forall tm
 in (name,
     Cons (Symbol "defhol",
           List [Cons(Symbol ":name", Symbol name),
                 Cons(Symbol ":thm",  list_mk_forall_term vs body)]))
 end

(*---------------------------------------------------------------------------*)
(* Constant specifications require the defined constants to be supplied      *)
(*---------------------------------------------------------------------------*)

Definition SPEC_def:
  SPEC x (y:bool) = y
End

fun mk_spec clist thm =
 let val tys = map type_of clist
     val consts_var = mk_var("consts", list_mk_fun(tys,bool))
     val consts_comb = list_mk_comb(consts_var, clist)
 in
   SPEC_def |> ISPEC consts_comb |> SPEC (concl thm) |> GSYM |> C EQ_MP thm
 end

fun dest_spec thm =
 let val (c,[consts,th]) = strip_comb $ concl thm
 in if same_const ``SPEC`` c then
       (snd $ strip_comb consts,th)
    else failwith ""
 end
 handle _ => failwith "dest_spec";

fun spec_sexp thm =
 let val (fns,tm) = dest_spec thm
     val {Name,...} = dest_thy_const(hd fns)
     val (vs,(left,right)) = (I##dest_eq) $ strip_forall tm
     val bare_def = Cons(Symbol"equal", List (map tm_sexp[left,right]))
 in
   (Name,
    Cons (Symbol "defhol",
          List [Cons(Symbol ":fns", List (map fns_entry fns)),
                Cons(Symbol ":defs",List [list_mk_forall_sexp vs bare_def])]))
 end

(*---------------------------------------------------------------------------*)
(* Definitions. A definition is a list of equations (clauses). A definition  *)
(* can also be a mutual recursion, introducing a list of constants.          *)
(* So a definition renders down into a list of constants paired with a list  *)
(* of clauses.                                                               *)
(*---------------------------------------------------------------------------*)

fun dest_clause_body tm = (strip_comb##I) (dest_eq tm)
fun dest_clause t = ((I ## dest_clause_body) o strip_forall) t

fun cls_qvars (vs,((c,args),r)) = vs
fun cls_lhs   (vs,((c,args),r)) = (c,args)
fun cls_rhs   (vs,((c,args),r)) = r
fun cls_const cls = fst(cls_lhs cls)

fun dest_def th =
 let open boolSyntax
     val eqns = strip_conj (concl th)
     val clauses = map dest_clause eqns
 in
   {fns = op_mk_set Term.aconv (map cls_const clauses),
    defs = clauses}
 end

(*---------------------------------------------------------------------------*)
(* Clause in a definition looks like "!vs. f a1 ... ak = rhs"                *)
(*---------------------------------------------------------------------------*)

fun clause_sexp (vs,((chd,args),r)) =
 let val {Name,Thy,Ty} = dest_thy_const chd
     val cty_sexp = Cons(Symbol"typ", List[ty_sexp Ty])
     val chd_sexp = List [Symbol Name, cty_sexp]
     val lhs_sexp = Cons(Symbol"hap*", List (chd_sexp::map tm_sexp args))
     val bare_def = Cons(Symbol"equal", List [lhs_sexp, tm_sexp r])
  in
    list_mk_forall_sexp vs bare_def
  end

fun def_sexp th =
 let val {fns,defs} = dest_def th
     val {Name,...} = dest_thy_const(hd fns)
 in (Name,
     Cons (Symbol "defhol",
           List [Cons(Symbol ":fns",   List (map fns_entry fns)),
                 Cons(Symbol ":defs",  List (map clause_sexp defs))]))
 end
 handle _ => raise ERR "def_sexp" "";

(*---------------------------------------------------------------------------*)
(* Decide between the kinds of declaration being made.                       *)
(*---------------------------------------------------------------------------*)

fun hol_sexp thm =
  def_sexp thm handle HOL_ERR _ =>
  thm_sexp thm handle HOL_ERR _ =>
  spec_sexp thm handle HOL_ERR _ => ("ERROR", Symbol "!<unknown construct>!");

(*---------------------------------------------------------------------------*)
(* Prettyprinting for ACL2 defhol form. Adapted from                         *)
(*                                                                           *)
(*   <holdir>/portableML/HOL_sexp.sml                                        *)
(*---------------------------------------------------------------------------*)

fun break_sexp_list s =
  let fun recurse A (Cons(s1,s2)) = recurse (s1::A) s2
        | recurse A s = (List.rev A, s)
  in
    recurse [] s
  end

val translate_symbol = String.translate (String.str o Char.toLower);

fun pp_sexp t =
 let open HOLPP HOLsexp_dtype
 in
   case t
    of Symbol s => add_string (translate_symbol s)
     | String s => add_string (Portable.mlquote s)
     | Integer i => add_string (if i < 0 then "-" ^ Int.toString (~i) else Int.toString i)
     | Cons _ =>
        let val (els, last) = break_sexp_list t
         in block INCONSISTENT 1 (
              add_string "(" ::
              pr_list pp_sexp [add_break(1,0)] els @
              (case last
                of Symbol "nil" => [add_string ")"]
                 | t => [add_string " .", add_break(1,0), printer t, add_string ")"])
            )
         end
 end

(*---------------------------------------------------------------------------*)
(* This taking apart of sexps and adding a little bit more formatting is     *)
(* only for presentation purposes and could be dropped.                      *)
(*---------------------------------------------------------------------------*)

fun pp_acl2 s =
  let open HOLPP HOLsexp_dtype
      fun dest_def_sexp s =
          let val Cons(Symbol"defhol", Cons(fns_elt, Cons(defs_elt, Symbol"nil"))) = s
              val Cons(Symbol":fns", fns) = fns_elt
              val Cons(Symbol":defs", defs) = defs_elt
          in (fns,defs)
          end
      fun dest_named_thm_sexp s =
          let val Cons(Symbol"defhol", Cons(name_elt, Cons(thm_elt, Symbol"nil"))) = s
              val Cons(Symbol":name", Symbol n) = name_elt
              val Cons(Symbol":thm", thm) = thm_elt
          in (n,thm)
          end
  in case total dest_def_sexp s
      of SOME(fns,defs) =>
          block CONSISTENT 3 (
              [add_string "(defhol", add_newline,
               add_string ":fns ", block CONSISTENT 1 [pp_sexp fns], add_newline,
               add_string ":defs ", block CONSISTENT 1 [pp_sexp defs], add_string ")"])
       | NONE =>
     case total dest_named_thm_sexp s
       of SOME(name,thm) =>
          block CONSISTENT 3 (
              [add_string "(defhol", add_newline,
               add_string ":name ", block CONSISTENT 1 [pp_sexp (Symbol name)], add_newline,
               add_string ":thm ", block CONSISTENT 1 [pp_sexp thm], add_string ")"])
        | NONE => pp_sexp s
  end

(*---------------------------------------------------------------------------*)
(* install pp_acl2 in REPL                                                   *)
(*---------------------------------------------------------------------------*)

val _ =
  let fun pp depth _ (s : HOLsexp.t) = pp_acl2 s
  in PolyML.addPrettyPrinter pp
  end;

(*---------------------------------------------------------------------------*)
(* Examples                                                                  *)
(*---------------------------------------------------------------------------*)

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

val acl2_defs = map hol_sexp thms

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

(*****************************************************************************)
(* Relational and clocked semantics of Pure Lisp                             *)
(*****************************************************************************)

quietdec := true;
map 
 load 
 ["stringLib","finite_mapTheory","intLib"];
open sumTheory finite_mapTheory pred_setTheory optionTheory;
Globals.checking_const_names := false;
set_trace "Subgoal number" 1000;
quietdec := false;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* Start new theory "PureLISP"                                               *)
(*****************************************************************************)
val _ = new_theory "PureLISP";

(*****************************************************************************)
(* An atom is Nil or a number or a string                                    *)
(*****************************************************************************)
val _ =
 Hol_datatype
  `atom = Nil | Number of num | String of string`;

(*****************************************************************************)
(* An S-expression is an atom or a dotted pair (cons-cell)                   *)
(*****************************************************************************)
val _ =
 Hol_datatype
  `sexpression = A of atom | Cons of sexpression => sexpression`;

(*****************************************************************************)
(* Printing utilities                                                        *)
(*****************************************************************************)
val int_of_term = numSyntax.int_of_term;

fun strip_quotes s = implode(tl(butlast(explode s)));

fun isCons tm =
 is_comb tm andalso is_comb(rator tm)
            andalso is_const(rator(rator tm))
            andalso (fst(dest_const(rator(rator tm)))) = "Cons";

fun isAtom tm =
 is_comb tm andalso is_const(rator tm)
            andalso fst(dest_const(rator tm)) = "A";

fun isNil tm =
 isAtom tm andalso rand tm = ``Nil``;

fun isSing tm =
 isCons tm andalso isNil(rand tm);

fun isList tm =
 isCons tm andalso (isNil(rand tm) orelse isList(rand tm));

val Split_def =
 Define
  `(Split(A _) = [])
   /\
   (Split(Cons e1 e2) = e1 :: Split e2)`;

(*****************************************************************************)
(* Some utility values and functions                                         *)
(*****************************************************************************)
val Num_def =
 Define
  `Num n = A(Number n)`;

val False_def =
 Define
  `False = A Nil`;

val isTrue_def =
 Define
  `isTrue s = ~(s = False)`;

val True_def =
 Define
  `True = A(String "T")`;

val Car_def =
 Define
  `Car(Cons s1 s2) = s1`;

val Cdr_def =
 Define
  `Cdr(Cons s1 s2) = s2`;

val List_def = 
 Define 
  `(List [] = A Nil) /\
   (List (s::sl) = Cons s (List sl))`;

val isList_def =
 Define
  `(isList (A a) = (a = Nil))
   /\
   (isList (Cons s1 s2) = isList s2)`;

val ListListEq =
 store_thm
  ("ListListEq",
   ``!sl1 sl2. (List sl1 = List sl2) = (sl1 = sl2)``,
   Induct 
    THEN RW_TAC list_ss [List_def]
    THENL
     [Induct_on `sl2`
       THEN RW_TAC list_ss [List_def],
      EQ_TAC
       THEN RW_TAC list_ss [List_def]
       THENL
        [Induct_on `sl2`
          THEN RW_TAC list_ss [List_def],
         METIS_TAC[List_def]]]);

val SplitList =
 store_thm
  ("SplitList",
   ``!sl. Split(List sl) = sl``,
   Induct
    THEN RW_TAC std_ss [Split_def,List_def]);

val ListSplit =
 store_thm
  ("ListSplit",
   ``!s. isList s ==> (List(Split s) = s)``,
   Induct
    THEN RW_TAC std_ss [Split_def,List_def,isList_def]);

val Eq_def =
 Define
  `Eq ((A a1),(A a2)) = if a1 = a2 then True else False`;

val Atom_def =
 Define
  `(Atom (A a) = True)
   /\
   (Atom _ = False)`;

val Add_def =
 Define
  `Add ((A(Number m)),(A(Number n))) = A(Number(m+n))`;

val Add1_def =
 Define
  `Add1 (A(Number m)) = A(Number(m+1))`;

val Sub_def =
 Define
  `Sub ((A(Number m)),(A(Number n))) = A(Number(m-n))`;

val Sub1_def =
 Define
  `Sub1 (A(Number m)) = A(Number(m-1))`;

val Mult_def =
 Define
  `Mult ((A(Number m)),(A(Number n))) = A(Number(m*n))`;

val FunConSem_def =
 Define
  `FunConSem s sl =
    if s = "car"  then Car(EL 0 sl)            else
    if s = "cdr"  then Cdr(EL 0 sl)            else 
    if s = "atom" then Atom(EL 0 sl)           else 
    if s = "eq"   then Eq(EL 0 sl,EL 1 sl)     else 
    if s = "cons" then Cons(EL 0 sl) (EL 1 sl) else 
    if s = "add"  then Add(EL 0 sl,EL 1 sl)    else 
    if s = "add1" then Add1(EL 0 sl)           else 
    if s = "sub"  then Sub(EL 0 sl,EL 1 sl)    else 
    if s = "sub1" then Sub1(EL 0 sl)           else 
    if s = "mult" then Mult(EL 0 sl,EL 1 sl)   else 
    ARB`;

(*****************************************************************************)
(* Syntax of Pure Lisp                                                       *)
(*****************************************************************************)
val _ =
 Hol_datatype
  `term = Con of sexpression
        | Var of string
        | App of func => term list
        | Ite of (term # term)list;
 
   func = FunCon of string
        | FunVar of string
        | Lambda of string list => term
        | Label  of string => func`;

(*****************************************************************************)
(* An environment (alist) is a finite function from names (strings) to       *)
(* values of type ``:sexpression + func`` (so variables and                  *)
(* Label-defined functions share the same namespace).                        *)
(*****************************************************************************)

(*****************************************************************************)
(* VarBind a xl sl extends a by binding each string in xl to the             *)
(* S-expression at the corresponding position in sl. If xl is shorter than   *)
(* sl, then only the first n elements of sl are used, where n is the         *)
(* length of x. If xl is longer than sl, than sl is padded with NILs.        *)
(*                                                                           *)
(* Subtle point: with the semantics in which clock timeout returns NONE      *)
(* having VarBind  only partially specified is no problem, but               *)
(* with the semantics in which timeout returns an S-expression it is         *)
(* tricky to distinguish the arbitrary value returned when VarBind is        *)
(* applied to lists of different lists from a real value.                    *)
(* We thus totalise VarBind as described above.                              *)
(*****************************************************************************)
val VarBind_def =
 Define
  `(VarBind a [] sl = (a : (string |-> sexpression + func)))
   /\
   (VarBind a (x::xl) [] = (VarBind a xl []) |+ (x, INL(A Nil)))
   /\
   (VarBind a (x::xl) (s::sl) = (VarBind a xl sl) |+ (x, INL s))`;

(*****************************************************************************)
(* FunBind a f fn extends a by binding fn to f                               *)
(*****************************************************************************)
val FunBind_def =
 Define
  `FunBind (a:string|->sexpression+func) f fn = a |+ (f, INR fn)`;

(*****************************************************************************)
(* Operational semantics of Pure Lisp using three inductive relations:       *)
(*                                                                           *)
(*  R_ap (fn,args,a) s - fn applied to args evaluates to s with alist a      *)
(*  R_ev (e,a) s        - term e evaluates to S-expression s with alist a    *)
(*  R_evl (el,a) sl     - term list el evaluates to S-expression list sl     *)
(*                                                                           *)
(* The names R_evl_rules, R_evl_ind, R_evl_cases are the ones                *)
(* automatically generated to name the theorems in the theory.               *)
(*                                                                           *)
(*****************************************************************************)
val (R_ap_rules,R_ap_ind,R_ap_cases) =
 Hol_reln
 `(!fc args a.
    R_ap (FunCon fc,args,a) (FunConSem fc args))
  /\
  (!fv args s a.
    R_ap (OUTR(a ' fv),args,a) s ==> R_ap (FunVar fv,args,a) s)
  /\
  (!xl e args s a.
    R_ev (e,VarBind a xl args) s 
     ==> R_ap (Lambda xl e,args,a) s)
  /\
  (!x fn args s a. 
    R_ap (fn,args,FunBind a x fn) s ==> R_ap(Label x fn,args,a) s)
  /\
  (!s a. 
    R_ev (Con s, a) s)
  /\
  (!x a. 
    R_ev (Var x, a) (OUTL(a ' x)))
  /\
  (!a.
    R_ev (Ite [], a) False)
  /\
  (!e1 e2 el s a. 
    R_ev (e1,a) False /\ R_ev (Ite el,a) s
    ==> R_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!e1 e2 el s1 s a.
    R_ev (e1,a) s1 /\ isTrue s1 /\ R_ev (e2,a) s 
    ==>
    R_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!fn el args s a. 
    R_evl (el,a) args /\ R_ap (fn,args,a) s
    ==> R_ev (App fn el,a) s)
  /\
  (!a.
    R_evl ([],a) [])
  /\
  (!e el s sl a.
    R_ev (e,a) s /\ R_evl (el,a) sl
    ==> R_evl (e::el,a) (s::sl))`;

val EvalquoteR_def =
 Define
  `EvalquoteR (fn,args) s = R_ap (fn,args,FEMPTY) s`;

(* Test example
computeLib.add_funs[FAPPLY_FUPDATE_THM];
computeLib.add_funs[FUPDATE_LIST_THM];
computeLib.add_funs[OUTL];
computeLib.add_funs[OUTR];

val Fact_def =
 Define
 `Fact =
   Label "fact"
    (Lambda ["n"]
       (Ite
          [(App (FunCon "eq") [Var "n"; Con (Num 0)],
            Con (Num 1));
           (Con True,
            App (FunCon "mult")
              [Var "n"; App (FunVar "fact") [App (FunCon "sub1") [Var "n"]]])]))`;

evalquote ``Fact`` ``[Num 6]``;

evalquote ``FunCon "car"`` ``[Cons x y]``;
evalquote ``FunCon "cdr"`` ``[Cons x y]``;
*)

(*****************************************************************************)
(* Encode options in S-expressions                                           *)
(*****************************************************************************)

val none_def =
 Define
  `none = A(String "NONE")`;

val some_def =
 Define
  `some s = Cons s (A Nil)`;

val issome_def =
 Define
  `(issome (Cons s0 s1) = (s1 = A Nil))
   /\
   (issome _ = F)`;

val somesomeEq =
 store_thm
 ("somesomeEq",
  ``(some s1 = some s2) = (s1 = s2)``,
  RW_TAC std_ss [DB.theorem "sexpression_11",some_def]);

val ListsomeEq =
 store_thm
 ("ListsomeEq",
  ``(List(s1::sl1) = Cons s2 (List sl2)) = (s1 = s2) /\ (sl1 = sl2)``,
  RW_TAC std_ss [DB.theorem "sexpression_11",some_def,List_def,ListListEq]);

val issomenone =
 store_thm
  ("issomenone",
   ``~(issome none) /\ ~(issome(A a)) /\ (issome s ==> ~(s = none))``,
   CONV_TAC EVAL
    THEN Cases_on `s`
    THEN RW_TAC std_ss [issome_def]);

val issomesome =
 store_thm
  ("issomesome",
   ``issome(some s)``,
   CONV_TAC EVAL);

val issomeExists =
 store_thm
  ("issomeExists",
   ``!x. issome x = ?s. x = some s``,
   Cases
    THEN RW_TAC std_ss [issome_def,some_def]);

val someNotEqnone =
 store_thm
  ("someNotEqnone",
   ``~(some s = none) /\ ~(none = some s)``,
   CONV_TAC EVAL);

val noneNONE =
 store_thm
  ("noneNONE",
   ``((A a = none) = (a = String "NONE")) 
     /\ 
     ((none = A a) = (a = String "NONE"))``,
   CONV_TAC EVAL
    THEN METIS_TAC[]);

val the_def =
 Define
  `the s = Car s`;

val thesome =
 store_thm
  ("thesome",
   ``the(some s) = s``,
   CONV_TAC EVAL);

val apply_c_def =
 tDefine
  "apply_c"
  `(apply_c n (fn,args,a) =
     if n=0 
      then none
      else case fn of
              FunCon fc   -> some(FunConSem fc args)
           || FunVar fv   -> apply_c (n-1) (OUTR(a ' fv),args,a)
           || Lambda xl e -> eval_c (n-1) (e,VarBind a xl args)
           || Label x fn  -> apply_c (n-1) (fn,args,FunBind a x fn))
   /\
   (eval_c n (e,a) =
     if n=0
      then none
      else case e of
              Con s              -> some s
           || Var v              -> some(OUTL(a ' v))
           || Ite []             -> some False
           || Ite ((e1,e2)::eel) -> (let s = eval_c (n-1) (e1,a) in
                                     if s = none
                                      then none
                                      else if the s = False
                                            then eval_c (n-1) (Ite eel,a)
                                            else eval_c (n-1) (e2,a))
           || App fn el          -> let sl = evlis_c (n-1) (el,a) in
                                     if  sl = none
                                      then none
                                      else apply_c (n-1) (fn,Split(the sl),a))
   /\
   (evlis_c n (el,a) =
     if n=0 
      then none
      else if NULL el
            then some(List[])
            else let s = eval_c (n-1) (HD el,a) in
                 if s = none
                  then none 
                  else let sl = evlis_c (n-1) (TL el, a) in
                       if sl = none then none else some(Cons (the s) (the sl)))`
 (WF_REL_TAC
   `measure 
     \x. if ISL x 
          then FST(OUTL x) else
         if ISR x /\ ISL(OUTR x) 
          then FST(OUTL(OUTR x)) 
          else FST(OUTR(OUTR x))`
    THEN RW_TAC arith_ss []);   

val EvalquoteEnc_def =
 Define
  `EvalquoteEnc n (fn,args) = apply_c n (fn,args,FEMPTY)`;

(* Factorial function

computeLib.add_funs[FAPPLY_FUPDATE_THM];
computeLib.add_funs[FUPDATE_LIST_THM];
computeLib.add_funs[OUTL];
computeLib.add_funs[OUTR];


val fact_tm =
 ``Label "fact"
    (Lambda ["n"]
       (Ite
          [(App (FunCon "eq") [Var "n"; Con (Num 0)],
            Con (Num 1));
           (Con True,
            App (FunCon "mult")
              [Var "n"; App (FunVar "fact") [App (FunCon "sub1") [Var "n"]]])]))`` ;

EVAL ``eval_c 63 (App ^fact_tm [Con(Num 1)],a)``;

EVAL ``eval_c 63 (App ^fact_tm [Con(Num 7)],a)``;
EVAL ``eval_c 64 (App ^fact_tm [Con(Num 7)],a)``;

EVAL ``EvalquoteEnc 62 (^fact_tm, [Num 7])``;
EVAL ``EvalquoteEnc 63 (^fact_tm, [Num 7])``;

EVAL ``EvalquoteEnc 10000 (APP Car [Cons x y])``;
*)

val apply_cCases =
 store_thm
  ("apply_cCases",
   ``(!fn args a. issome(apply_c n (fn,args,a)) \/ (apply_c n (fn,args,a) = none))
     /\
     (!e a. issome(eval_c n (e,a)) \/ (eval_c n (e,a) = none))
     /\
     (!el a. issome(evlis_c n (el,a)) \/ (evlis_c n (el,a) = none))``,
   Induct_on `n`
    THEN RW_TAC list_ss
          [SIMP_RULE arith_ss [] (INST[``n:num``|->``SUC n``]apply_c_def),
           SIMP_RULE arith_ss [] (INST[``n:num``|->``0``]apply_c_def),
           issomesome,someNotEqnone,LET_DEF]
    THENL
     [Cases_on `fn` 
       THEN RW_TAC std_ss [issomesome],
      Cases_on `e` 
       THEN RW_TAC std_ss [issomesome]
       THEN Induct_on `l`
       THEN RW_TAC std_ss [issomesome]
       THEN Cases_on `h`
       THEN RW_TAC std_ss [issomesome]]);

val apply_cCasesCor =
 store_thm
  ("apply_cCasesCor",
   ``(!fn n args a. issome(apply_c n (fn,args,a)) \/ (apply_c n (fn,args,a) = none))
     /\
     (!e n a. issome(eval_c n (e,a)) \/ (eval_c n (e,a) = none))
     /\
     (!el n a. issome(evlis_c n (el,a)) \/ (evlis_c n (el,a) = none))``,
    METIS_TAC[apply_cCases]);

val apply_c =
 store_thm
  ("apply_c",
   ``(apply_c 0 (fn,args,a) = none)
     /\
     (apply_c (SUC n) (FunCon fc,args,a) = some(FunConSem fc args))
     /\
     (apply_c (SUC n) (FunVar fv,args,a) = apply_c n (OUTR(a ' fv),args,a))
     /\
     (apply_c (SUC n) (Lambda xl e,args,a) = eval_c n (e,VarBind a xl args))
     /\
     (apply_c (SUC n) (Label x fn,args,a) = apply_c n (fn,args,FunBind a x fn))
     /\
     (eval_c 0 (e,a) = none)
     /\
     (eval_c (SUC n) (Con s,a) = some s)
     /\
     (eval_c (SUC n) (Var v,a) = some(OUTL(a ' v)))
     /\
     (eval_c (SUC n) (Ite [],a) = some False)
     /\
     (eval_c (SUC n) (Ite ((e1,e2)::eel),a) = 
       if issome(eval_c n (e1,a)) 
        then (if the(eval_c n (e1,a)) = False
               then eval_c n (Ite eel,a)
               else eval_c n (e2,a))
        else none)
     /\
     (eval_c (SUC n) (App fn el,a) = 
       if issome(evlis_c n (el,a)) 
        then apply_c n (fn,Split(the(evlis_c n (el,a))),a)
        else none)
     /\
     (evlis_c 0 (el,a) = none)
     /\
     (evlis_c (SUC n) ([],a) = some(List[]))
     /\
     (evlis_c (SUC n) (e::el,a) =
       if issome(eval_c n (e,a))
        then (if issome(evlis_c n (el,a))
               then some(Cons (the(eval_c n (e,a))) (the(evlis_c n (el,a))))
               else none)
        else none)``,
   RW_TAC list_ss 
    [SIMP_RULE arith_ss [] (INST[``n:num``|->``SUC n``]apply_c_def),
     SIMP_RULE arith_ss [] (INST[``n:num``|->``0``]apply_c_def)]
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
    THEN TRY(DISJ_CASES_TAC (Q.SPECL [`e1`,`a`] (el 2 (CONJUNCTS apply_cCases))))
    THEN TRY(DISJ_CASES_TAC (Q.SPECL [`el`,`a`] (el 3 (CONJUNCTS apply_cCases))))
    THEN TRY(DISJ_CASES_TAC (Q.SPECL [`e`,`a`] (el 2 (CONJUNCTS apply_cCases))))
    THEN FULL_SIMP_TAC std_ss [issomenone,noneNONE]);

val isListevlis_c =
 store_thm
  ("isListevlis_c",
   ``!el n s. (evlis_c n (el,a) = some s) ==> isList s``,
   Induct
    THEN RW_TAC list_ss [apply_c,someNotEqnone,somesomeEq,isList_def,List_def]
    THEN Cases_on `n`
    THEN FULL_SIMP_TAC list_ss [apply_c,someNotEqnone,somesomeEq,isList_def,List_def]
    THEN RW_TAC std_ss [isList_def]
    THEN DISJ_CASES_TAC (Q.SPECL [`h`,`n'`,`a`] (el 2 (CONJUNCTS apply_cCasesCor)))
    THEN DISJ_CASES_TAC (Q.SPECL [`el`,`n'`,`a`] (el 3 (CONJUNCTS apply_cCasesCor)))
    THEN FULL_SIMP_TAC std_ss [issomenone,noneNONE,someNotEqnone,issomeExists,somesomeEq]
    THEN RW_TAC std_ss [isList_def,thesome]
    THEN METIS_TAC[]);

local
val TAC0 =
 Q.EXISTS_TAC `0` 
  THEN RW_TAC arith_ss []
  THEN `?m. n = SUC m` by intLib.COOPER_TAC
  THEN RW_TAC std_ss [apply_c,LET_THM]  
  THEN METIS_TAC[]
val TAC1 =
 Q.EXISTS_TAC `SUC m`
  THEN RW_TAC std_ss []
  THEN `?p. (n = SUC p) /\ m < p` by intLib.COOPER_TAC
  THEN RW_TAC std_ss [apply_c,isTrue_def,LET_THM]
  THEN METIS_TAC[]
val TAC2 =
 Q.EXISTS_TAC `SUC(m+m')`
  THEN RW_TAC std_ss []
  THEN `?p. (n = SUC p) /\ m < p /\ m' < p` by intLib.COOPER_TAC
  THEN RW_TAC std_ss [apply_c,isTrue_def,LET_THM,issomesome]
  THEN METIS_TAC
        [isTrue_def,False_def,DB.theorem "atom_distinct",apply_c,
         SplitList,DB.theorem "sexpression_11",EVAL ``True = False``,
         issomesome,thesome,somesomeEq,ListsomeEq]
in
val R_ap_apply_c_lemma =
 store_thm
  ("R_ap_apply_c_lemma",
   ``(!fnargsa s.
       R_ap fnargsa s
       ==> (\fnargsa s. ?m. !n. m < n ==> (some s = apply_c n fnargsa)) fnargsa s)
     /\
     (!ea s.
       R_ev ea s
       ==> (\ea s. ?m. !n. m < n ==> (some s = eval_c n ea)) ea s)
     /\
     (!ela sl.
       R_evl ela sl
       ==> (\ela sl. ?m. !n. m < n ==> (some(List sl) = evlis_c n ela)) ela sl)``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (R_ap_rules,R_ap_ind))
    THEN RW_TAC std_ss [LET_THM]
    THEN TRY(TAC0 ORELSE TAC1 ORELSE TAC2))
end;

val R_ap_apply_c =
 store_thm
  ("R_ap_apply_c",
   ``(!fnargsa s. R_ap fnargsa s ==> ?n. some s = apply_c n fnargsa)
     /\
     (!ea s. R_ev ea s ==> ?n. some s = eval_c n ea)
     /\
     (!ela sl. R_evl ela sl ==> ?n. some(List sl) = evlis_c n ela)``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC R_ap_apply_c_lemma
    THEN FULL_SIMP_TAC std_ss []
    THEN `m < SUC m` by DECIDE_TAC
    THEN METIS_TAC[]);

val apply_c_R_ap_lemma =
 store_thm
  ("apply_c_R_ap_lemma",
   ``(!fn args s a. (apply_c n (fn,args,a) = some s) ==> R_ap (fn,args,a) s)
     /\
     (!e s a. (eval_c n (e,a) = some s) ==> R_ev (e,a) s)
     /\
     (!el sl a. (evlis_c n (el,a) = some(List sl)) ==> R_evl (el,a) sl)``,
   Induct_on `n`
    THEN RW_TAC std_ss [apply_c,R_ap_rules,someNotEqnone]
    THENL
     [Cases_on `fn`
       THEN FULL_SIMP_TAC std_ss [apply_c,R_ap_rules,somesomeEq]
       THEN RW_TAC std_ss [apply_c,R_ap_rules],
      Cases_on `e`
       THEN FULL_SIMP_TAC std_ss [apply_c,R_ap_rules,somesomeEq]
       THEN RW_TAC std_ss [apply_c,R_ap_rules]
       THENL
        [DISJ_CASES_TAC (Q.SPECL [`l`,`a`] (el 3 (CONJUNCTS apply_cCases)))
          THEN FULL_SIMP_TAC std_ss [apply_c,R_ap_rules,somesomeEq,issomeExists]
          THEN RES_TAC
          THEN METIS_TAC[someNotEqnone,thesome,isListevlis_c,ListSplit,R_ap_rules],
         Induct_on `l`
          THEN RW_TAC std_ss [apply_c,R_ap_rules,somesomeEq]
          THEN RW_TAC std_ss [apply_c,R_ap_rules,somesomeEq]
          THEN Cases_on `h`
          THEN Cases_on `eval_c n (q,a) = some False`
          THENL
           [RES_TAC
             THEN FULL_SIMP_TAC std_ss [apply_c,issomesome,thesome]
             THEN METIS_TAC[R_ap_rules],
            FULL_SIMP_TAC std_ss [apply_c,issomesome,thesome]
             THEN DISJ_CASES_TAC (Q.SPECL [`q`,`a`] (el 2 (CONJUNCTS apply_cCases)))
             THEN FULL_SIMP_TAC std_ss [apply_c,R_ap_rules,somesomeEq,issomeExists]
             THEN METIS_TAC[R_ap_rules,isTrue_def,thesome,somesomeEq]]],
      Induct_on `el`
       THEN FULL_SIMP_TAC std_ss [apply_c,R_ap_rules]
       THEN RW_TAC std_ss [apply_c,R_ap_rules]
       THEN RW_TAC std_ss [apply_c,R_ap_rules]
       THENL
        [DISJ_CASES_TAC (Q.SPECL [`el`,`a`] (el 3 (CONJUNCTS apply_cCases)))
          THEN FULL_SIMP_TAC std_ss [somesomeEq,issomeExists,ListListEq]
          THEN RW_TAC std_ss [R_ap_rules],
         DISJ_CASES_TAC (Q.SPECL [`h`,`a`] (el 2 (CONJUNCTS apply_cCases)))
          THEN FULL_SIMP_TAC std_ss [somesomeEq,issomeExists,ListListEq,thesome,someNotEqnone]
          THEN `sl = Split(Cons s' s)` by METIS_TAC[thesome,SplitList]
          THEN RW_TAC std_ss [Split_def]
          THEN METIS_TAC[ListSplit,R_ap_rules,isListevlis_c],
         FULL_SIMP_TAC std_ss [someNotEqnone],
         FULL_SIMP_TAC std_ss [someNotEqnone]]]);

val apply_c_R_ap =
 store_thm
  ("apply_c_R_ap",
   ``(!fnargsa s. (apply_c n fnargsa = some s) ==> R_ap fnargsa s)
     /\
     (!ea s. (eval_c n ea = some s) ==> R_ev ea s)
     /\
     (!ela sl. (evlis_c n ela = some(List sl)) ==> R_evl ela sl)``,
   RW_TAC std_ss []
    THENL
     [Cases_on `fnargsa` THEN Cases_on `r`,
      Cases_on `ea`,
      Cases_on `ela`]
    THEN METIS_TAC[apply_c_R_ap_lemma]);

val apply_c_R_ap_EQ =
 store_thm
  ("apply_c_R_ap_EQ",
   ``(!fnargsa s. R_ap fnargsa s = ?n. some s = apply_c n fnargsa)
     /\
     (!ea s. R_ev ea s = ?n. some s = eval_c n ea)
     /\
     (!ela sl. R_evl ela sl = ?n. some(List sl) = evlis_c n ela)``,
   METIS_TAC[R_ap_apply_c,apply_c_R_ap]);

(*****************************************************************************)
(* Tool to compute s such that R_ap (fn,args,a) s                            *)
(*****************************************************************************)
fun apply fn_tm args_tm a =
 MATCH_MP
  (REWRITE_RULE[some_def](hd(CONJUNCTS apply_c_R_ap)))
  (EVAL ``apply_c 1000000000 (^fn_tm,^args_tm,a)``);

(*****************************************************************************)
(* Add some library theorems to the evaluator compset to make computation on *)
(* finite functions work.                                                    *)
(*****************************************************************************)
computeLib.add_funs[FAPPLY_FUPDATE_THM];
computeLib.add_funs[FUPDATE_LIST_THM];
computeLib.add_funs[OUTL];
computeLib.add_funs[OUTR];

(*****************************************************************************)
(* Example: factorial function                                               *)
(*****************************************************************************)
val Fact_def =
 Define
 `Fact =
   Label "fact"
    (Lambda ["n"]
       (Ite
          [(App (FunCon "eq") [Var "n"; Con (Num 0)],
            Con (Num 1));
           (Con True,
            App (FunCon "mult")
              [Var "n"; 
               App (FunVar "fact") [App (FunCon "sub1") [Var "n"]]])]))`;

(*****************************************************************************)
(* Evaluate 6!, 20!, 50! and 100! in the empty environment                   *)
(*****************************************************************************)
apply ``Fact`` ``[Num 6]``   ``FEMPTY``;
apply ``Fact`` ``[Num 20]``  ``FEMPTY``;
apply ``Fact`` ``[Num 50]``  ``FEMPTY``;
apply ``Fact`` ``[Num 100]`` ``FEMPTY``;

(*****************************************************************************)
(* Check (EQ (CAR(CONS X Y)) X) and (EQ (CDR(CONS X Y)) Y) by computation    *)
(*****************************************************************************)
apply ``FunCon "car"`` ``[Cons x y]`` ``FEMPTY``;
apply ``FunCon "cdr"`` ``[Cons x y]`` ``FEMPTY``;



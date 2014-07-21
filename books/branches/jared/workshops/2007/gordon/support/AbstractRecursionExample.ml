quietdec := true;
map
 load
 ["stringLib","finite_mapTheory","intLib"];
Globals.checking_const_names := false;
set_trace "Subgoal number" 1000;
intLib.deprecate_int();
quietdec := false;


(*****************************************************************************)
(* f x = if p x then q x else h x (f(k x))                                   *)
(*****************************************************************************)

val (f_rel_rules,f_rel_ind,f_rel_cases) =
 Hol_reln
  `(!x. p x ==> f_rel (p,q,h,k) x (q x)) 
   /\
   (!x. ~(p x) /\ f_rel (p,q,h,k) (k x) y ==> f_rel (p,q,h,k) x (h x y))`;

val f_eq_rel_lemma =
 store_thm
  ("f_eq_rel_lemma",
   ``(!x p q h k. 
       f (p,q,h,k) x = if p x then q x else h x (f (p,q,h,k) (k x)))
     ==>
     !x y pqhk. f_rel pqhk x y ==>  (\pqhk x y. (y = f pqhk x)) pqhk x y``,
   STRIP_TAC
    THEN IndDefRules.RULE_TAC
          (IndDefRules.derive_mono_strong_induction [] (f_rel_rules,f_rel_ind))
    THEN BETA_TAC
    THEN METIS_TAC[]);

val f_eq_rel_lemma =
 store_thm
  ("f_eq_rel_lemma",
   ``!pqhk x y. 
       f_rel pqhk x y 
       ==>  
       (\pqhk x y. 
         (!x. f pqhk x = 
               let (p,q,h,k) = pqhk in
               if p x then q x else h x (f (p,q,h,k) (k x)))
         ==>
         (y = f pqhk x)) pqhk x y``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (f_rel_rules,f_rel_ind))
    THEN pairLib.GEN_BETA_TAC 
    THEN CONV_TAC(TOP_DEPTH_CONV pairLib.let_CONV)
    THEN METIS_TAC[]);

val f_eq_rel_thm =
 store_thm
  ("f_eq_rel_thm",
   ``!p q h k x y. 
       (!x. 
          f (p,q,h,k) x = if p x then q x else h x (f (p,q,h,k) (k x)))
       /\  
       f_rel (p,q,h,k) x y 
       ==>
       (y = f (p,q,h,k) x)``,
   METIS_TAC
    [CONV_RULE 
     (TOP_DEPTH_CONV pairLib.let_CONV)
     (Q.SPEC
       `(p,q,h,k)`
       (CONV_RULE (TOP_DEPTH_CONV pairLib.GEN_BETA_CONV) f_eq_rel_lemma))]);

val f_clk_def =
 Define
  `f_clk (p,q,h,k) n x = 
    if n=0 
     then NONE 
     else if p x 
      then SOME(q x) 
      else case f_clk (p,q,h,k) (n-1) (k x) of
              NONE   -> NONE
           || SOME y -> SOME(h x y)`;

val f_rel_clk_lemma =
 store_thm
  ("f_rel_clk_lemma",
    ``!x y pqhk.
       f_rel pqhk x y 
       ==> 
       (\pqhk x y. ?m. !n. m < n ==> (f_clk pqhk n x = SOME y)) pqhk x y``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (f_rel_rules,f_rel_ind))
    THEN RW_TAC std_ss [LET_THM]
    THENL
     [Q.EXISTS_TAC `0` 
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC arith_ss [LET_THM]
       THEN ONCE_REWRITE_TAC [f_clk_def]  
       THEN RW_TAC arith_ss [],
      Q.EXISTS_TAC `SUC m` 
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC arith_ss [LET_THM]
       THEN `m < m'` by DECIDE_TAC
       THEN RES_TAC
       THEN ONCE_REWRITE_TAC [f_clk_def]  
       THEN RW_TAC arith_ss []]);

val f_rel_clk =
 store_thm
  ("f_rel_clk",
    ``!x y pqhk. f_rel pqhk x y ==> ?n. f_clk pqhk n x = SOME y``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC f_rel_clk_lemma
    THEN FULL_SIMP_TAC std_ss []
    THEN `m < SUC m` by DECIDE_TAC
    THEN METIS_TAC[]);

val f_clk =
 store_thm
  ("f_clk",
   ``(f_clk pqhk 0 x = NONE)
     /\
     (f_clk (p,q,h,k) (SUC n) x = 
       if p x 
        then SOME(q x)
        else case f_clk (p,q,h,k) n (k x) of
                NONE   -> NONE
             || SOME y -> SOME(h x y))``,
   Cases_on `pqhk` THEN Cases_on `r` THEN Cases_on `r'`
    THEN RW_TAC std_ss 
          [SIMP_RULE arith_ss [] (INST[``n:num``|->``0``]f_clk_def),
           SIMP_RULE arith_ss [] (INST[``n:num``|->``SUC n``]f_clk_def)]);

val f_clk_rel_lemma =
 store_thm
  ("f_clk_rel_lemma",
   ``!n x y p q h k. 
      (f_clk (p,q,h,k) n x = SOME y) ==> f_rel (p,q,h,k) x y``,
    Induct
     THEN RW_TAC std_ss [f_clk,f_rel_rules]
     THEN Cases_on `f_clk (p,q,h,k) n (k x)`
     THEN FULL_SIMP_TAC std_ss []
     THEN METIS_TAC[f_rel_rules]);

val f_clk_rel =
 store_thm
  ("f_clk_rel",
   ``!n pqhk x y. (f_clk pqhk n x = SOME y) ==> f_rel pqhk x y``,
    Cases_on `pqhk` THEN Cases_on `r` THEN Cases_on `r'`
     THEN METIS_TAC[f_clk_rel_lemma]);
   
val f_thm =
 store_thm
  ("f_thm",
   ``!x y pqhk. f_rel pqhk x y = ?n. f_clk pqhk n x = SOME y``,
   METIS_TAC[f_clk_rel,f_rel_clk]);

(*****************************************************************************)
(* Versions with ARB for timeout                                             *)
(*****************************************************************************)
val f_clk_ARB_def =
 Define
  `f_clk_ARB (p,q,h,k) n x = 
    if n=0 
     then ARB
     else if p x then q x else h x (f_clk_ARB (p,q,h,k) (n-1) (k x))`;

val f_rel_clk_ARB_lemma =
 store_thm
  ("f_rel_clk_ARB_lemma",
    ``!x y pqhk.
       f_rel pqhk x y 
       ==> 
       (\pqhk x y. ?m. !n. m < n ==> (f_clk_ARB pqhk n x = y))pqhk x y``,
   IndDefRules.RULE_TAC
    (IndDefRules.derive_mono_strong_induction [] (f_rel_rules,f_rel_ind))
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `0` 
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC arith_ss [LET_THM]
       THEN ONCE_REWRITE_TAC [f_clk_ARB_def]  
       THEN RW_TAC arith_ss [],
      Q.EXISTS_TAC `SUC m` 
       THEN RW_TAC arith_ss []
       THEN `?m. n = SUC m` by intLib.COOPER_TAC
       THEN RW_TAC arith_ss [LET_THM]
       THEN `m < m'` by DECIDE_TAC
       THEN RES_TAC
       THEN ONCE_REWRITE_TAC [f_clk_ARB_def]  
       THEN RW_TAC arith_ss []]);

val f_rel_clk_ARB =
 store_thm
  ("f_rel_clk_ARB",
    ``!x y pqhk. f_rel pqhk x y ==> ?n. f_clk_ARB pqhk n x = y``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC f_rel_clk_ARB_lemma
    THEN FULL_SIMP_TAC std_ss []
    THEN `m < SUC m` by DECIDE_TAC
    THEN METIS_TAC[]);

val f_clk_ARB =
 store_thm
  ("f_clk_ARB",
   ``(f_clk_ARB pqhk 0 x = ARB)
     /\
     (f_clk_ARB (p,q,h,k) (SUC n) x = 
       if p x then q x else h x (f_clk_ARB (p,q,h,k) n (k x)))``,
   Cases_on `pqhk` THEN Cases_on `r` THEN Cases_on `r'`
    THEN RW_TAC std_ss 
          [SIMP_RULE arith_ss [] (INST[``n:num``|->``0``]f_clk_ARB_def),
           SIMP_RULE arith_ss [] (INST[``n:num``|->``SUC n``]f_clk_ARB_def)]);

val f_clk_rel_ARB =
 store_thm
  ("f_clk_rel_ARB",
   ``!n x y p q h k. 
      (!x. h x ARB = ARB)
      /\ ~(y = ARB) /\ (f_clk_ARB (p,q,h,k) n x = y) 
      ==> f_rel (p,q,h,k) x y``,
    Induct
     THEN RW_TAC std_ss [f_clk_ARB]
     THEN METIS_TAC[f_rel_rules]);

val f_ARB_thm =
 store_thm
  ("f_ARB_thm",
   ``!x y p q h k. 
      (!x. h x ARB = ARB) 
      ==>
      !y. ~(y = ARB)
          ==>
          (f_rel (p,q,h,k) x y = ?n. f_clk_ARB (p,q,h,k) n x = y)``,
   METIS_TAC[f_clk_rel_ARB,f_rel_clk_ARB]);

Theory datatypes
Ancestors
  hol_to_acl2 combin
Libs
  HOL_to_ACL2

Datatype:
  ntree = nLeaf num | nNode ntree num ntree
End

Datatype:
  btree = bLeaf 'a | bNode btree 'a btree
End

Datatype:
  tree   = Leaf  | Node 'a forest ;
  forest = Empty | Cons tree forest
End

Datatype:
  alt = Left 'a | Right 'b
End

Datatype:
  trio = T1 'a | T2 'b | T3
End

Datatype:
  flist = fNil 'b | fCons flist 'a
End

(*---------------------------------------------------------------------------*)
(* Exercise translation of constructor terms                                 *)
(*---------------------------------------------------------------------------*)

Theorem ntree_refl:
  nLeaf 3 = nLeaf 3 ∧
  nLeaf 4 = nLeaf (2 + 2) ∧
  nNode (nLeaf 3) 2 (nLeaf 4) = nNode (nLeaf 3) 2 (nLeaf 4)
Proof
  EVAL_TAC
QED

Definition insert_ntree_def:
  (insert_ntree m (nLeaf n) =
     if m = n then
        nLeaf n else
     if m < n then
        nNode (nLeaf m) n (nLeaf 0)
     else
        nNode (nLeaf 0) m (nLeaf n)) ∧
  (insert_ntree m (nNode nt1 n nt2) =
     if m = n then
        nNode nt1 m nt2 else
     if m < n then
        nNode (insert_ntree m nt1) n nt2
     else
        nNode nt1 n (insert_ntree m nt2))
End

Theorem btree_refl:
  bLeaf x = bLeaf x ∧
  bLeaf x = bLeaf (I x) ∧
  bNode (bLeaf x) y (bLeaf z) = bNode (bLeaf (K x y)) y (bLeaf z)
Proof
  EVAL_TAC
QED

Definition insert_btree_def:
  (insert_btree leq x (bLeaf y) =
     if x = y then
        bLeaf y else
     if leq x y then
        bNode (bLeaf x) y (bLeaf y)
     else
        bNode (bLeaf y) y (bLeaf x)) ∧
  (insert_btree leq x (bNode nt1 y nt2) =
     if x = y then
        bNode nt1 y nt2 else
     if leq x y then
        bNode (insert_btree leq x nt1) y nt2
    else
        bNode nt1 y (insert_btree leq x nt2))
End

(*---------------------------------------------------------------------------*)
(* Implicits                                                                 *)
(*---------------------------------------------------------------------------*)

Theorem tree_refl:
  Leaf = Leaf ∧
  Leaf ≠ Node x f
Proof
  EVAL_TAC
QED

Theorem alt_refl:
  Left 1 = Left 1 ∧
  Left (a:'a) ≠ Right (a:'a) ∧
  Left (a:'a) ≠ Right (b:'b)
Proof
  EVAL_TAC
QED

Theorem trio_refl:
  (T1 x = T1 y ⇔ x = y) ∧
  ((T1 a :('a,num)trio) ≠ T2 b) ∧
  (T3 : (bool,num)trio = T3)
Proof
  EVAL_TAC
QED

Theorem flist_refl:
  (fNil x = fNil y ⇔ x = y) ∧
  (fCons fl x ≠ fNil y)
Proof
  EVAL_TAC
QED

(*---------------------------------------------------------------------------*)
(* Export                                                                    *)
(*---------------------------------------------------------------------------*)

val defs =
    map def_bundle
        [insert_ntree_def, I_THM, K_THM, insert_btree_def]

val thms =
    [thm_bundle "ntree_refl" ntree_refl,
     thm_bundle "btree_refl" btree_refl,
     thm_bundle "tree_refl"  tree_refl,
     thm_bundle "alt_refl"   alt_refl,
     thm_bundle "trio_refl"  trio_refl,
     thm_bundle "flist_refl" flist_refl]

val _ = print_bundles_to_file
         "datatypes.defhol"
         (map dtype_bundle
              [“:ntree”,
               “:'a btree”,
               “:'a tree”,
               “:'a forest”,
               “:('a,'b) alt”,
               “:('a,'b) trio”,
               “:('a,'b) flist”]
         @ defs @ thms)

Theory mirror
Ancestors
  hol_to_acl2 combin
Libs
  HOL_to_ACL2

Datatype:
  btree = Leaf 'a | Node btree 'a btree
End

Definition mirror_def:
   mirror (Leaf x) = Leaf x ∧
   mirror (Node l x r) = Node (mirror r) x (mirror l)
End

Theorem mirror_id:
  ∀t. mirror (mirror t) = t
Proof
  Induct >> rw [mirror_def]
QED

val bundles =
    full_dtype_bundle “:'a btree” @
    [def_bundle mirror_def,
     goal_bundle "mirror_id" (concl mirror_id)]

val _ = print_bundles_to_file "mirror.defhol" bundles

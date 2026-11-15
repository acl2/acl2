These files contain ACL2 scripts for the proof described in the paper, "Formalizing the Chandy–Lamport Distributed Snapshot
Reordering Theorem in ACL2", Monjil & Ray, submitted in ACL2 Workshop 2026.

model.lisp : Contains the main distributed system model.
scan.lisp : Contains the scan function that builds and updates the cut-meta tracking checkpoint status of the implementation state.
basic.lisp : Contains some primitive list processing lemmas and a few simple lemmas about the model.
good_state_inv.lisp : Defines the structural well-formedness of an implementation state. Proves its preservation under system-transition for all input types.
channel_equivalence.lisp : A few definition and simple lemmas used in the main proof.
cut_meta_inv.lisp: Defines structural well-formedness of cut-meta-data, consistency between cut-meta and implementation state, and cut-markers-in-transit-p. Proves their preservation under system-transition.
recovery_inv.lisp: Defines a predicate describing that the current state has no recovery activity eg. there is no recovery msg anywhere in the system and no process has status 'recovering'. Also proves that no_recovery_state is preseved under system-transition for start-checkpoint, receive, normal and nop input types.
local_swap.lisp: Defines the the checkpoint start-end segment predicate for an input segment. Proves the local swap theorem.
global_reorder.lisp: Proves the main global theorem descibing the Chandy-Lamport Distributed Snapshot Reordering. 

Most of the theorems in local_swap and global_reorder uses two predicates (cl-checkpoint-body-inputs-p and recovery-free-state-p) which the paper ommits for brevity in the shown codes. These predicates define the allowable state with no recovery activity and the allowable input types (start-checkpoint, receive, normal and nop) such that no recovery activity can begin.

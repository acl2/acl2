NOTE: This directory likely requires the latest "bleeding edge" version of ACL2
from github.  Older versions, such as the most recent official release, will
likely not work.

Contents of this directory (email ewsmith@gmail.com with any questions):

Proof support:
support.lisp

Simple proof of add+3 program:
add-plus-3.lisp

One-round Blake2s proof:
blake2s1round.old.lisp -- The spec (original version)
blake2s1round.lisp -- The spec (with change to f-loop-1)
blake2s-one-round-r1cs.lisp -- The R1CS
blake2s-one-round-spec-openers.lisp -- Rules to unroll the spec
blake2s-one-round-proof.lisp -- Proof via bit-blasting
blake2s-one-round-proof2.lisp -- Proof via recovering structure

Full Blake2s proof:
(Spec is in ACL2 Community books)
blake2s-r1cs.lisp -- The R1CS for Blake2s
blake2s-spec-openers.lisp -- Rules to unroll the spec
Note: Proof by bit-blasting currently does not scale to full Blake2s
blake2s-proof2.lisp -- Proof via recovering structure

Misc:
top.lisp - bundle up several files

# A Formal Proof of the Banach-Tarski theorem:

## Main reference:  Weston, T.. “THE BANACH-TARSKI PARADOX.” (2003).

## Goal: Prove the Banach-Tarski theorem in ACL2(r)

There are four stages to the proof of the Banach-tarski theorem for a solid sphere centered
at origin with radius equal to 1:

#### Stage1: Hausdorff paradox

#### Stage2: Banach-Tarski Theorem for the surface of the sphere

#### Stage3: Banach-Tarski theorem for a solid ball centered at origin except for the orgin

#### Stage4: Prove the Banach-Tarski theorem for the entire ball

##### Progress:

Finished Stage1 of the proof.

Stage1:
Hausdorff Paradox: There is a countable set D that is a subset of S^2 such that S^2-D can be divided into 5 pieces which can then be rotated to form 2 copies of S^2-D.

Proved the equivalence between different partitions of S^2-D. hausdorff-paradox.lisp contains the proof.
proved that the set D is countable. hausdorff-paradox-2.lisp contains the proof.
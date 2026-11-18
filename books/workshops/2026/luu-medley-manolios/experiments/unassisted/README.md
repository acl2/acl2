# ACL2 formalization of "GPU-Accelerated Search for Fast Matrix Multiplication over F_2" (ALENEX 2027)

All work lives in this folder.  Nothing in the ACL2 fork (`~/Documents/acl2-copy`)
was modified; the books only `include-book` its certified community books
(std/lists, kestrel/lists-light/perm, arithmetic-5, ordinals).

## How to certify

```bash
./cert.sh top.lisp
```

`cert.sh` runs the fork's `books/build/cert.pl` with `ACL2` and
`ACL2_SYSTEM_BOOKS` pointing at the fork.  `try.sh <book>` certifies one book
and prints the key checkpoints on failure.

## Representation

* A vector over F_2 of length `L` is a true list of `L` bits (`bvp`); addition is
  `bv+` (componentwise xor).  An `n x n` matrix is a vector of length `n*n` with
  entry `(i,j)` at index `i*n+j` (`midx`), exactly the bit convention of the
  paper's Appendix A.
* A rank-one tensor `A (x) B (x) C` is `(outer3 A B C)`, a vector of length
  `(n*n)^3`; coordinate `(a,b,c)` is at `(tidx3 L L a b c)`.
* A summand is a list `(A B C)`; a scheme is a list of summands read as a
  multiset (two lists that are permutations, `perm`, denote the same vertex).
* Moves are `(:flip p s u)` and `(:plus p piv tgt)`; `apply-move` deletes zero
  summands; `apply-path` applies a list of moves.

## Map from the paper to the books

| Paper | Book | Main events |
|---|---|---|
| Def. 2.1 (the tensor `M^(n)`) | `mmt.lisp`, `mmt-def.lisp` | `mmt`, `nth-of-mmt` (coordinate formula `delta_{g,k} delta_{h,i} delta_{j,l}`); `mmt-satisfies-definition` (for all `D,F`: `tensor-eval(M,D,F) = matmul(D,F)`); `mmt-unique` (any tensor satisfying the equation is `M`) |
| Eq. (2.2)/(2.3), rank-`R` decompositions | `mmt.lisp` | `triple-sum`, `naive-scheme` (the trivial rank-`n^3` scheme), `schemep-of-naive-scheme` |
| Def. 2.2 (schemes; unique factorization over F_2) | `scheme.lisp`, `outer.lisp` | `schemep`, `summandp`; `outer3-factor-A-unique` |
| Def. 2.3 (flip, plus) and the remark that they preserve `M^(n)` | `scheme.lisp` | `flip-results`, `plus-results`, `flip-preserves-sum`, `plus-preserves-sum`, `apply-move-preserves-schemep`, `apply-path-preserves-schemep`; multiset soundness: `defcong perm ...` |
| Observation 4.1 | `scheme.lisp` | `delete-pair-move-ok`, `apply-delete-pair-move` |
| Lemma 4.1 | `mmt.lisp` | `mmt` is defined as `sum_{i,j,k} E_ij (x) E_jk (x) E_ik`; `nth-of-mmt` is the coordinate formula |
| Lemma 4.2 (span) | `span.lisp` | `span-lemma`: the slice sum of the `p`-factors is `E_xy` (constructive coefficient comparison); `not-all-facs-equal` |
| Lemma 4.3 | `add-dup.lisp` | `add-dup-path` (the 4-move / 2-move path of Fig. 1), `add-dup-lemma` |
| Lemma 4.4 | `add-arbitrary.lisp` | `add-arb-path`, `add-arb-lemma` (the basis argument is replaced by a greedy walk through a duplicate-free set of factors; see the file header) |
| Lemma 4.5 | `zero-subset.lisp` | `zero-subset-path`, `zero-subset-lemma` (decomposition into basis tensors, A then B then C, with a lexicographic measure; parity argument for pair deletion) |
| Theorem 4.1 | `connectivity.lisp` | `connect-path`, `flip-graph-strongly-connected` |
| Sec. 5.1 `__match_any_sync` | `search-step.lisp` | `match-any-sync`, `match-any-sync-spec`, `match-any-sync-gives-flip-precondition` |
| Sec. 5.2 generalized flips (subset form used on the GPU) | `genflip.lisp` | `gen-flip`, `gen-flip-preserves-sum` (the displayed computation), `gen-flip-reduces-rank`, `gen-flip-in-scheme`, `gen-flip-reachable` (via Theorem 4.1) |
| Sec. 5.2 change-of-basis form `B G G^{-1} C` | `genflip-basis.lisp` | `change-of-basis-preserves-T2`, `change-of-basis-preserves-group-sum`, `pairwise-flip-as-change-of-basis` (the ordinary flip is `G = [[1,0],[1,1]]`) |
| Appendix A (rank-245 scheme) | `rank245-data.lisp` (decoded by `decode_scheme.py`), `rank245.lisp` | `rank245-is-a-scheme`, `rank245-terms-distinct`, `rank245-has-245-terms`; `top.lisp`: `rank245-reachable-from-naive` |
| Appendix B (Theorem B.1) | `optimal-genflip*.lisp` | see below |
| Appendix C (Algorithm 1) | `search-step.lisp` | `apply-step`, `step-ok-p`, `apply-step-preserves-schemep`, `reduce-step-lowers-rank`, `apply-steps-preserves-schemep`, `search-result-reachable-by-flips-and-pluses` |

### Appendix B

`rank(T_BC)` is taken as the tensor rank of the order-2 tensor
`T_BC = sum_i B_i (x) C_i`: `(has-decomp L L T k)` says `T` is a sum of at most
`k` simple tensors.

* `optimal-genflip.lisp`
  * Part 1: `genflip-survivors-decompose-T2`, `genflip-lower-bound`: for every
    invertible `G`, the survivors form a decomposition, so `survivors >= rank`.
  * Part 2: `trivial-kernel-implies-le`: a linear map `F_2^s -> F_2^L` with
    trivial kernel forces `s <= L` (counting: `all-bvs`).
  * Part 3: `echelon-decomp-is-shortest`: a decomposition whose `B` factors
    are in reduced echelon form and whose `C` factors have trivial kernel is
    at least as short as any decomposition of the same tensor.
* `optimal-genflip-elim.lisp`, `optimal-genflip-inv.lisp`: elementary pair
  flips preserve the tensor, commute with changes of basis, and a sequence of
  them started from `(I, I)` yields an invertible `G`
  (`T2-eq-identity-implies-rows-sum2-identity`).
* `optimal-genflip-phaseB.lisp`, `optimal-genflip-phaseB2.lisp`: Gauss-Jordan
  elimination on the `B` side (`elim-col`, `phaseB`) with the pivot invariant.
* `optimal-genflip-phaseC.lisp`, `optimal-genflip-select.lisp`,
  `optimal-genflip-final.lisp`: elimination of dependencies among the `C`
  factors of the live pairs (`dep-elim`, `phaseC`), selection of the live
  pairs, and `theorem-B1`.

The paper's construction chooses a basis adapted to `U = ker B` and
`L = W^perp`; the formalization instead performs the change of basis by
elementary flips (each is a generalized flip with `G = I + E_ij`), which is
what yields an explicit `G` for the upper bound.  The optimality argument
(`s >= rank`) is the paper's; the argument `rank >= s` is done with an
explicit echelon form and the counting lemma instead of dimension theory.

## What is not formalized

* The experimental content (Section 6, Figures 2-6) and the GPU
  implementation details (registers, lanes, slots, random streams, the
  probe-round parameter `k`).  Appendix C is modeled at the level of the
  effect of one step on the scheme held by a warp.
* The generalized flip in `search-step.lisp` is modeled for groups sharing
  the `A` factor (the paper's presentation); the `B`/`C` positions are
  symmetric.

## Status

All 24 books (7486 lines, 202 `defun`, 665 `defthm`) certify from a clean
directory with the fork's `saved_acl2` via `./cert.sh top.lisp` (about 40
minutes on a laptop; the slowest books are `zero-subset`, `optimal-genflip-final`,
`scheme`, and `optimal-genflip-phaseB2`).  There are
no `skip-proofs`, `defaxiom`, or trust tags anywhere in the development.
Every theorem named in the table above is proved; the paper-level results are

* `mmt-satisfies-definition`, `mmt-unique` (Definition 2.1),
* `flip-preserves-sum`, `plus-preserves-sum` (Definition 2.3),
* `span-lemma` (Lemma 4.2), `add-dup-lemma` (Lemma 4.3),
  `add-arb-lemma` (Lemma 4.4), `zero-subset-lemma` (Lemma 4.5),
* `flip-graph-strongly-connected` (Theorem 4.1),
* `gen-flip-preserves-sum`, `change-of-basis-preserves-T2` (Section 5.2),
* `rank245-is-a-scheme`, `rank245-reachable-from-naive` (Appendix A),
* `theorem-B1`, `theorem-B1-lower-bound` (Theorem B.1, parts (a)-(d)),
* `search-result-reachable-by-flips-and-pluses` (Appendix C).

Proof-engineering notes: ACL2 symbols are case-insensitive, so the paper's
`T`, `S`, `P`, `U`, `A/a` are renamed (`sch`, `PL`, `usum`, `ia ib ic`, ...);
`(sq n)` is kept disabled so that hypotheses like `(equal (len X) (sq n))` do
not destroy the shape of rewrite rules; large conjunctive theorems about the
elimination loops are split into one theorem per property.

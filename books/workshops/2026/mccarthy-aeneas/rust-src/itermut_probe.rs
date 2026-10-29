//@ skip
// Roadmap item 8: slice iterator extraction (iter / iter_mut / zip), the
// last structural de-sugar class in aes_fixslice_encrypt.rs.  (The skip
// directive keeps this out of the default runners: it needs charon's carved
// pipeline, not the runners' flags.  The generated book and its proofs ARE
// part of the certified suite: tests/acl2/itermut_probe{,-proofs}.lisp.)
//
// Pipeline (the mono carve-out, charon fork):
//   charon rustc --preset=aeneas --monomorphize --monomorphize-mut=except-types \
//     --remove-adt-clauses --lift-associated-types='*' \
//     --dest-file=itermut_probe.llbc -- --edition=2021 --crate-type=rlib ...
//   aeneas -backend acl2 -use-fuel -loops-to-rec itermut_probe.llbc
//
// Under plain --monomorphize, charon bakes region-erased borrow-carrying
// decls (Option<&'_ mut u32>, Iter<'_, u32>, ...) that Aeneas's decl-level
// region analysis rejects.  The carve-out keeps exactly those
// instantiations polymorphic (baking would erase unrecoverable regions), so
// Aeneas core translates all four shapes: IterMut::next comes back as the
// triple (elem option, advanced iter, next_back), loops thread a composed
// write-back continuation, iter_mut/zip return (iterator, backward) pairs.
//
// The ACL2 printer then models the opaque iterators first-order --
// Iter/IterMut as {lst, pos} defprods, Zip as {a, b} -- synthesizes the
// ctors/next methods against those models, and DEFUNCTIONALIZES the loop
// back-continuations: the arrow-typed loop formal becomes a list of pending
// write values (identity closure ~> nil, the wrap lambda ~> (cons v back)),
// applied by the emitted -apply-back/-wb-some companions on the decrement
// model (after k nexts the cursor is at k; applying the pending writes
// latest-first lands each in the slot its next read).
//
// Shapes:
//   p1_iter_sum    : shared iteration      for x in xs.iter() { .. }
//   p2_itermut_inc : mutable iteration     for x in xs.iter_mut() { *x = .. }
//   p3_zip_xor     : the add_round_key shape: a.iter_mut().zip(b)
//   p4_ark_exact   : verbatim upstream add_round_key text
//   driver         : known-answer composition of all four (returns 44)

type State = [u32; 8];

fn p1_iter_sum(xs: &[u32]) -> u32 {
    let mut s: u32 = 0;
    for x in xs.iter() {
        s = s.wrapping_add(*x);
    }
    s
}

fn p2_itermut_inc(xs: &mut [u32]) {
    for x in xs.iter_mut() {
        *x = x.wrapping_add(1);
    }
}

fn p3_zip_xor(a: &mut [u32], b: &[u32]) {
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

fn p4_ark_exact(state: &mut State, rkey: &[u32]) {
    debug_assert_eq!(rkey.len(), 8);
    for (a, b) in state.iter_mut().zip(rkey) {
        *a ^= b;
    }
}

fn driver() -> u32 {
    let mut st: State = [1, 2, 3, 4, 5, 6, 7, 8];
    let rk: [u32; 8] = [8, 7, 6, 5, 4, 3, 2, 1];
    p2_itermut_inc(&mut st); // st = [2,3,4,5,6,7,8,9]
    p3_zip_xor(&mut st, &rk); // xor with rk
    p4_ark_exact(&mut st, &rk); // xor again: cancels
    p1_iter_sum(&st) // 2+3+4+5+6+7+8+9 = 44
}

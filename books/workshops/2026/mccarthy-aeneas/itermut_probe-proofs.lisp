; Known-answer + symbolic regression for slice iterators (de-vendoring
; roadmap item 8): shared iteration (iter), mutable iteration (iter_mut),
; and the add_round_key shape (iter_mut().zip(shared)), including the
; verbatim upstream add_round_key text (p4).
;
; The Rust source is tests/src/itermut_probe.rs, compiled with charon's
; carved pipeline (--preset=aeneas --monomorphize
; --monomorphize-mut=except-types --remove-adt-clauses
; --lift-associated-types='*' -- --edition=2021) and extracted with
; -backend acl2 -use-fuel -loops-to-rec.  Iter/IterMut/Zip stay polymorphic
; (their regions are unrecoverable once baked) and arrive as opaque decls;
; the printer models them as {lst, pos} defprods (Zip as {a, b}) and
; defunctionalizes the loops' composed write-back continuations into lists
; of pending values, applied by the -apply-back/-wb-some companions on the
; decrement model: after k successful nexts the cursor sits at k, and the
; composed continuation applies the pending writes latest-first, so each
; lands in the slot its next read.
;
; The symbolic theorems below are the point: with concrete list structure
; but FREE elements, the loops unroll by rewriting (the :free fuel :expand
; hint re-fires on every exposed fuel) and the final state must come out
; elementwise -- any slot transposition or off-by-one in the write-back
; model would leave an unprovable mismatch.
(in-package "ACL2")
(include-book "itermut_probe")

;; ---- known answers (everything computes; fuel 100 covers len-8 loops) ----
;; p2: increment each element in place through IterMut.
(defthm p2-known-answer
  (equal (itermut-probe-p2-itermut-inc 100 (list 1 2 3 4 5 6 7 8))
         (ok (list 2 3 4 5 6 7 8 9))))
;; p3: xor the &mut side with the shared side pairwise.
(defthm p3-known-answer
  (equal (itermut-probe-p3-zip-xor 100 (list 2 3 4 5 6 7 8 9)
                                       (list 8 7 6 5 4 3 2 1))
         (ok (list 10 4 2 0 2 4 10 8))))
;; p4 (verbatim upstream add_round_key): xor again with the same key
;; cancels p3.
(defthm p4-known-answer
  (equal (itermut-probe-p4-ark-exact 100 (list 10 4 2 0 2 4 10 8)
                                         (list 8 7 6 5 4 3 2 1))
         (ok (list 2 3 4 5 6 7 8 9))))
;; p1: shared-iterator sum of the final state.
(defthm p1-known-answer
  (equal (itermut-probe-p1-iter-sum 100 (list 2 3 4 5 6 7 8 9)) (ok 44)))
;; the composition: inc, xor, xor-again (cancels), sum = 2+3+...+9.
(defthm driver-known-answer
  (equal (itermut-probe-driver 100) (ok 44)))

;; ---- symbolic: elementwise characterization with free elements ----
(defthm p2-symbolic-elementwise
  (equal (result-ok->val
          (itermut-probe-p2-itermut-inc 100 (list a b c d e f g h)))
         (list (result-ok->val (u32-wrapping-add a 1))
               (result-ok->val (u32-wrapping-add b 1))
               (result-ok->val (u32-wrapping-add c 1))
               (result-ok->val (u32-wrapping-add d 1))
               (result-ok->val (u32-wrapping-add e 1))
               (result-ok->val (u32-wrapping-add f 1))
               (result-ok->val (u32-wrapping-add g 1))
               (result-ok->val (u32-wrapping-add h 1))))
  :hints (("Goal"
           :expand ((:free (n it bk)
                     (itermut-probe-p2-itermut-inc-loop0 n it bk))))))

(defthm p3-symbolic-elementwise
  (equal (result-ok->val
          (itermut-probe-p3-zip-xor 100 (list a b c d e f g h)
                                        (list p q r s u v w x)))
         (list (u32-xor a p) (u32-xor b q) (u32-xor c r) (u32-xor d s)
               (u32-xor e u) (u32-xor f v) (u32-xor g w) (u32-xor h x)))
  :hints (("Goal"
           :expand ((:free (n it bk)
                     (itermut-probe-p3-zip-xor-loop0 n it bk))))))

;; p4 is the same loop shape on an 8-array state (upstream text verbatim).
(defthm p4-symbolic-elementwise
  (equal (result-ok->val
          (itermut-probe-p4-ark-exact 100 (list a b c d e f g h)
                                          (list p q r s u v w x)))
         (list (u32-xor a p) (u32-xor b q) (u32-xor c r) (u32-xor d s)
               (u32-xor e u) (u32-xor f v) (u32-xor g w) (u32-xor h x)))
  :hints (("Goal"
           :expand ((:free (n it bk)
                     (itermut-probe-p4-ark-exact-loop0 n it bk))))))

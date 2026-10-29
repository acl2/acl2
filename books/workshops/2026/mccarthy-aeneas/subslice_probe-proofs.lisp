; Known-answer + symbolic regression for subslice borrows (de-vendoring
; roadmap item 7): shared window reads (Index<Range>), mutable window borrows
; through function calls (IndexMut<Range> -- forward read, callee on the
; window, vec-update-range write-back), and the mutable array-to-slice
; coercion (identity on the list model).
(in-package "ACL2")
(include-book "subslice_probe")
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;; ---- known answers (everything computes) ----
;; go: window [2,6) of (0..7) is (2 3 4 5); bump adds 1 at 0 and 2 at 3;
;; the write-back splices (3 3 4 7) back.
(defthm go-known-answer
  (equal (subslice-probe-go (list 0 1 2 3 4 5 6 7))
         (ok (list 0 1 3 3 4 7 6 7))))
(defthm rd-known-answer
  (equal (subslice-probe-rd (list 0 1 2 3 4 5 6 7)) (ok 3)))
(defthm len-of-known-answer
  (equal (subslice-probe-len-of (list 0 1 2 3 4 5 6 7)) (ok 4)))
(defthm coerce-known-answer
  (equal (subslice-probe-coerce (list 0 1 2 3 4 5 6 7))
         (ok (list 7 1 2 3 4 5 6 7))))

;; ---- symbolic: the borrow machinery composes on any length-8 array ----
(defthm rk-of-go
  (implies (and (true-listp a) (equal (len a) 8))
           (equal (result-kind (subslice-probe-go a)) :ok))
  :hints (("Goal" :in-theory (e/d (subslice-probe-go subslice-probe-bump)
                                  (vec-index-range vec-update-range
                                   nth update-nth)))))
(defthm len-of-go-val
  (implies (and (true-listp a) (equal (len a) 8))
           (equal (len (result-ok->val (subslice-probe-go a))) 8))
  :hints (("Goal" :in-theory (e/d (subslice-probe-go subslice-probe-bump)
                                  (vec-index-range vec-update-range
                                   nth update-nth)))))

;; StepBy<Range<usize>>: (0..8).step_by(4) visits 0 and 4 (the key
;; schedule's (8..72).step_by(32) fold shape).
(defthm stepby-known-answer
  (equal (subslice-probe-stepby 100 (list 1 2 3 4 5 6 7 8)) (ok 6)))

; Correctness of extracted `for i in 0..n` loops (range_for.lisp). Shows the
; new iterator support is not just admissible but verifiable: the extracted
; range loop, which threads a Range value as state and calls the synthesized
; Range::next, equals a simple recursive fold spec for all inputs.

(in-package "ACL2")
(include-book "range_for")
(local (include-book "arithmetic-5/top" :dir :system))

;; Long generated names, abbreviated locally.
(defmacro rnext (r)
  `(core-iter-range-impl-core-iter-traits-iterator-iterator-for-core-ops-range-range-usize-next-usize-
    ,r))
(defmacro rng (i e) `(core-ops-range-range-usize- ,i ,e))

;; ---- execution vectors: the extracted loops run correctly ----
(assert-event (equal (range-for-sum-to 20 10) (ok 45)))     ; 0+1+...+9
(assert-event (equal (range-for-sum-to 2 1) (ok 0)))
(assert-event (equal (range-for-add-rk 9 (list 1 2 3 4 5 6 7 8)
                                         (list 1 1 1 1 1 1 1 1))
                     (ok (list 0 3 2 5 4 7 6 9))))

;; ---- symbolic correctness of sum_to ----

;; What the synthesized Range::next does on a concrete range.
(defthm rnext-on-range
  (equal (rnext (rng i e))
         (if (< i e)
             (ok (cons (core-option-option-usize--some i) (rng (+ i 1) e)))
           (ok (cons (core-option-option-usize--none) (rng i e))))))

;; Fold spec: wrapping-sum of the indices [i, e), threaded through s.
(defun sum-spec (i e s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (sum-spec (+ i 1) e (mod (+ s i) (expt 2 32)))
    s))

;; Step the extracted loop once on a concrete range. The recursive step (i<e)
;; exposes the recursion on the NEXT range (rng (i+1) e) -- which the loop's
;; own abstract-iterator induction does not -- and needs i<2^32 so `i as u32`
;; succeeds. The base step (i>=e) needs no bound.
(defthm loop0-step-rec
  (implies (and (natp i) (natp s) (< i e) (< i (expt 2 32)) (<= s *u32-max*)
                (not (zp fuel)))
           (equal (range-for-sum-to-loop0 fuel (rng i e) s)
                  (range-for-sum-to-loop0 (1- fuel) (rng (+ i 1) e)
                                          (mod (+ s i) (expt 2 32)))))
  :hints (("Goal" :expand ((range-for-sum-to-loop0 fuel (rng i e) s))
                  :in-theory (enable rnext-on-range u32-cast u32-wrapping-add))))

(defthm loop0-step-base
  (implies (and (<= e i) (not (zp fuel)))
           (equal (range-for-sum-to-loop0 fuel (rng i e) s) (ok s)))
  :hints (("Goal" :expand ((range-for-sum-to-loop0 fuel (rng i e) s))
                  :in-theory (enable rnext-on-range))))

;; Induction scheme matching the stepped loop (fuel down, index up).
(defun sum-ind (fuel i e s)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (list i e s)
    (if (< i e)
        (sum-ind (1- fuel) (+ i 1) e (mod (+ s i) (expt 2 32)))
      (list i e s))))

;; The extracted loop over the range [i,e) equals the fold spec, given enough
;; fuel and a range bounded so each `i as u32` cast succeeds (i < 2^32). The
;; two step lemmas drive it; keep the result accessors closed so the equality
;; stays atomic (the constructor-injectivity rule + IH close each case).
(defthm sum-to-loop0-is-spec
  (implies (and (natp i) (natp e) (natp s) (<= s *u32-max*)
                (<= e (expt 2 32)) (<= i e)
                (< (- e i) (nfix fuel)))
           (equal (range-for-sum-to-loop0 fuel (rng i e) s)
                  (ok (sum-spec i e s))))
  :hints (("Goal" :induct (sum-ind fuel i e s)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (sum-spec)
                                  (range-for-sum-to-loop0 rnext-on-range
                                   (:executable-counterpart
                                    core-ops-range-range-usize-))))))

;; Top level: sum_to n == fold over [0, n).
(defthm sum-to-is-spec
  (implies (and (natp e) (<= e (expt 2 32)) (< e (nfix fuel)))
           (equal (range-for-sum-to fuel e) (ok (sum-spec 0 e 0))))
  :hints (("Goal" :use ((:instance sum-to-loop0-is-spec (i 0) (s 0)))
                  :in-theory (disable sum-to-loop0-is-spec
                                      range-for-sum-to-loop0))))

; Proofs about COMPILER-GENERATED code: the books gen-demo.lisp,
; gen-loops.lisp and gen-no_nested_borrows.lisp were produced end-to-end by
;   charon (Rust -> LLBC)  -->  aeneas -backend acl2 -use-fuel -loops-to-rec
; and certified unmodified.  This book proves the Stage-0 specification
; theorems AGAINST THAT OUTPUT -- the Stage-2 exit criterion of the plan
; ("equivalence proofs certify against generated code").

(in-package "ACL2")

(include-book "demo")
(include-book "loops")
(include-book "no_nested_borrows")
(include-book "arithmetic/top-with-meta" :dir :system)

;; ---------------------------------------------------------------------
;; demo::mul2_add1  (generated: demo-mul2-add1)
;; ---------------------------------------------------------------------

(defthm gen-mul2-add1-ok
  (implies (and (u32p x) (<= (+ (* 2 x) 1) *u32-max*))
           (equal (demo-mul2-add1 x) (ok (+ (* 2 x) 1)))))

(defthm gen-mul2-add1-overflow
  (implies (and (u32p x) (> (+ (* 2 x) 1) *u32-max*))
           (equal (demo-mul2-add1 x) (result-fail (err-failure)))))

;; ---------------------------------------------------------------------
;; demo::list_nth == nth, over the generated demo-clist type
;; ---------------------------------------------------------------------

(defun gclist->list (l)
  (declare (xargs :measure (demo-clist-count l)))
  (demo-clist-case l
    :ccons (cons (demo-clist-ccons->f0 l) (gclist->list (demo-clist-ccons->f1 l)))
    :cnil nil))

(defthm gclist->list-when-ccons
  (implies (equal (demo-clist-kind l) :ccons)
           (equal (gclist->list l)
                  (cons (demo-clist-ccons->f0 l)
                        (gclist->list (demo-clist-ccons->f1 l)))))
  :hints (("Goal" :expand ((gclist->list l)))))

(defthm gclist->list-when-not-ccons
  (implies (not (equal (demo-clist-kind l) :ccons))
           (equal (gclist->list l) nil))
  :hints (("Goal" :expand ((gclist->list l)))))

(defthm gen-list-nth-correct
  (implies (and (u32p i)
                (< i (len (gclist->list l)))
                (< (len (gclist->list l)) (nfix n)))
           (equal (demo-list-nth n l i)
                  (ok (nth i (gclist->list l)))))
  :hints (("Goal" :induct (demo-list-nth n l i))))

;; ---------------------------------------------------------------------
;; demo::i32_id is the identity on non-negative i32
;; ---------------------------------------------------------------------

(defthm gen-i32-id-correct
  (implies (and (i32p i) (<= 0 i) (< i (nfix n)))
           (equal (demo-i32-id n i) (ok i)))
  :hints (("Goal" :induct (demo-i32-id n i))))

;; ---------------------------------------------------------------------
;; loops::sum == 2 * (0 + 1 + ... + max-1)   (the Rust source doubles the
;; accumulator on return), proved via the classic loop invariant on the
;; generated loops-sum-loop0.
;; ---------------------------------------------------------------------

(defun gsum-spec (i max)
  (declare (xargs :measure (nfix (- max i))))
  (if (and (natp i) (natp max) (< i max))
      (+ i (gsum-spec (+ 1 i) max))
    0))

(defthm natp-gsum-spec
  (natp (gsum-spec i max))
  :rule-classes :type-prescription)

(defthm gsum-spec-lower-bound
  (implies (and (natp i) (natp max) (< i max))
           (<= i (gsum-spec i max)))
  :rule-classes :linear)

(defthm gen-sum-loop-correct
  (implies (and (u32p max) (u32p i) (u32p s)
                (<= i max)
                (< (- max i) (nfix n))
                (<= (+ s (gsum-spec i max)) *u32-max*))
           (equal (loops-sum-loop0 n max i s)
                  (ok (+ s (gsum-spec i max)))))
  :hints (("Goal" :induct (loops-sum-loop0 n max i s))))

(defthm gen-sum-correct
  (implies (and (u32p max)
                (< max (nfix n))
                (<= (* 2 (gsum-spec 0 max)) *u32-max*))
           (equal (loops-sum n max)
                  (ok (* 2 (gsum-spec 0 max))))))

;; ---------------------------------------------------------------------
;; no_nested_borrows::get_max == max
;; ---------------------------------------------------------------------

(defthm gen-get-max-correct
  (implies (and (u32p x) (u32p y))
           (equal (no-nested-borrows-get-max x y) (ok (max x y)))))

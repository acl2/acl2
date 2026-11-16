; Sum preservation: a valid move, and hence a valid path, preserves the
; scheme sum.
;
; Main results:
;  - scheme-sum-of-apply-move / scheme-sum-of-apply-moves: a valid move, and
;    hence a valid path, preserves the scheme sum.
;  - sum-preservation-corollary: a scheme that sums to a fixed tensor tt
;    still sums to tt after any valid path; tt is never constrained.

(in-package "ACL2")

(include-book "tensor")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; Length-based cancellation, local proof machinery for the move-level sum
;; argument: the dimensioned cancel rules cannot fire there because their
;; dimension is a free variable, while this form relieves its hypotheses by
;; computing lengths.
(local
 (defruled bit-list-add-cancel-first
   (implies (and (bit-list-p y)
                 (<= (len y) (len x)))
            (equal (bit-list-add x (bit-list-add x y))
                   y))
   :induct (cdr-cdr-induct x y)
   :enable (bit-list-add)))

;; Not a duplicate of any library rule: the corresponding goal about a bare
;; list is proved by opening len and true-listp, which does not happen for
;; subterms like (cddr s) in context.  As an enabled rule it also lets the
;; simplifier collapse partial summand remakes back onto their source terms,
;; which the move proofs below depend on.
(local
 (defrule list-of-car-when-len-1
   (implies (and (true-listp x)
                 (equal (len x) 1))
            (equal (list (car x)) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled scheme-sum-of-apply-move
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (move-validp move sch)
                (natp n))
           (equal (scheme-sum (apply-move move sch n) n)
                  (scheme-sum sch n)))
  :do-not-induct t
  :use ((:instance summandp-when-in-summand-listp (s (move-s1 move)))
        (:instance summandp-when-in-summand-listp (s (move-s2 move))))
  :enable (apply-move in-when-occs-geq-2 in-of-delete
           scheme-sum-of-insert scheme-sum-of-delete
           tensor-of-add-a tensor-of-add-b tensor-of-add-c
           tensor-when-zero-a tensor-when-zero-b tensor-when-zero-c
           bit-list-add-self
           bit-list-add-commutative bit-list-add-commutative-2
           bit-list-add-associative bit-list-add-cancel-first)
  :disable (tensor))

(defruled scheme-sum-of-apply-moves
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (path-validp moves sch n)
                (natp n))
           (equal (scheme-sum (apply-moves moves sch n) n)
                  (scheme-sum sch n)))
  :induct (apply-moves moves sch n)
  :enable (apply-moves scheme-sum-of-apply-move))

(defrule sum-preservation-corollary
  (implies (and (schemep sch n)
                (path-validp moves sch n)
                (natp n)
                (equal (scheme-sum sch n) tt))
           (equal (scheme-sum (apply-moves moves sch n) n)
                  tt))
  :enable (scheme-sum-of-apply-moves))

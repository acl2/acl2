; The zero-subset lemma of the companion paper (lemma:zero-subset).
;
; If a correct scheme sch for n x n matrix multiplication over F2 (n >= 2)
; contains a sub-multiset r whose summand tensors sum to zero, then there
; is a valid flip/plus path from sch to sch with r removed (theorem
; zero-subset): three decomposition sweeps (positions 0, 1, 2) reduce r to
; a zero-summing multiset of unit summands, whose members each occur an
; even number of times and are deleted in identical pairs.  The machinery
; lives in zero-support.lisp.  Validated by execution at n = 2 (the two
; assert-event forms at the end).

(in-package "ACL2")

(include-book "zero-support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 5: lemma:zero-subset
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The full path: three decomposition sweeps (positions 0, 1, 2), then
;;; pair deletion of the resulting zero-summing unit-summand multiset.

(define zero-subset-path ((sch obag::bagp) (r mat-triple-listp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (enable mat-triple-listp-of-insert-list
                                              mat-triple-listp-of-delete-list))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (enable mat-triple-listp-of-insert-list
                                    mat-triple-listp-of-delete-list)))
  (b* ((base (delete-list r sch))
       (l1 (expand-pos-list r 0 n))
       (sch1 (insert-list l1 base))
       (l2 (expand-pos-list l1 1 n))
       (sch2 (insert-list l2 base))
       (l3 (expand-pos-list l2 2 n))
       (sch3 (insert-list l3 base)))
    (append (decompose-list-pos-path sch r 0 n)
            (append (decompose-list-pos-path sch1 l1 1 n)
                    (append (decompose-list-pos-path sch2 l2 2 n)
                            (delete-pairs-path sch3 l3 n))))))

;;; The image of r after the three sweeps is a unit-summand list.

(defruled unit-summand-listp-of-triple-expand
  (implies (and (summand-listp r n)
                (natp n))
           (unit-summand-listp
            (expand-pos-list (expand-pos-list (expand-pos-list r 0 n) 1 n) 2 n)
            n))
  :do-not-induct t
  :use ((:instance pos-unit-listp-of-expand-pos-list (l r) (p 0))
        (:instance pos-unit-listp-of-expand-pos-list-preserve
                   (l (expand-pos-list r 0 n)) (q 0) (p 1))
        (:instance pos-unit-listp-of-expand-pos-list
                   (l (expand-pos-list r 0 n)) (p 1))
        (:instance pos-unit-listp-of-expand-pos-list-preserve
                   (l (expand-pos-list (expand-pos-list r 0 n) 1 n))
                   (q 0) (p 2))
        (:instance pos-unit-listp-of-expand-pos-list-preserve
                   (l (expand-pos-list (expand-pos-list r 0 n) 1 n))
                   (q 1) (p 2))
        (:instance pos-unit-listp-of-expand-pos-list
                   (l (expand-pos-list (expand-pos-list r 0 n) 1 n)) (p 2))
        (:instance unit-summand-listp-when-pos-units
                   (l (expand-pos-list
                       (expand-pos-list (expand-pos-list r 0 n) 1 n) 2 n))))
  :enable (summand-listp-of-expand-pos-list)
  :disable (unit-summand-listp expand-pos-list summandp bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; lemma:zero-subset

(defrule zero-subset
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (true-listp r)
                (list-in-bagp r sch)
                (equal (scheme-sum r n) (bit-listn0 (* n n n n n n))))
           (b* ((path (zero-subset-path sch r n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (delete-list r sch))
                  (correct-schemep (delete-list r sch) n))))
  :do-not-induct t
  :use ((:instance summand-listp-when-list-in-bagp (l r) (b sch))
        (:instance decompose-list-pos-invariant (l r) (p 0))
        (:instance decompose-list-pos-invariant
                   (sch (insert-list (expand-pos-list r 0 n)
                                     (delete-list r sch)))
                   (l (expand-pos-list r 0 n)) (p 1))
        (:instance decompose-list-pos-invariant
                   (sch (insert-list (expand-pos-list
                                      (expand-pos-list r 0 n) 1 n)
                                     (delete-list r sch)))
                   (l (expand-pos-list (expand-pos-list r 0 n) 1 n)) (p 2))
        (:instance delete-pairs-invariant
                   (sch (insert-list
                         (expand-pos-list
                          (expand-pos-list (expand-pos-list r 0 n) 1 n) 2 n)
                         (delete-list r sch)))
                   (l (expand-pos-list
                       (expand-pos-list (expand-pos-list r 0 n) 1 n) 2 n)))
        (:instance unit-summand-listp-of-triple-expand)
        (:instance scheme-sum-of-delete-list (l r) (b sch)))
  :enable (zero-subset-path correct-schemep
           list-in-bagp-of-insert-list-self
           delete-list-of-insert-list-same
           scheme-sum-of-expand-pos-list
           summand-listp-of-expand-pos-list
           scheme-sum-of-insert-list)
  :disable (decompose-list-pos-invariant delete-pairs-invariant
            decompose-list-pos-path delete-pairs-path
            expand-pos-list insert-list delete-list list-in-bagp
            scheme-sum mm-tensor summandp bit-matp unit-summand-listp
            apply-move move-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable validation of zero-subset-path at n = 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; r = two identical copies of a grafted non-unit summand.

(assert-event
 (let* ((x '((1 1) (0 1))) (y '((0 1) (1 1))) (z '((1 0) (1 1)))
        (s (summand x y z))
        (path0 (add-arbitrary-path *arb-std2* x y z 2))
        (sch (apply-moves path0 *arb-std2* 2))
        (r (list s s)))
   (and (correct-schemep sch 2)
        (list-in-bagp r sch)
        (equal (scheme-sum r 2) (bit-listn0 64))
        (let* ((zp (zero-subset-path sch r 2))
               (res (apply-moves zp sch 2)))
          (and (path-validp zp sch 2)
               (equal res (delete-list r sch))
               (equal res *arb-std2*)
               (correct-schemep res 2))))))

;;; r with overlapping unit expansions: s3 = s4 + s5 in the A factor with
;;; shared B and C, so r = (s3 s4 s5) sums to zero.

(assert-event
 (let* ((y '((0 1) (1 1))) (z '((1 0) (1 1)))
        (x4 '((1 1) (0 0))) (x5 '((0 0) (1 1)))
        (x3 (bit-mat-add x4 x5))
        (s3 (summand x3 y z))
        (s4 (summand x4 y z))
        (s5 (summand x5 y z))
        (p3 (add-arbitrary-path *arb-std2* x3 y z 2))
        (sch3 (apply-moves p3 *arb-std2* 2))
        (p4 (add-arbitrary-path sch3 x4 y z 2))
        (sch4 (apply-moves p4 sch3 2))
        (p5 (add-arbitrary-path sch4 x5 y z 2))
        (sch (apply-moves p5 sch4 2))
        (r (list s3 s4 s5)))
   (and (correct-schemep sch 2)
        (list-in-bagp r sch)
        (equal (scheme-sum r 2) (bit-listn0 64))
        (let* ((zp (zero-subset-path sch r 2))
               (res (apply-moves zp sch 2)))
          (and (path-validp zp sch 2)
               (equal res (delete-list r sch))
               (correct-schemep res 2))))))

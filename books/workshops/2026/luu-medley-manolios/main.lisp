; The flip-plus connectivity theorem of the companion paper (thm:main).
;
; For two correct schemes sch and sch2 (n >= 2): graft two copies of every
; summand of sch2 onto sch by lem:add-arbitrary (graft-path), then delete
; the zero-summing sub-multiset (append sch sch2) by lemma:zero-subset;
; the result is exactly sch2 (theorem flip-plus-connectivity).  Validated
; by execution at n = 2 in both directions (the assert-event at the end).

(in-package "ACL2")

(include-book "zero-subset")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 6: thm:main (flip-plus connectivity)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; deleting the head of an ordered bag is taking its cdr

(defruled delete-of-head
  (implies (and (obag::bagp b) (consp b))
           (equal (obag::delete (car b) b) (cdr b)))
  :enable (obag::delete obag::bagp obag::head obag::tail
           obag::emptyp obag::bfix))

;;; every bag is a sub-multiset of itself

(defruled list-in-bagp-self
  (implies (obag::bagp b)
           (list-in-bagp b b))
  :induct (cdr-induct b)
  :enable (list-in-bagp delete-of-head
           obag::in obag::bagp obag::head obag::emptyp obag::bfix))

;;; deleting a bag from itself empties it

(defruled delete-list-self
  (implies (obag::bagp b)
           (equal (delete-list b b) nil))
  :induct (cdr-induct b)
  :enable (delete-list delete-of-head obag::bagp))

;;; sub-multiset-ness over append

(defruled list-in-bagp-of-append
  (implies (obag::bagp c)
           (equal (list-in-bagp (append a b) c)
                  (and (list-in-bagp a c)
                       (list-in-bagp b (delete-list a c)))))
  :induct (delete-list a c)
  :enable (list-in-bagp delete-list))

;;; adding two copies of a summand preserves the scheme sum (char. 2)

(defruled scheme-sum-of-double-insert
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (summandp s n)
                (natp n))
           (equal (scheme-sum (obag::insert s (obag::insert s sch)) n)
                  (scheme-sum sch n)))
  :use ((:instance bit-list-add-cancel-1
                   (x (scheme-sum sch n))
                   (y (summand-tensor s))
                   (n (* n n n n n n))))
  :enable (scheme-sum-of-insert)
  :disable (summand-tensor tensor summandp scheme-sum bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the graft leg

(define graft-path ((sch obag::bagp) (l mat-triple-listp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :induct (graft-path sch l n)
                           :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                                      (enable mat-triple-head-lemmas)))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (enable mat-triple-head-lemmas))))
  (if (atom l)
      nil
    (append (add-arbitrary-path sch (car (car l)) (cadr (car l))
                                (caddr (car l)) n)
            (graft-path (obag::insert (car l) (obag::insert (car l) sch))
                        (cdr l) n))))

(defrule graft-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (summand-listp l n))
           (b* ((path (graft-path sch l n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (insert-list l (insert-list l sch)))
                  (correct-schemep res n))))
  :induct (graft-path sch l n)
  :enable (graft-path apply-moves insert-list
           insert-list-of-insert
           list-3-reconstruct
           correct-schemep
           scheme-sum-of-double-insert)
  :disable (apply-move move-validp mm-tensor scheme-sum tensor
            summand-tensor bit-matp
            add-arbitrary-path)
  :hints (("Subgoal *1/2" :use ((:instance summandp-when-in-summand-listp
                                           (s (car l)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 6b: assembly of thm:main
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Inserting the elements of an ordered bag into the empty bag rebuilds it.

(defruled insert-list-of-self-nil
  (implies (obag::bagp b)
           (equal (insert-list b nil) b))
  :induct (cdr-induct b)
  :enable (insert-list obag::bagp obag::insert obag::emptyp
           obag::head obag::tail obag::bfix))

(defruled true-listp-of-append-2
  (implies (true-listp b)
           (true-listp (append a b)))
  :induct (cdr-induct a))

;;; The connectivity path: graft two copies of every summand of the target
;;; scheme, then delete the zero-summing sub-multiset (append sch sch2).

(define main-path ((sch obag::bagp) (sch2 obag::bagp) (n natp))
  :guard (and (mat-triple-listp sch) (mat-triple-listp sch2))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (enable mat-triple-listp-of-insert-list
                                              mat-triple-listp-of-append))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (enable mat-triple-listp-of-insert-list)))
  (append (graft-path sch sch2 n)
          (zero-subset-path (insert-list sch2 (insert-list sch2 sch))
                            (append sch sch2)
                            n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; thm:main

(defrule flip-plus-connectivity
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (b* ((path (main-path sch sch2 n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res sch2))))
  :do-not-induct t
  :use ((:instance graft-invariant (l sch2))
        (:instance zero-subset
                   (sch (insert-list sch2 (insert-list sch2 sch)))
                   (r (append sch sch2)))
        (:instance bit-list-add-same
                   (x (mm-tensor n))
                   (n (* n n n n n n)))
        (:instance scheme-sum-of-append
                   (a sch) (b sch2))
        (:instance list-in-bagp-of-append
                   (a sch) (b sch2)
                   (c (insert-list sch2 (insert-list sch2 sch))))
        (:instance true-listp-when-summand-listp (x sch2))
        (:instance true-listp-of-append-2 (a sch) (b sch2)))
  :enable (main-path correct-schemep
           list-in-bagp-self
           list-in-bagp-of-insert-list
           list-in-bagp-of-insert-list-self
           delete-list-of-insert-list
           delete-list-of-insert-list-same
           delete-list-of-append
           delete-list-self
           insert-list-of-self-nil)
  :disable (graft-invariant zero-subset
            graft-path zero-subset-path
            expand-pos-list insert-list delete-list list-in-bagp
            scheme-sum mm-tensor summandp bit-matp unit-summand-listp
            apply-move move-validp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable validation of main-path at n = 2: connect the standard
;;; rank-8 scheme and a rank-10 scheme in both directions.

(assert-event
 (let* ((x '((1 1) (0 1))) (y '((0 1) (1 1))) (z '((1 0) (1 1)))
        (p0 (add-arbitrary-path *arb-std2* x y z 2))
        (schb (apply-moves p0 *arb-std2* 2))
        (scha *arb-std2*))
   (and (correct-schemep scha 2)
        (correct-schemep schb 2)
        (let* ((p1 (main-path scha schb 2))
               (r1 (apply-moves p1 scha 2))
               (p2 (main-path schb scha 2))
               (r2 (apply-moves p2 schb 2)))
          (and (path-validp p1 scha 2)
               (equal r1 schb)
               (path-validp p2 schb 2)
               (equal r2 scha))))))

; Support for the zero-subset lemma of the companion paper
; (lemma:zero-subset, assembled in zero-subset.lisp).
;
; Contents:
;  - Stage 0: bag-list infrastructure (insert-list / delete-list /
;    list-in-bagp and their algebra).
;  - Stage 1: the single replacement step (replace-step): from sch plus two
;    copies of s[p := u] (as produced by add-arbitrary), a flip against s
;    replaces s by s[p := u] and s[p := s_p + u].
;  - Stage 2/2b: decomposing one position of one summand into unit matrices
;    (decompose-pos-path with the decompose-pos-invariant), recursion on
;    count-ones-mat via units-of / first-one-row / first-one-col-mat from
;    gf2span.
;  - Stage 3/3b: sweeping one position over a summand list
;    (decompose-list-pos-path, expand-pos-list) with typing and sum lemmas.
;  - Stage 4: deleting a zero-summing unit-summand sub-multiset in
;    identical pairs (delete-pairs-path with delete-pairs-invariant), using
;    the parity theorem even-count-occurrences-when-zero-scheme-sum
;    (parity.lisp) and rem:delete-identical-pair (paths.lisp).
;
; All path constructions were validated by execution at n = 2 before
; proving (resume-notes/zero-probe1.lsp).

(in-package "ACL2")

(include-book "add-arbitrary")
(include-book "parity")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 0: bag-list infrastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Insert every summand of a list into a bag (no zero-dropping: the lists
;;; inserted here are lists of well-formed nonzero summands).

(define insert-list ((l mat-triple-listp) (b obag::bagp))
  :returns (b1 obag::bagp :hyp (obag::bagp b))
  (if (atom l)
      b
    (obag::insert (car l) (insert-list (cdr l) b)))
  ///
  (defrule summand-listp-of-insert-list
    (implies (and (obag::bagp b)
                  (summand-listp b n)
                  (summand-listp l n))
             (summand-listp (insert-list l b) n))
    :induct (insert-list l b)
    :disable (summandp))
  ;; Structural mirror, for the guard proofs of the path builders below.
  (defruled mat-triple-listp-of-insert-list
    (implies (and (obag::bagp b)
                  (mat-triple-listp b)
                  (mat-triple-listp l))
             (mat-triple-listp (insert-list l b)))
    :induct (insert-list l b)
    :enable (mat-triple-listp-of-insert))
  (defruled insert-list-of-insert
    (implies (obag::bagp b)
             (equal (insert-list l (obag::insert x b))
                    (obag::insert x (insert-list l b))))
    :induct (insert-list l b)))

;;; Delete every summand of a list from a bag (one occurrence each).

(define delete-list ((l mat-triple-listp) (b obag::bagp))
  :returns (b1 obag::bagp :hyp (obag::bagp b))
  (if (atom l)
      b
    (delete-list (cdr l) (obag::delete (car l) b)))
  ///
  (defrule summand-listp-of-delete-list
    (implies (and (obag::bagp b)
                  (summand-listp b n))
             (summand-listp (delete-list l b) n))
    :induct (delete-list l b)
    :disable (summandp))
  ;; Structural mirror, for the guard proofs of the path builders below.
  (defruled mat-triple-listp-of-delete-list
    (implies (and (obag::bagp b)
                  (mat-triple-listp b))
             (mat-triple-listp (delete-list l b)))
    :induct (delete-list l b)
    :enable (mat-triple-listp-of-delete)))

;;; l is a sub-multiset of the bag b: each element is present, with
;;; multiplicity (the recursion deletes as it goes).

(define list-in-bagp ((l mat-triple-listp) (b obag::bagp))
  :returns (yes/no booleanp)
  (if (atom l)
      t
    (and (obag::in (car l) b)
         (list-in-bagp (cdr l) (obag::delete (car l) b))))
  ///
  (defruled summand-listp-when-list-in-bagp
    (implies (and (obag::bagp b)
                  (summand-listp b n)
                  (list-in-bagp l b)
                  (true-listp l))
             (summand-listp l n))
    :induct (list-in-bagp l b)
    :disable (summandp)))

;;; A sub-multiset of a delete is a sub-multiset of the whole bag.

(defruled list-in-bagp-of-delete-weaken
  (implies (and (obag::bagp b)
                (list-in-bagp l (obag::delete y b)))
           (list-in-bagp l b))
  :induct (list-in-bagp l b)
  :enable (list-in-bagp in-of-delete in-when-occs-geq-2)
  :hints (("Subgoal *1/2" :use ((:instance delete-of-delete
                                           (x (car l))
                                           (y y)
                                           (bag b))))))

;;; Sub-multiset-ness is monotone under inserting more elements.

(defruled list-in-bagp-of-insert
  (implies (and (obag::bagp b)
                (list-in-bagp l b))
           (list-in-bagp l (obag::insert x b)))
  :induct (list-in-bagp l b)
  :enable (list-in-bagp in-of-insert list-in-bagp-of-delete-weaken)
  :expand ((list-in-bagp l (obag::insert x b)))
  :hints (("Subgoal *1/2''" :cases ((equal (car l) x)))))

(defruled list-in-bagp-of-insert-list
  (implies (and (obag::bagp b)
                (list-in-bagp l b))
           (list-in-bagp l (insert-list e b)))
  :induct (insert-list e b)
  :enable (insert-list list-in-bagp-of-insert))

;;; Deleting a sub-multiset commutes past inserts: the deletes always find
;;; their occurrences in the base bag.

(defruled delete-list-of-insert
  (implies (and (obag::bagp b)
                (list-in-bagp l b))
           (equal (delete-list l (obag::insert x b))
                  (obag::insert x (delete-list l b))))
  :induct (list-in-bagp l b)
  :enable (list-in-bagp delete-list)
  :hints (("Subgoal *1/2" :cases ((equal (car l) x)))))

(defruled delete-list-of-insert-list
  (implies (and (obag::bagp b)
                (list-in-bagp l b))
           (equal (delete-list l (insert-list e b))
                  (insert-list e (delete-list l b))))
  :induct (insert-list e b)
  :enable (insert-list delete-list-of-insert insert-list-of-insert
           list-in-bagp-of-insert-list))

(defruled delete-list-of-insert-list-same
  (implies (obag::bagp b)
           (equal (delete-list l (insert-list l b))
                  b))
  :induct (insert-list l b)
  :enable (insert-list delete-list insert-list-of-insert))

(defruled list-in-bagp-of-insert-list-self
  (implies (obag::bagp b)
           (list-in-bagp l (insert-list l b)))
  :induct (insert-list l b)
  :enable (insert-list list-in-bagp insert-list-of-insert in-of-insert))

;;; Composition laws.

(defruled insert-list-of-append
  (equal (insert-list (append u v) b)
         (insert-list u (insert-list v b)))
  :induct (insert-list u b)
  :enable (insert-list))

(defruled delete-list-of-append
  (equal (delete-list (append u v) b)
         (delete-list v (delete-list u b)))
  :induct (delete-list u b)
  :enable (delete-list))

;;; Multiplicity in a sub-multiset bounds multiplicity in the bag.

(defruled count-occurrences-leq-occs
  (implies (and (obag::bagp b)
                (list-in-bagp l b))
           (<= (count-occurrences x l) (obag::occs x b)))
  :induct (list-in-bagp l b)
  :enable (list-in-bagp count-occurrences obag::occs-of-delete))

;;; scheme-sum against insert-list and delete-list; characteristic 2 makes
;;; the two laws identical.

(defruled scheme-sum-of-insert-list
  (implies (and (obag::bagp b)
                (summand-listp b n)
                (summand-listp l n)
                (natp n))
           (equal (scheme-sum (insert-list l b) n)
                  (bit-list-add (scheme-sum l n) (scheme-sum b n))))
  :induct (insert-list l b)
  :enable (insert-list scheme-sum scheme-sum-of-insert
           bit-list-add-associative)
  :disable (summand-tensor tensor summandp))

(defruled scheme-sum-of-delete-list
  (implies (and (obag::bagp b)
                (summand-listp b n)
                (list-in-bagp l b)
                (natp n))
           (equal (scheme-sum (delete-list l b) n)
                  (bit-list-add (scheme-sum l n) (scheme-sum b n))))
  :induct (list-in-bagp l b)
  :enable (list-in-bagp delete-list scheme-sum scheme-sum-of-delete
           bit-list-add-associative bit-list-add-commutative
           bit-list-add-commutative-2)
  :disable (summand-tensor tensor summandp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 1: the single replacement step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; From sch plus two copies of sp = s[p := u] (as produced by
;;; add-arbitrary), the flip of sp against s at position (pos-prev p) --
;;; they agree there and at (pos-next p) -- is valid; its output at the
;;; remaining position is a zero summand (dropped), so the move lands on
;;; sch with s replaced by s[p := u] and s[p := s_p + u].  This is the
;;; paper's replacement step in lemma:zero-subset (stated there for the A
;;; position with a flip on B; here uniformly in p).

(defruled replace-step
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (obag::in s sch)
                (natp p) (< p 3)
                (bit-matp u n n)
                (not (equal u (bit-mat0 n n)))
                (not (equal u (summand-get-pos s p))))
           (b* ((sp (summand-set-pos s p u))
                (spp (summand-set-pos s p (bit-mat-add (summand-get-pos s p) u)))
                (sch1 (obag::insert sp (obag::insert sp sch)))
                (move (list :flip (pos-prev p) sp s)))
             (and (move-validp move sch1)
                  (equal (apply-move move sch1 n)
                         (obag::insert spp
                                       (obag::insert sp (obag::delete s sch)))))))
  :do-not-induct t
  :use ((:instance summandp-when-in-summand-listp))
  :enable (apply-move in-of-insert in-of-delete bit-mat-add-same)
  :disable (bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 2: decomposing one position of one summand into units
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; get/set algebra

(defrule summand-get-pos-of-summand-set-pos-same
  (equal (summand-get-pos (summand-set-pos s p m) p) m))

(defruled summand-set-pos-of-summand-set-pos-same
  (equal (summand-set-pos (summand-set-pos s p m) p m2)
         (summand-set-pos s p m2)))

(defruled summand-set-pos-of-own-get
  (implies (mat-triplep s)
           (equal (summand-set-pos s p (summand-get-pos s p)) s)))

(defruled summandp-of-summand-set-pos
  (implies (and (summandp s n)
                (bit-matp m n n)
                (not (equal m (bit-mat0 n n))))
           (summandp (summand-set-pos s p m) n))
  :disable (bit-matp))

(defruled unit-at-first-one-nonzero
  (implies (and (bit-matp x n n)
                (natp n)
                (< 0 (count-ones-mat x)))
           (not (equal (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) n n)
                       (bit-mat0 n n))))
  :use ((:instance count-ones-mat-of-add-unit (m n))
        (:instance bit-mat-add-of-bit-mat0-2 (a x) (m n)))
  :disable (bit-mat-add-of-bit-mat0-2 bit-matp))

(defruled unit-at-first-one-neq
  (implies (and (bit-matp x n n)
                (natp n)
                (<= 2 (count-ones-mat x)))
           (not (equal (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) n n)
                       x)))
  :use ((:instance count-ones-mat-of-add-unit (m n))
        (:instance bit-mat-add-same (a x) (m n) (n n))
        (:instance count-ones-mat-zero-iff
                   (x (bit-mat-add x x)) (m n)))
  :disable (bit-matp))

(defruled unit-when-count-ones-1
  (implies (and (bit-matp x n n)
                (natp n)
                (equal (count-ones-mat x) 1))
           (equal (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) n n)
                  x))
  :use ((:instance count-ones-mat-of-add-unit (m n))
        (:instance count-ones-mat-zero-iff
                   (x (bit-mat-add x (bit-mat-unit2 (first-one-row x)
                                                    (first-one-col-mat x)
                                                    n n)))
                   (m n))
        (:instance bit-mat-add-zero-iff-equal
                   (a x)
                   (b (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) n n))
                   (m n)))
  :disable (bit-matp bit-mat-add-zero-iff-equal))

(defruled list-3-reconstruct
  (implies (and (true-listp s)
                (equal (len s) 3))
           (equal (list (car s) (cadr s) (caddr s)) s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; definitions

(define set-pos-all ((s mat-triplep) (p natp) (us bit-mat-list-p))
  :returns (l mat-triple-listp :hyp :guard)
  (if (atom us)
      nil
    (cons (summand-set-pos s p (car us))
          (set-pos-all s p (cdr us))))
  ///
  (defruled set-pos-all-of-summand-set-pos
    (equal (set-pos-all (summand-set-pos s p m) p us)
           (set-pos-all s p us))
    :induct (set-pos-all s p us)
    :enable (summand-set-pos-of-summand-set-pos-same)))

(define decompose-pos-path ((sch obag::bagp) (s mat-triplep) (p natp) (n natp))
  :guard (mat-triple-listp sch)
  :measure (count-ones-mat (summand-get-pos s p))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :induct (decompose-pos-path sch s p n)
                           :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                                      (disable add-arbitrary-path)))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (current-theory :here))))
  (b* ((xp (summand-get-pos s p))
       ((unless (and (bit-matp xp n n)
                     (natp n)
                     (<= 2 (count-ones-mat xp))))
        nil)
       (u (bit-mat-unit2 (first-one-row xp) (first-one-col-mat xp) n n))
       (sp (summand-set-pos s p u))
       (xpp (bit-mat-add xp u))
       (spp (summand-set-pos s p xpp))
       (sch2 (obag::insert spp
                           (obag::insert sp (obag::delete s sch)))))
    (append (append (add-arbitrary-path sch (car sp) (cadr sp) (caddr sp) n)
                    (list (list :flip (pos-prev p) sp s)))
            (decompose-pos-path sch2 spp p n)))
  :hints (("Goal" :use ((:instance count-ones-mat-of-add-unit
                                   (x (summand-get-pos s p))
                                   (m n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; base lemma

(defruled decompose-base
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (obag::in s sch)
                (natp p) (< p 3)
                (< (count-ones-mat (summand-get-pos s p)) 2))
           (equal (insert-list
                   (set-pos-all s p (units-of (summand-get-pos s p) n n))
                   (obag::delete s sch))
                  sch))
  :do-not-induct t
  :use ((:instance summandp-when-in-summand-listp)
        (:instance count-ones-mat-zero-iff
                   (x (summand-get-pos s p)) (m n)))
  :enable (insert-list set-pos-all
           unit-when-count-ones-1
           summand-set-pos-of-own-get
           units-of bit-mat-add-same)
  :disable (bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; step lemma

(defruled decompose-step
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (obag::in s sch)
                (natp p) (< p 3)
                (<= 2 (count-ones-mat (summand-get-pos s p))))
           (b* ((xp (summand-get-pos s p))
                (u (bit-mat-unit2 (first-one-row xp) (first-one-col-mat xp) n n))
                (sp (summand-set-pos s p u))
                (xpp (bit-mat-add xp u))
                (spp (summand-set-pos s p xpp))
                (sch2 (obag::insert spp
                                    (obag::insert sp (obag::delete s sch))))
                (path1 (append (add-arbitrary-path sch (car sp) (cadr sp)
                                                   (caddr sp) n)
                               (list (list :flip (pos-prev p) sp s)))))
             (and (path-validp path1 sch n)
                  (equal (apply-moves path1 sch n) sch2)
                  (correct-schemep sch2 n)
                  (obag::in spp sch2))))
  :do-not-induct t
  :use ((:instance summandp-when-in-summand-listp)
        (:instance replace-step
                   (u (bit-mat-unit2 (first-one-row (summand-get-pos s p))
                                     (first-one-col-mat (summand-get-pos s p))
                                     n n)))
        (:instance scheme-sum-of-apply-move
                   (move (list :flip (pos-prev p)
                             (summand-set-pos
                              s p
                              (bit-mat-unit2 (first-one-row (summand-get-pos s p))
                                             (first-one-col-mat (summand-get-pos s p))
                                             n n))
                             s))
                   (sch (obag::insert
                         (summand-set-pos
                          s p
                          (bit-mat-unit2 (first-one-row (summand-get-pos s p))
                                         (first-one-col-mat (summand-get-pos s p))
                                         n n))
                         (obag::insert
                          (summand-set-pos
                           s p
                           (bit-mat-unit2 (first-one-row (summand-get-pos s p))
                                          (first-one-col-mat (summand-get-pos s p))
                                          n n))
                          sch))))
        (:instance bit-list-add-cancel-1
                   (x (mm-tensor n))
                   (y (summand-tensor
                       (summand-set-pos
                        s p
                        (bit-mat-unit2 (first-one-row (summand-get-pos s p))
                                       (first-one-col-mat (summand-get-pos s p))
                                       n n))))
                   (n (* n n n n n n))))
  :enable (correct-schemep apply-moves
           scheme-sum-of-insert
           unit-at-first-one-nonzero
           unit-at-first-one-neq
           summandp-of-summand-set-pos
           list-3-reconstruct
           in-of-insert in-of-delete
           count-ones-mat-zero-iff
           count-ones-mat-of-add-unit)
  :disable (bit-matp apply-move move-validp
            add-arbitrary-path))

;;; A factor of a well-formed summand is nonzero.

(defruled summand-get-pos-nonzero
  (implies (and (summandp s n)
                (natp p) (< p 3))
           (not (equal (summand-get-pos s p) (bit-mat0 n n))))
  :disable (bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 2b: the single-position invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled summand-set-pos-injective
  (iff (equal (summand-set-pos s p m1) (summand-set-pos s p m2))
       (equal m1 m2)))

;; Deleting x from a bag into which y then x were inserted leaves insert y:
;; unconditional (when x = y the two same-element rules compose).
(defrule delete-of-insert-insert
  (implies (obag::bagp b)
           (equal (obag::delete x (obag::insert y (obag::insert x b)))
                  (obag::insert y b)))
  :cases ((equal x y)))

(defrule decompose-pos-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (obag::in s sch)
                (natp p) (< p 3))
           (b* ((path (decompose-pos-path sch s p n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res
                         (insert-list
                          (set-pos-all s p (units-of (summand-get-pos s p) n n))
                          (obag::delete s sch)))
                  (correct-schemep res n))))
  :induct (decompose-pos-path sch s p n)
  :enable (decompose-pos-path
           insert-list set-pos-all units-of
           insert-list-of-insert
           set-pos-all-of-summand-set-pos
           summand-set-pos-injective
           bit-mat-add-equal-arg2
           summand-get-pos-nonzero
           summandp-of-summand-set-pos
           unit-at-first-one-nonzero
           correct-schemep
           apply-moves)
  :disable (apply-move move-validp mm-tensor scheme-sum tensor
            summand-tensor bit-matp
            add-arbitrary-path add-arbitrary
            first-one-row first-one-col-mat bit-mat-unit2
            count-ones-mat bit-mat-add
            summand-set-pos summand-get-pos)
  :hints (("Subgoal *1/2" :use (decompose-base
                                (:instance summandp-when-in-summand-listp)))
          ("Subgoal *1/1" :use (decompose-step
                                (:instance summandp-when-in-summand-listp)
                                (:instance summand-get-pos-nonzero))
           :expand ((units-of (summand-get-pos s p) n n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 3: sweeping one position over a summand list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; insert-list blocks commute (needed to reassemble appended expansions)

(defruled insert-list-swap
  (implies (obag::bagp b)
           (equal (insert-list a (insert-list c b))
                  (insert-list c (insert-list a b))))
  :rule-classes ((:rewrite :loop-stopper ((a c))))
  :induct (insert-list a b)
  :enable (insert-list insert-list-of-insert))

;;; Replacing position p of a well-formed summand by each unit of a
;;; decomposition yields a list of well-formed summands.

(defruled summand-listp-of-set-pos-all-units
  (implies (and (summandp s n)
                (natp n) (natp p) (< p 3)
                (bit-matp x n n))
           (summand-listp (set-pos-all s p (units-of x n n)) n))
  :induct (units-of x n n)
  :enable (units-of set-pos-all
           summandp-of-summand-set-pos
           unit-at-first-one-nonzero)
  :disable (bit-matp summandp summand-set-pos
            first-one-row first-one-col-mat bit-mat-unit2
            count-ones-mat)
  :hints (("Subgoal *1/2" :use ((:instance count-ones-mat-zero-iff
                                           (m n))))))

;;; The unit expansion of position p of every summand in a list.

(define expand-pos-list ((l mat-triple-listp) (p natp) (n natp))
  :returns (e mat-triple-listp :hyp :guard
             :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (enable mat-triple-listp-of-insert-list
                                                    mat-triple-head-lemmas))))
  (if (atom l)
      nil
    (append (set-pos-all (car l) p
                         (units-of (summand-get-pos (car l) p) n n))
            (expand-pos-list (cdr l) p n))))

;;; The path decomposing position p of every summand of l, tracking the
;;; evolving scheme through the closed-form results.

(define decompose-list-pos-path ((sch obag::bagp) (l mat-triple-listp)
                                 (p natp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :induct (decompose-list-pos-path sch l p n)
                           :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                                      (e/d (mat-triple-listp-of-insert-list
                                                            mat-triple-head-lemmas)
                                                           (decompose-pos-path))))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (enable mat-triple-listp-of-insert-list
                                                    mat-triple-head-lemmas))))
  (if (atom l)
      nil
    (append (decompose-pos-path sch (car l) p n)
            (decompose-list-pos-path
             (insert-list (set-pos-all (car l) p
                                       (units-of (summand-get-pos (car l) p)
                                                 n n))
                          (obag::delete (car l) sch))
             (cdr l) p n))))

(defrule decompose-list-pos-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (list-in-bagp l sch)
                (natp p) (< p 3))
           (b* ((path (decompose-list-pos-path sch l p n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res
                         (insert-list (expand-pos-list l p n)
                                      (delete-list l sch)))
                  (correct-schemep res n))))
  :induct (decompose-list-pos-path sch l p n)
  :enable (decompose-list-pos-path expand-pos-list
           list-in-bagp delete-list insert-list
           insert-list-of-append
           insert-list-swap
           delete-list-of-insert-list
           list-in-bagp-of-insert-list
           summand-listp-of-set-pos-all-units
           correct-schemep
           apply-moves)
  :disable (apply-move move-validp mm-tensor scheme-sum tensor
            summand-tensor bit-matp
            decompose-pos-path units-of set-pos-all
            first-one-row first-one-col-mat bit-mat-unit2
            count-ones-mat bit-mat-add
            summand-set-pos summand-get-pos)
  :hints (("Subgoal *1/2" :use ((:instance decompose-pos-invariant
                                           (s (car l)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 3b: typing and sums of the unit expansions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; typing: unit positions

;;; Every summand in l has a unit matrix at position p.

(define pos-unit-listp ((l mat-triple-listp) (p natp) (n natp))
  :returns (yes/no booleanp)
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (enable mat-triple-listp-of-insert-list
                                                    mat-triple-head-lemmas))))
  (if (atom l)
      t
    (and (unit-matp (summand-get-pos (car l) p) n n)
         (pos-unit-listp (cdr l) p n)
         t)))

;;; get-pos of set-pos at a different position (both < 3).

(defruled summand-get-pos-of-summand-set-pos-diff
  (implies (and (natp p) (< p 3)
                (natp q) (< q 3)
                (not (equal p q)))
           (equal (summand-get-pos (summand-set-pos s p m) q)
                  (summand-get-pos s q))))

;;; The units produced by units-of are unit-matp.

(defruled unit-matp-of-first-one-unit
  (implies (and (bit-matp x n n)
                (natp n)
                (< 0 (count-ones-mat x)))
           (unit-matp (bit-mat-unit2 (first-one-row x) (first-one-col-mat x)
                                     n n)
                      n n))
  :use ((:instance first-one-row-bound (m n))
        (:instance first-one-col-mat-bound (m n))
        (:instance unit-matp-of-bit-mat-unit
                   (i (first-one-row x)) (j (first-one-col-mat x))
                   (m n) (n n)))
  :enable (bit-mat-unit2-is-bit-mat-unit)
  :disable (bit-matp unit-matp))

;;; An expansion block has units at position p ...

(defruled pos-unit-listp-of-set-pos-all-units
  (implies (and (bit-matp x n n)
                (natp n) (natp p) (< p 3))
           (pos-unit-listp (set-pos-all s p (units-of x n n)) p n))
  :induct (units-of x n n)
  :enable (units-of set-pos-all pos-unit-listp
           unit-matp-of-first-one-unit)
  :disable (bit-matp unit-matp summand-set-pos summand-get-pos
            first-one-row first-one-col-mat bit-mat-unit2
            count-ones-mat)
  :hints (("Subgoal *1/2" :use ((:instance count-ones-mat-zero-iff
                                           (m n))))))

;;; ... and preserves the factors at the other positions.

(defruled pos-unit-listp-of-set-pos-all-preserve
  (implies (and (natp p) (< p 3)
                (natp q) (< q 3)
                (not (equal p q))
                (unit-matp (summand-get-pos s q) n n))
           (pos-unit-listp (set-pos-all s p us) q n))
  :induct (set-pos-all s p us)
  :enable (set-pos-all pos-unit-listp
           summand-get-pos-of-summand-set-pos-diff)
  :disable (unit-matp summand-set-pos summand-get-pos))

;;; pos-unit-listp over append.

(defruled pos-unit-listp-of-append
  (equal (pos-unit-listp (append a b) p n)
         (and (pos-unit-listp a p n)
              (pos-unit-listp b p n)))
  :induct (cdr-induct a)
  :enable (pos-unit-listp))

;;; The expansion sweep at p makes position p unit ...

(defruled pos-unit-listp-of-expand-pos-list
  (implies (and (summand-listp l n)
                (natp n) (natp p) (< p 3))
           (pos-unit-listp (expand-pos-list l p n) p n))
  :induct (cdr-induct l)
  :enable (expand-pos-list pos-unit-listp pos-unit-listp-of-append
           pos-unit-listp-of-set-pos-all-units)
  :disable (unit-matp summandp set-pos-all units-of
            summand-get-pos bit-matp))

;;; ... and preserves unit-ness at other positions.

(defruled pos-unit-listp-of-expand-pos-list-preserve
  (implies (and (pos-unit-listp l q n)
                (natp p) (< p 3)
                (natp q) (< q 3)
                (not (equal p q)))
           (pos-unit-listp (expand-pos-list l p n) q n))
  :induct (cdr-induct l)
  :enable (expand-pos-list pos-unit-listp pos-unit-listp-of-append
           pos-unit-listp-of-set-pos-all-preserve)
  :disable (unit-matp set-pos-all units-of summand-get-pos))

;;; A dimensioned list with units at all three positions is a list of unit
;;; summands.

(defruled unit-summand-listp-when-pos-units
  (implies (and (summand-dim-listp l n)
                (pos-unit-listp l 0 n)
                (pos-unit-listp l 1 n)
                (pos-unit-listp l 2 n))
           (unit-summand-listp l n))
  :induct (cdr-induct l)
  :enable (pos-unit-listp unit-summand-listp unit-summandp)
  :disable (unit-matp bit-matp))

;;; summand-listp of the expansion sweep (dimensioned, nonzero).

(defruled summand-listp-of-expand-pos-list
  (implies (and (summand-listp l n)
                (natp n) (natp p) (< p 3))
           (summand-listp (expand-pos-list l p n) n))
  :induct (cdr-induct l)
  :enable (expand-pos-list summand-listp-of-append
           summand-listp-of-set-pos-all-units)
  :disable (summandp set-pos-all units-of summand-get-pos bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; sums of the expansions

(defruled scheme-sum-of-append
  (implies (and (summand-dim-listp a n)
                (summand-dim-listp b n)
                (natp n))
           (equal (scheme-sum (append a b) n)
                  (bit-list-add (scheme-sum a n) (scheme-sum b n))))
  :induct (cdr-induct a)
  :enable (scheme-sum bit-list-add-associative)
  :disable (summand-tensor tensor))

;;; The units of x sum back to x.

(defruled mat-list-sum-of-units-of
  (implies (and (bit-matp x n n)
                (natp n))
           (equal (mat-list-sum (units-of x n n) n n) x))
  :induct (units-of x n n)
  :enable (units-of mat-list-sum
           bit-mat-add-commutative)
  :disable (bit-matp first-one-row first-one-col-mat bit-mat-unit2
            count-ones-mat))

;;; tensor with a literal zero factor (free-variable-friendly forms of
;;; tensor-when-zero-a/b/c).

(defruled tensor-of-bit-mat0-a
  (implies (and (bit-matp b n n) (bit-matp c n n) (natp n))
           (equal (tensor (bit-mat0 n n) b c)
                  (bit-listn0 (* n n n n n n))))
  :use ((:instance tensor-when-zero-a (a (bit-mat0 n n)))))

(defruled tensor-of-bit-mat0-b
  (implies (and (bit-matp a n n) (bit-matp c n n) (natp n))
           (equal (tensor a (bit-mat0 n n) c)
                  (bit-listn0 (* n n n n n n))))
  :use ((:instance tensor-when-zero-b (b (bit-mat0 n n)))))

(defruled tensor-of-bit-mat0-c
  (implies (and (bit-matp a n n) (bit-matp b n n) (natp n))
           (equal (tensor a b (bit-mat0 n n))
                  (bit-listn0 (* n n n n n n))))
  :use ((:instance tensor-when-zero-c (c (bit-mat0 n n)))))

;;; The sum of an expansion block is the tensor of the summand with
;;; position p replaced by the sum of the units.

(defruled scheme-sum-of-set-pos-all
  (implies (and (summand-dimp s n)
                (bit-mat-listnp us n n)
                (natp n) (natp p) (< p 3))
           (equal (scheme-sum (set-pos-all s p us) n)
                  (summand-tensor
                   (summand-set-pos s p (mat-list-sum us n n)))))
  :induct (cdr-induct us)
  :enable (set-pos-all scheme-sum mat-list-sum bit-mat-listnp
           tensor-of-add-a tensor-of-add-b tensor-of-add-c
           tensor-of-bit-mat0-a tensor-of-bit-mat0-b tensor-of-bit-mat0-c)
  :disable (tensor bit-matp))

(defruled bit-mat-listnp-of-units-of
  (bit-mat-listnp (units-of x m n) m n)
  :induct (units-of x m n)
  :enable (units-of bit-mat-listnp)
  :disable (first-one-row first-one-col-mat bit-mat-unit2 count-ones-mat))

;;; Hence each summand's expansion sums to its own tensor, and the sweep
;;; preserves the scheme sum.

(defruled scheme-sum-of-expand-pos-list
  (implies (and (summand-listp l n)
                (natp n) (natp p) (< p 3))
           (equal (scheme-sum (expand-pos-list l p n) n)
                  (scheme-sum l n)))
  :induct (cdr-induct l)
  :enable (expand-pos-list scheme-sum scheme-sum-of-append
           scheme-sum-of-set-pos-all mat-list-sum-of-units-of
           summand-set-pos-of-own-get
           summand-listp-of-set-pos-all-units
           summand-listp-of-expand-pos-list
           bit-mat-listnp-of-units-of)
  :disable (summand-tensor tensor bit-matp
            set-pos-all units-of summand-get-pos summand-set-pos
            mat-list-sum))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 4: deleting a zero-summing unit-summand sub-multiset in pairs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; membership from positive count

(defruled member-when-count-occurrences-pos
  (implies (< 0 (count-occurrences x l))
           (member-equal x l))
  :induct (cdr-induct l)
  :enable (count-occurrences))

;;; removing one occurrence adds the tensor back (characteristic 2)

(defruled scheme-sum-of-remove1
  (implies (and (member-equal x l)
                (summand-dim-listp l n)
                (natp n))
           (equal (scheme-sum (remove1-equal x l) n)
                  (bit-list-add (summand-tensor x) (scheme-sum l n))))
  :induct (cdr-induct l)
  :enable (scheme-sum remove1-equal
           bit-list-add-associative bit-list-add-commutative
           bit-list-add-commutative-2)
  :disable (summand-tensor tensor)
  :hints (("Subgoal *1/2"
           :use ((:instance bit-list-add-cancel-1
                            (x (scheme-sum (cdr l) n))
                            (y (summand-tensor (car l)))
                            (n (* n n n n n n)))))))

(defruled unit-summand-listp-of-remove1
  (implies (unit-summand-listp l n)
           (unit-summand-listp (remove1-equal x l) n))
  :induct (cdr-induct l)
  :enable (unit-summand-listp remove1-equal)
  :disable (unit-summandp))

;;; list-in-bagp and delete-list through removing a pair

(defruled list-in-bagp-of-remove1-delete
  (implies (and (obag::bagp b)
                (member-equal x m)
                (list-in-bagp m b))
           (list-in-bagp (remove1-equal x m) (obag::delete x b)))
  :induct (list-in-bagp m b)
  :enable (list-in-bagp remove1-equal in-of-delete))

(defruled delete-list-of-remove1
  (implies (and (obag::bagp b)
                (member-equal x m))
           (equal (delete-list (remove1-equal x m) (obag::delete x b))
                  (delete-list m b)))
  :induct (delete-list m b)
  :enable (delete-list remove1-equal))

;;; count-occurrences through the recursion

(defruled count-occurrences-of-remove1
  (implies (member-equal x l)
           (equal (count-occurrences x (remove1-equal x l))
                  (1- (count-occurrences x l))))
  :induct (cdr-induct l)
  :enable (count-occurrences remove1-equal))

;;; The head of a nonempty zero-summing unit-summand sub-multiset occurs
;;; at least twice: its multiplicity is even (parity theorem) and positive.

(defruled head-pair-facts
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (unit-summand-listp l n)
                (list-in-bagp l sch)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n)))
                (consp l))
           (and (member-equal (car l) (cdr l))
                (<= 2 (obag::occs (car l) sch))))
  :do-not-induct t
  :use ((:instance even-count-occurrences-when-zero-scheme-sum
                   (s (car l)))
        (:instance count-occurrences-leq-occs
                   (x (car l)) (b sch))
        (:instance member-when-count-occurrences-pos
                   (x (car l)) (l (cdr l))))
  :enable (count-occurrences evenp-of-plus-1 list-in-bagp)
  :disable (scheme-sum unit-summand-listp evenp summandp
            unit-summandp bit-matp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the path

(define delete-pairs-path ((sch obag::bagp) (l mat-triple-listp) (n natp))
  :irrelevant-formals-ok t
  :measure (len l)
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :induct (delete-pairs-path sch l n)
                           :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                                      (enable mat-triple-listp-of-insert-list
                                                              mat-triple-head-lemmas)))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-obag-lemmas)
                                            (enable mat-triple-listp-of-insert-list
                                                    mat-triple-head-lemmas))))
  (declare (irrelevant sch n))
  (if (atom l)
      nil
    (cons (list :flip 0 (car l) (car l))
          (delete-pairs-path (obag::delete (car l)
                                           (obag::delete (car l) sch))
                             (remove1-equal (car l) (cdr l))
                             n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the invariant

(defrule delete-pairs-invariant
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (unit-summand-listp l n)
                (list-in-bagp l sch)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n))))
           (b* ((path (delete-pairs-path sch l n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (delete-list l sch)))))
  :induct (delete-pairs-path sch l n)
  :enable (delete-pairs-path apply-moves
           list-in-bagp delete-list unit-summand-listp
           member-when-count-occurrences-pos
           scheme-sum-of-remove1
           unit-summand-listp-of-remove1
           list-in-bagp-of-remove1-delete
           delete-list-of-remove1
           count-occurrences-of-remove1
           count-occurrences-leq-occs
           scheme-sum
           in-when-occs-geq-2)
  :disable (apply-move move-validp scheme-sum-of-insert
            summand-tensor tensor unit-summandp bit-matp summandp
            evenp count-occurrences)
  :hints (("Subgoal *1/2"
           :use (head-pair-facts
                 (:instance bit-list-add-cancel-1
                            (x (scheme-sum (remove1-equal (car l) (cdr l)) n))
                            (y (summand-tensor (car l)))
                            (n (* n n n n n n)))))))

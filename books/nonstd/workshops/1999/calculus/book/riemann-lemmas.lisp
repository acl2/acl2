(in-package "ACL2")

(include-book "top-with-meta")
(include-book "riemann-defuns")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Arithmetic lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following is similar to <-*-RIGHT-CANCEL, but a linear rule,
;;; found from failed attempt to prove a version of dot-prod-bounded.
;;; In fact it is used in the proof of DOT-PROD-BOUNDED-LEMMA.
(defthm <-times-right
  (implies (and (realp x)
                (realp y)
                (realp z)
                (<= 0 x)
                (<= y z))
           (<= (* y x) (* z x)))
  :rule-classes :linear)

(defthm abs-*-is-*
  (implies (and (realp x)
                (realp y)
                (equal (abs x) x)
                (equal (abs y) y))
           (equal (abs (* x y))
                  (* x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lemmas about partitionp and other such notions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some key lemmas about the basic notions.
(defthm common-refinement-preserves-partitionp
  (implies (and (partitionp p1)
                (partitionp p2))
           (partitionp (common-refinement p1 p2))))

(defthm common-refinement-is-refinement-of-first
  (implies (and (partitionp p1)
                (partitionp p2))
           (refinement-p (common-refinement p1 p2) p1)))

(defthm common-refinement-is-refinement-of-second
  (implies (and (partitionp p1)
                (partitionp p2))
           (refinement-p (common-refinement p1 p2) p2)))

(defthm common-refinement-is-commutative
  (implies (and (partitionp p1)
                (partitionp p2))
           (equal (common-refinement p1 p2)
                  (common-refinement p2 p1))))

;;; The following needs to be more than just a :forward-chaining rule
;;; in order for the proof of real-listp-map-rcfn-refinement to
;;; succeed.
(defthm first-not-greater-than-last-for-partitions
  (implies (partitionp p)
           (not (< (car (last p)) (car p))))
  :rule-classes (:forward-chaining :linear))

(defthm abslist-non-negative
  (non-negative-listp (abslist x))
  :rule-classes (:generalize :rewrite))

(defthm sumlist-non-negative
  (implies (non-negative-listp x)
           (<= 0 (sumlist x)))
  :rule-classes (:generalize :rewrite))

(defthm maxlist-non-negative
  ;; used in dot-prod-bounded-lemma
  (implies (non-negative-listp x)
           (<= 0 (maxlist x)))
  :rule-classes :generalize)

(defthm dot-prod-abslist
  (implies (and (real-listp x)
                (non-negative-listp x)
                (real-listp y))
           (<= (dotprod x y)
               (dotprod x (abslist y))))
  :rule-classes :linear)

;;; I checked that at least one of the following two must be a
;;; generalize lemma, or else the proof fails for
;;; dot-prod-bounded-lemma.  These were in fact originally constructed
;;; as generalize lemmas only.
(defthm realp-sumlist
  (implies (real-listp x)
           (realp (sumlist x)))
  :rule-classes (:generalize :rewrite))

(defthm realp-maxlist
  (implies (real-listp x)
           (realp (maxlist x)))
  :rule-classes (:generalize :rewrite))

(defthm non-negative-listp-map-times
  (implies (and (real-listp x)
                (real-listp y)
                (non-negative-listp x)
                (non-negative-listp y))
           (non-negative-listp (map-times x y))))

(defthm abs-sumlist
  (implies (non-negative-listp x)
           (equal (abs (sumlist x))
                  (sumlist x))))

(defthm dot-prod-bounded-lemma
  ;; The proof fails when x and y are switched in the conclusion.
  ;; Go figure.
  (implies (and (real-listp x)
                (real-listp y)
                (non-negative-listp x)
                (non-negative-listp y))
           (<= (abs (dotprod y x))
               (* (sumlist y)
                  (maxlist x))))
  :rule-classes :linear)

(defthm len-abslist
  (equal (len (abslist x))
         (len x)))

(defthm real-listp-abslist
  (implies (true-listp x)
           (equal (real-listp (abslist x))
                  (real-listp x))))

(defthm dot-product-abslist-2
  (implies (and (real-listp x)
                (non-negative-listp x)
                (real-listp y))
           (<= (abs (dotprod x y))
               (abs (dotprod x (abslist y)))))
  :hints (("Goal" :induct (map-times x y)))
  :rule-classes nil)

;;; We will apply the following lemma where x is (deltas p) and y is
;;; the list of differences of applying rcfn at a given member of p2
;;; and at the least member of p1 greater than or equal to x.

(defthm dot-prod-bounded
  (implies (and (real-listp x)
                (non-negative-listp x)
                (real-listp y))
           (<= (abs (dotprod x y))
               (* (sumlist x)
                  (maxlist (abslist y)))))
  :hints (("Goal" :in-theory (disable dotprod)
           :use dot-product-abslist-2)))

;;; Let us now show that summing the deltas gives us the whole
;;; interval.  Somewhat amazingly, we can prove this even without
;;; knowing that we have a partition.

(defthm sumlist-deltas
  (equal (sumlist (deltas p))
         (span p)))

;;; In the following the original hypothesis required (len x) to be
;;; equal to (len y) and (len z), but that was stronger than
;;; necessary.
(defthm minus-dotprod-2
  (implies (equal (len y) (len z))
           (equal (- (dotprod x y) (dotprod x z))
                  (dotprod x (difflist y z))))
  :hints (("Goal" :induct (list (difflist x y) (difflist x z))))
  :rule-classes
  (:rewrite
   ;; and a commuted version:
   (:rewrite :corollary
             (implies (and (equal (len x) (len y))
                           (equal (len x) (len z)))
                      (equal (+ (- (dotprod x z)) (dotprod x y))
                             (dotprod x (difflist y z)))))))

(defthm len-deltas
  (equal (len (deltas p))
         (len (cdr p))))

(defthm len-map-rcfn
  (equal (len (map-rcfn p))
         (len p)))

(defthm len-map-rcfn-refinement
  (equal (len (map-rcfn-refinement p1 p2))
         (len p1)))

(defthm partitionp-implies-real-listp-deltas
  (implies (partitionp p)
           (real-listp (deltas p)))
  :rule-classes (:forward-chaining :rewrite))

(defthm real-listp-difflist
  (implies (and (real-listp x)
                (real-listp y))
           (real-listp (difflist x y))))

(defthm real-listp-map-rcfn-cdr
  (implies (real-listp x)
           (real-listp (map-rcfn (cdr x)))))

(defthm partitionp-cdr-member
  (implies (and (partitionp p1)
                (member a p1))
           (equal (partitionp (cdr (member a p1)))
                  (not (equal (cdr (member a p1))
                              nil)))))

(defthm partitionp-forward-to-true-listp
  (implies (partitionp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defthm len-cdr-member-len
  (<= (len (cdr (member a x)))
      (len x))
  :rule-classes :linear)

(defthm refinementp-len
  (implies (and (refinement-p p1 p2)
                (partitionp p1)
                (partitionp p2))
           (<= (len p2)
               (len p1)))
  ;; hint found from inside the proof-builder loop
  :hints (("Goal" :expand (len p1)))
  :rule-classes nil)

(defthm partitionp-last
  (implies (partitionp p)
           (partitionp (last p))))

(defthm member-cdr-partition-lemma
  (implies (and (partitionp p)
                (< b (car p)))
           (not (member b p))))

(defthm member-cdr-partition-lemma-2
  (implies (and (partitionp p)
                (> b (car (last p))))
           (not (member b p))))

(defthm realp-next-gte
  (implies (and (partitionp p)
                (<= a (car (last p))))
           (realp (next-gte a p))))

(defthm partitionp-forward-to-real-listp
  (implies (partitionp p)
           (real-listp p))
  :rule-classes :forward-chaining)

(defthm real-listp-map-rcfn-refinement-cdr
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car (last p2))))
           (real-listp (map-rcfn-refinement (cdr p1) p2))))

(defthm non-negative-listp-deltas
  (implies (partitionp p)
           (non-negative-listp (deltas p))))

(defthm map-rcfn-refinement-nil
  ;; For use when map-rcfn-refinement is disabled
  (equal (map-rcfn-refinement nil p)
         nil))

(defthm dotprod-nil
  ;; For use when dotprod is disabled
  (equal (dotprod nil x)
         0))

(defthm len-difflist
  (equal (len (difflist x y))
         (len x)))

(defthm distributivity-commuted
  (equal (* (+ y z) x)
         (+ (* y x) (* z x))))

;;; An attempt to prove riemann-bound resulted in the following single
;;; unproved goal:

#|
  (IMPLIES
   (AND
    (CONSP (CDR P1))
    (<=
     (ABS (DOTPROD (DELTAS P1)
                   (DIFFLIST (MAP-RCFN (CDR P1))
                             (MAP-RCFN-REFINEMENT (CDR P1) P2))))
     (+
      (- (* (CAR P1)
            (MAXLIST (ABSLIST (DIFFLIST (MAP-RCFN (CDR P1))
                                        (MAP-RCFN-REFINEMENT (CDR P1) P2))))))
      (* (CAR (LAST P2))
         (MAXLIST (ABSLIST (DIFFLIST (MAP-RCFN (CDR P1))
                                     (MAP-RCFN-REFINEMENT (CDR P1) P2)))))))
    (PARTITIONP P1)
    (PARTITIONP P2)
    (EQUAL (LAST (CDR P1)) (LAST P2))
    (EQUAL (CAR P1) (CAR P2))
    (REFINEMENT-P P1 P2))
   (<= (ABS (DOTPROD (DELTAS P1)
                     (DIFFLIST (MAP-RCFN (CDR P1))
                               (MAP-RCFN-REFINEMENT (CDR P1) P2))))
       (+ (- (* (CAR P1)
                (MAXLIST (ABSLIST (DIFFLIST (MAP-RCFN P1)
                                            (MAP-RCFN-REFINEMENT P1 P2))))))
          (* (CAR (LAST P2))
             (MAXLIST (ABSLIST (DIFFLIST (MAP-RCFN P1)
                                         (MAP-RCFN-REFINEMENT P1 P2))))))))
|#

;;; The trick to proving the goal above is to generalize it so that
;;; all we are doing is taking maxlist of a bigger list in the
;;; conclusion than in the hypothesis.  Here are the components of
;;; that generalization (also generalizing the ABS term, and replacing
;;; (CAR P1) and (CAR (LAST P1))).

(defthm realp-last-element-of-partition
  (implies (partitionp p)
           (realp (car (last p))))
  :rule-classes :forward-chaining)

(defthm realp-abs
  (implies (realp x)
           (realp (abs x))))

(defthm realp-dotprod
  (implies (and (real-listp x)
                (real-listp y))
           (realp (dotprod x y))))

(defthm abs-nonnegative
  (<= 0 (abs x))
  ;; Why must we make this a :rewrite rule too?
  :rule-classes (:rewrite :type-prescription))

(defthm real-listp-map-rcfn
  (implies (real-listp x)
           (real-listp (map-rcfn x))))

(defthm real-listp-map-rcfn-refinement
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car (last p2))))
           (real-listp (map-rcfn-refinement p1 p2))))

(defthm maxlist-abslist-nonnegative
  (<= 0 (maxlist (abslist x)))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lemmas discovered during the various proofs after the initial
;;; period.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm dotprod-append
  (implies (equal (len x1) (len y1))
           (equal (dotprod (append x1 x2)
                           (append y1 y2))
                  (+ (dotprod x1 y1)
                     (dotprod x2 y2)))))

(defthm map-rcfn-refinement-append
  (equal (map-rcfn-refinement (append p1 p2) p3)
         (append (map-rcfn-refinement p1 p3)
                 (map-rcfn-refinement p2 p3))))

(defthm map-times-append
  (implies (equal (len x1) (len y1))
           (equal (map-times (append x1 x2)
                             (append y1 y2))
                  (append (map-times x1 y1)
                          (map-times x2 y2)))))

(defthm sumlist-append
  (equal (sumlist (append x y))
         (+ (sumlist x) (sumlist y))))

(defthm append-nil
  (implies (true-listp x)
           (equal (append x nil)
                  x)))

;;; !! I should consider making the following a type prescription rule.
(defthm consp-map-rcfn-refinement
  (equal (consp (map-rcfn-refinement p1 p2))
         (consp p1)))

(defthm cdr-append
  (implies (consp x)
           (equal (cdr (append x y))
                  (append (cdr x) y))))

(defthm sumlist-cons
  (equal (sumlist (cons a x))
         (+ a (sumlist x))))

(defthm riemann-rcfn-refinement-append
  (implies (and (consp p1)
                (consp p2)
                (equal (car (last p1)) (car p2)))
           (equal (riemann-rcfn-refinement (append p1 (cdr p2)) p3)
                  (+ (riemann-rcfn-refinement p1 p3)
                     (riemann-rcfn-refinement p2 p3)))))

(defthm riemann-rcfn-cons
  (implies (consp p)
           (equal (riemann-rcfn (cons a p))
                  (+ (* (- (car p) a)
                        (rcfn (car p)))
                     (riemann-rcfn p)))))

(defthm riemann-rcfn-refinement-cdr-2
  (implies (and (<= a (car p1))
                (< (car p2) a)
                (partitionp p1)
                (partitionp p2))
           (equal (riemann-rcfn-refinement p1 (cdr p2))
                  (riemann-rcfn-refinement p1 p2))))

(defthm partitionp-forward-to-consp
  (implies (partitionp x)
           (consp x))
  :rule-classes :forward-chaining)

(defthm refinement-p-forward-to-member
  (implies (and (refinement-p p1 p2)
                (consp p2))
           (member (car p2) p1))
  :rule-classes :forward-chaining)

(defthm partitionp-member-rewrite
  (implies (and (partitionp p)
                (member a p))
           (partitionp (member a p))))

;;; Originally used in i-small-maxlist-abslist-difflist-maps.lisp --
;;; can it be made a type prescription rule instead?

(defthm maxlist-nonnegative
  (not (< (maxlist x) 0)))

(defthm realp-standard-part-maxlist
  (implies (real-listp x)
           (realp (standard-part (maxlist x)))))

;;; Originally proved in integral-rcfn-equal-if-i-close.lisp,
;;; refinement-makes-i-small-change.lisp, and
;;; riemann-sum-approximates-integral-1.lisp --
;;; !! Shouldn't this be a type-prescription rule?
(defthm realp-riemann-rcfn
  (implies (partitionp p)
           (realp (riemann-rcfn p))))

(defthm member-index
  (implies (and (<= 0 index)
                (< index (len p)))
           (member (nth index p) p)))

(defthm member-cdr-member-implies-member
  (implies (member a (cdr (member b x)))
           (member a x))
  :rule-classes :forward-chaining)

;;; !! Consider making this a :forward-chaining rule.  It was
;;; originally proved in map-rcfn-refinement-cdr-co-member.lisp.
(defthm member-cadr-of-refinement
  (implies (and (refinement-p p1 p2)
                (member a p2))
           (member a p1)))

(defthm nth-index-abslist
  (equal (nth index (abslist x))
         (abs (nth index x))))

(defthm nth-index-difflist
  (implies (and (equal (len x) (len y)) ; appears to be necessary
                (<= 0 index)
                (< index (len x)))
           (equal (nth index (difflist x y))
                  (- (nth index x) (nth index y)))))

(defthm realp-mesh
  (implies (partitionp p)
           (realp (mesh p)))
  :rule-classes :type-prescription)

(defthm mesh-positive
  (implies (partitionp p)
           (<= 0 (mesh p)))
  :rule-classes :type-prescription)

(defthm abs-of-nonnegative
  (implies (<= 0 x)
           (equal (abs x) x)))

(defthm real-listp-map-times
  (implies (and (real-listp x)
                (real-listp y))
           (real-listp (map-times x y))))

(defthm realp-riemann-rcfn-refinement
  (implies (strong-refinement-p p1 p2)
           (realp (riemann-rcfn-refinement p1 p2)))
  :hints (("Goal" :in-theory (disable dotprod))))

(defthm realp-span
  (implies (partitionp p)
           (realp (span p)))
  :rule-classes :type-prescription)

(defthm partitionp-implies-first-less-than-second
  (implies (and (partitionp p)
                (consp (cdr p)))
           (< (car p) (cadr p)))
  :rule-classes :forward-chaining)

(defthm partitionp-append
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car p2)))
           (partitionp (append p1 (cdr p2)))))

(defthm mesh-append
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car p2)))
           (equal (mesh (append p1 (cdr p2)))
                  (max (mesh p1) (mesh p2)))))

;;; The following three rules were first proved in
;;; refinement-makes-i-small-change-1.lisp but as equalities and
;;; stored as rewrite rules instead.  Rather than hang rewrite rules
;;; on consp (which may cause inefficiencies in the rewriter), these
;;; rules are formulated here as :type-prescription rules.

(defthm consp-abslist
  (implies (consp x)
           (consp (abslist x)))
  :rule-classes :type-prescription)

(defthm consp-difflist
  (implies (consp x)
           (consp (difflist x y)))
  :rule-classes :type-prescription)

(defthm consp-map-rcfn
  (implies (consp x)
           (consp (map-rcfn x)))
  :rule-classes :type-prescription)


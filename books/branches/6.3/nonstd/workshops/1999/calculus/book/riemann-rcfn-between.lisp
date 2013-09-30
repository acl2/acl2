(in-package "ACL2")

;;; The following deflabel is used in the proof of
;;; riemann-rcfn-between.  The approach was originally to define a
;;; theory by disabling rules that originally got in the way of that
;;; proof; see riemann-rcfn-between-theory below.  However, when later
;;; I added partitionp-make-partition-forward, the proof was
;;; destroyed.  Rather than adding this lemma to the list of disables
;;; in riemann-rcfn-between-theory, I have chosen to enable exactly
;;; what is needed in the proof of riemann-rcfn-between.
(deflabel start-of-riemann-rcfn-between)

(include-book "riemann-defuns")
(include-book "make-partition")
(local (include-book "riemann-lemmas"))
(local (include-book "integral-rcfn-lemmas"))
(local (include-book "nsa-lemmas"))
(include-book "max-and-min-attained")

(in-theory (disable min-x-rec max-x-rec))

#|
;;; OBSOLETE deftheory -- see comment at top of file.
;;; Set up the theory for the proof of riemann-rcfn-between, so that
;;; we can prove riemann-rcfn-upper-bound and riemann-rcfn-lower-bound
;;; in any manner we choose to employ.
(deftheory riemann-rcfn-between-theory
  (disable riemann-rcfn
           make-partition
           distributivity
           functional-commutativity-of-minus-*-right
           commutativity-of-*
           commutativity-of-+))
|#

(encapsulate
 ()
 (local (include-book "riemann-rcfn-upper-bound"))

 (defthm riemann-rcfn-upper-bound
   (implies (partitionp p)
            (let ((a (car p))
                  (b (car (last p))))
              (<= (riemann-rcfn p)
                  (* (rcfn (max-x-rec p))
                     (- b a)))))
   :rule-classes nil))

(encapsulate
 ()
 (local (include-book "riemann-rcfn-lower-bound"))

 (defthm riemann-rcfn-lower-bound
   (implies (partitionp p)
            (let ((a (car p))
                  (b (car (last p))))
              (>= (riemann-rcfn p)
                  (* (rcfn (min-x-rec p))
                     (- b a)))))
   :rule-classes nil))

(defthm riemann-rcfn-between
  (implies (and (realp a)
                (realp b)
                (< a b))
           (let ((p (make-partition a b (i-large-integer))))
             (between (riemann-rcfn p)
                      (* (rcfn (min-x-rec p))
                         (- b a))
                      (* (rcfn (max-x-rec p))
                         (- b a)))))
  :hints (("Goal"
           :use
           (
            (:instance
             riemann-rcfn-upper-bound
             (p (make-partition a b (i-large-integer))))
            (:instance
             riemann-rcfn-lower-bound
             (p (make-partition a b (i-large-integer))))
            )
           :in-theory (union-theories '(car-last-make-partition
                                        car-make-partition
                                        partitionp-make-partition
                                        between)
                                      (current-theory 'start-of-riemann-rcfn-between))))
  :rule-classes nil)

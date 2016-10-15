(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()
 (local (include-book "riemann-bound"))
 (defthm riemann-bound
  (implies (strong-refinement-p p1 p2)
           (<= (abs (- (riemann-rcfn p1)
                       (riemann-rcfn-refinement p1 p2)))
               (abs (* (span p1)
                       (maxlist
                        (abslist
                         (difflist
                          (map-rcfn p1)
                          (map-rcfn-refinement p1 p2))))))))))

(encapsulate
 ()
 (local (include-book "refinement-makes-i-small-change-1"))
 (defthm refinement-makes-i-small-change-1
   (implies (and (strong-refinement-p p1 p2)
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2)))
            (i-small (* (span p1)
                        (maxlist
                         (abslist
                          (difflist
                           (map-rcfn p1)
                           (map-rcfn-refinement p1 p2)))))))))

(defthm first-not-greater-than-last-for-partitions-alternate
  (implies (and (equal (last p1) (last p2))
                (partitionp p1)
                (partitionp p2))
           (not (< (car (last p2)) (car p1))))
  :rule-classes
  (:forward-chaining :linear))

(defthm realp-car-map-rcfn-refinement
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1))
                       (car (last p2))))
           (realp (car (map-rcfn-refinement p1 p2)))))

(defthm last-is-list-car
  (implies (and (true-listp x)
                (consp x))
           (equal (last x)
                  (list (car (last x)))))
  :rule-classes nil)

(defthm equal-last-reduces-to-equal-car-last
  (implies (and (true-listp x)
                (consp x)
                (true-listp y)
                (consp y))
           (iff (equal (last x) (last y))
                (equal (car (last x)) (car (last y)))))
  :hints (("Goal" :use
           (last-is-list-car
            (:instance last-is-list-car
                       (x y))))))

(defthm refinement-makes-i-small-change-2
  (implies (and (strong-refinement-p p1 p2)
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-small (- (riemann-rcfn p1)
                       (riemann-rcfn-refinement p1 p2))))
  :hints (("Goal"
           :use
           ((:instance small-if-<-small
                       (x (* (span p1)
                             (maxlist
                              (abslist
                               (difflist
                                (map-rcfn p1)
                                (map-rcfn-refinement p1 p2))))))
                       (y (- (riemann-rcfn p1)
                             (riemann-rcfn-refinement p1 p2)))))
           :in-theory (disable mesh
                               maxlist abslist difflist refinement-p
                               map-rcfn map-rcfn-refinement
                               dotprod span small-if-<-small abs
                               riemann-rcfn-refinement riemann-rcfn
                               ;; I did the proof in the proof-builder
                               ;; without the following.
                               ;; Unfortunately it throws off the
                               ;; automatic proof unless I disable it.
                               small-<-non-small)))
  :rule-classes nil)

(encapsulate
 ()
 (local (include-book "riemann-rcfn-refinement-is-riemann-rcfn"))
 (defthm riemann-rcfn-refinement-is-riemann-rcfn
   (implies (strong-refinement-p p1 p2)
            (equal (riemann-rcfn-refinement p1 p2)
                   (riemann-rcfn p2)))))

(defthm refinement-makes-i-small-change
  (implies (and (strong-refinement-p p1 p2)
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-small (- (riemann-rcfn p1)
                       (riemann-rcfn p2))))
  :hints (("Goal" :use refinement-makes-i-small-change-2)))

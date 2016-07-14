(in-package "ACL2")

(include-book "riemann-lemmas" :load-compiled-file nil)

(local
 (defthm riemann-bound-lemma-1
   (implies
    (and
     (realp diff)
     (<= 0 diff)
     (realp maxlist)
     (realp maxlist-bigger)
     (<= 0 maxlist)
     (<= maxlist maxlist-bigger))
    (<= (* diff maxlist) (* diff maxlist-bigger)))
   :rule-classes nil))

(local
 (defthm riemann-bound-lemma-2
   (implies
    (and
     (consp (cdr p1))
     (partitionp p1)
     (partitionp p2)
     (equal (car (last p1)) (car (last p2))))
    (<= (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                    (map-rcfn-refinement (cdr p1) p2))))
        (maxlist (abslist (difflist (map-rcfn p1)
                                    (map-rcfn-refinement p1 p2))))))))

(local
 (defthm riemann-bound-lemma-3
   (implies
    (and
     (consp (cdr p1))
     (partitionp p1)
     (partitionp p2)
     (equal (car (last p1)) (car (last p2))))
    (<= (+
         (- (* (car p1)
               (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                           (map-rcfn-refinement (cdr p1) p2))))))
         (* (car (last p2))
            (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                        (map-rcfn-refinement (cdr p1) p2))))))
        (+ (- (* (car p1)
                 (maxlist (abslist (difflist (map-rcfn p1)
                                             (map-rcfn-refinement p1 p2))))))
           (* (car (last p2))
              (maxlist (abslist (difflist (map-rcfn p1)
                                          (map-rcfn-refinement p1 p2))))))))
   :hints (("Goal"
            :use
            ((:instance riemann-bound-lemma-1
                        (diff (- (car (last p2)) (car p1)))
                        (maxlist (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                                             (map-rcfn-refinement (cdr p1)
                                                                                  p2)))))
                        (maxlist-bigger (maxlist (abslist (difflist (map-rcfn p1)
                                                                    (map-rcfn-refinement p1 p2)))))))
            :in-theory
            (disable maxlist mesh dotprod map-rcfn map-rcfn-refinement
                     deltas abslist difflist partitionp refinement-p
                     abs dot-prod-bounded)))
   :rule-classes nil))

(local
 (defthm riemann-bound-lemma-4
   (implies
    (and
     (consp (cdr p1))
     (realp abs)
     (<= 0 abs)
     (<=
      abs
      (+
       (- (* (car p1)
             (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                         (map-rcfn-refinement (cdr p1) p2))))))
       (* (car (last p2))
          (maxlist (abslist (difflist (map-rcfn (cdr p1))
                                      (map-rcfn-refinement (cdr p1) p2)))))))
     (partitionp p1)
     (partitionp p2)
     (equal (car (last p1)) (car (last p2))))
    (<= abs
        (+ (- (* (car p1)
                 (maxlist (abslist (difflist (map-rcfn p1)
                                             (map-rcfn-refinement p1 p2))))))
           (* (car (last p2))
              (maxlist (abslist (difflist (map-rcfn p1)
                                          (map-rcfn-refinement p1 p2))))))))
   :hints (("Goal"
            :use
            (riemann-bound-lemma-3)
            :in-theory
            (disable maxlist mesh dotprod map-rcfn map-rcfn-refinement
                     deltas abslist difflist partitionp refinement-p
                     abs dot-prod-bounded)))))

(defthm riemann-bound-lemma-5
  (implies (and (partitionp p1)
                (partitionp p2)
                (equal (car (last p1)) (car (last p2)))
                (equal (car p1) (car p2))
                (refinement-p p1 p2))
           (<= (abs (- (riemann-rcfn p1)
                       (riemann-rcfn-refinement p1 p2)))
               (* (span p1)
                  (maxlist
                   (abslist
                    (difflist
                     (map-rcfn p1)
                     (map-rcfn-refinement p1 p2)))))))
  :hints (("Goal"
           :in-theory
           (disable maxlist mesh dotprod map-rcfn map-rcfn-refinement
                    deltas abslist difflist partitionp refinement-p
                    abs dot-prod-bounded)
           :use
           ((:instance dot-prod-bounded (x (deltas p1))
                       (y (difflist (map-rcfn (cdr p1))
                                    (map-rcfn-refinement (cdr p1) p2))))))))

(defthm riemann-bound
  (implies (strong-refinement-p p1 p2)
           (<= (abs (- (riemann-rcfn p1)
                       (riemann-rcfn-refinement p1 p2)))
               (abs (* (span p1)
                       (maxlist
                        (abslist
                         (difflist
                          (map-rcfn p1)
                          (map-rcfn-refinement p1 p2))))))))
  :hints (("Goal" :use riemann-bound-lemma-5
           :in-theory
           (union-theories '(strong-refinement-p partitionp2
                                                 partitionp
                                                 partitionp-forward-to-true-listp
                                                 ;paritionp-forward-to-consp
                                                 )
                           ;; The following list of rules was derived
                           ;; by doing the proof in the proof-builder.
                           '((:DEFINITION NOT)
                             (:FORWARD-CHAINING PARTITIONP-FORWARD-TO-REALP-CAR)
                             (:FORWARD-CHAINING REALP-LAST-ELEMENT-OF-PARTITION)
                             (:REWRITE REALP-MAXLIST)
                             (:REWRITE REAL-LISTP-ABSLIST)
                             (:REWRITE REAL-LISTP-DIFFLIST)
                             (:REWRITE REAL-LISTP-MAP-RCFN-REFINEMENT)
                             (:REWRITE REAL-LISTP-MAP-RCFN)
                             (:TYPE-PRESCRIPTION REAL-LISTP)
                             (:FORWARD-CHAINING PARTITIONP-FORWARD-TO-REAL-LISTP)
                             (:TYPE-PRESCRIPTION DIFFLIST)
                             (:REWRITE <-+-NEGATIVE-0-1)
                             (:FORWARD-CHAINING FIRST-NOT-GREATER-THAN-LAST-FOR-PARTITIONS)
                             (:TYPE-PRESCRIPTION PARTITIONP)
                             (:DEFINITION SPAN)
                             (:REWRITE COMMUTATIVITY-OF-+)
                             (:DEFINITION IMPLIES)
                             (:DEFINITION STRONG-REFINEMENT-P)
                             (:DEFINITION ABS)
                             (:LINEAR MAXLIST-ABSLIST-NONNEGATIVE))))))

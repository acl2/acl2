(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

(encapsulate
 ()
 (local (include-book "maxlist-abslist-difflist-maps-lt"))
 (defthm maxlist-abslist-difflist-maps-lt
   (implies (and (strong-refinement-p p1 p2)
                 (consp (cdr p1))
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2))
                 (standard-numberp r)
                 (realp r)
                 (< 0 r))
            (< (maxlist
                (abslist
                 (difflist
                  (map-rcfn p1)
                  (map-rcfn-refinement p1 p2))))
               r))
   :rule-classes nil))

(defthm acl2-numberp-maxlist-abslist-difflist
  (acl2-numberp (maxlist (abslist (difflist x y)))))

(defthm i-limited-maxlist-abslist-difflist-maps
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-limited (maxlist
                       (abslist
                        (difflist
                         (map-rcfn p1)
                         (map-rcfn-refinement p1 p2))))))
  :hints (("Goal" :in-theory
           (disable maxlist abslist difflist map-rcfn map-rcfn-refinement
                    partitionp refinement-p i-small large-if->-large)
           :use
           ((:instance large-if->-large
                       (y 1)
                       (x (maxlist
                           (abslist
                            (difflist
                             (map-rcfn p1)
                             (map-rcfn-refinement p1 p2))))))
            (:instance maxlist-abslist-difflist-maps-lt (r 1))))))

(defthm standard-part-maxlist-nonnegative
  (implies (real-listp x)
           (<= 0 (standard-part (maxlist x))))
  :rule-classes :linear)

(defthm realp-maxlist-abslist-difflist
  (implies
   (and
    (partitionp p1)
    (partitionp p2)
    (equal (car (last p1)) (car (last p2))))
   (realp (maxlist (abslist (difflist (map-rcfn p1)
                                      (map-rcfn-refinement p1 p2)))))))

(defthm standard-part-maxlist-nonnegative-alternate
  (implies (real-listp x)
           (equal (< 0 (standard-part (maxlist x)))
                  (not (equal (standard-part (maxlist x)) 0)))))

(encapsulate
 ()
 (local (include-book "two-times-r-is-not-less-than-standard-part"))
 (defthm two-times-r-is-not-less-than-standard-part
   (implies (and (realp r)
                 (<= 0 r))
            (not (< (* 2 r) (standard-part r))))))

(defthm i-small-maxlist-abslist-difflist-maps-consp-cdr
  (implies (and (strong-refinement-p p1 p2)
                (consp (cdr p1))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-small (maxlist
                     (abslist
                      (difflist
                       (map-rcfn p1)
                       (map-rcfn-refinement p1 p2))))))
  :hints (("Goal" :use
           ((:instance maxlist-abslist-difflist-maps-lt
                       (r (* 1/2 (standard-part
                                  (maxlist
                                   (abslist
                                    (difflist
                                     (map-rcfn p1)
                                     (map-rcfn-refinement p1 p2)))))))))
           :in-theory
           (disable maxlist abslist difflist map-rcfn map-rcfn-refinement
                    partitionp refinement-p i-small abs))))

(defthm i-small-maxlist-abslist-difflist-maps-degenerate
  (implies (and (strong-refinement-p p1 p2)
                (not (consp (cdr p1)))
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-small (maxlist
                     (abslist
                      (difflist
                       (map-rcfn p1)
                       (map-rcfn-refinement p1 p2)))))))

(defthm i-small-maxlist-abslist-difflist-maps
  (implies (and (strong-refinement-p p1 p2)
                (standard-numberp (car p1))
                (standard-numberp (car (last p1)))
                (i-small (mesh p2)))
           (i-small (maxlist
                     (abslist
                      (difflist
                       (map-rcfn p1)
                       (map-rcfn-refinement p1 p2))))))
  :hints (("Goal" :cases ((consp (cdr p1)))
           :in-theory (disable strong-refinement-p
                               mesh
                               maxlist
                               abslist
                               difflist
                               map-rcfn
                               map-rcfn-refinement))))

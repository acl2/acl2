(in-package "ACL2")

(include-book "riemann-defuns")
(include-book "riemann-lemmas")
(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

;;; The following needs nsa-lemmas.
(defthm i-limited-span
  (implies (and (standard-numberp (car p))
                (standard-numberp (car (last p))))
           (i-limited (span p))))

(in-theory (disable span))

(encapsulate
 ()
 (local (include-book "i-small-maxlist-abslist-difflist-maps"))
 (defthm i-small-maxlist-abslist-difflist-maps
   (implies (and (strong-refinement-p p1 p2)
                 (standard-numberp (car p1))
                 (standard-numberp (car (last p1)))
                 (i-small (mesh p2)))
            (i-small (maxlist
                      (abslist
                       (difflist
                        (map-rcfn p1)
                        (map-rcfn-refinement p1 p2))))))))

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
                          (map-rcfn-refinement p1 p2))))))))

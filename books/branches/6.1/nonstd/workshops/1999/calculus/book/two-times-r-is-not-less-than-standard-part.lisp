(in-package "ACL2")

(include-book "nsa-lemmas")
; Book .../nonstd/nsa/realp was included in an early version of the proof.
(include-book "top-with-meta")

(defthm <-*-2
  (iff (< (* 2 r) x)
       (< r (- x r)))
  :rule-classes
  ((:rewrite :corollary
             (implies (syntaxp (not (quotep r)))
                      (equal (< (* 2 r) x)
                             (< r (- x r)))))))

(include-book "defaxioms")

(defthm two-times-r-is-not-less-than-standard-part
  (implies (and (realp r)
                (<= 0 r))
           (not (< (* 2 r) (standard-part r))))
  :hints (("Goal" :in-theory (enable i-small)
           :use
           ((:instance small-if-<-small
                       (x (+ (- r) (standard-part r)))
                       (y r))))))

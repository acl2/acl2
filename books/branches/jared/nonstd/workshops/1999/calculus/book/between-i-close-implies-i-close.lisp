(in-package "ACL2")

(include-book "nsa-lemmas")
(include-book "top-with-meta")
(include-book "defaxioms")
; Book .../nonstd/nsa/realp was included in an early version of the proof.

;;; This is all we need from between-limited-implies-limited.lisp.
(defun between (x a b)
  (if (< a b)
      (and (<= a x) (<= x b))
    (and (<= b x) (<= x a))))

(defthm i-close-squeeze-1
   (implies (and (between z x y)
                 (realp z)
                 (realp x)
                 (realp y)
                 (i-close x y))
            (i-close x z))
   :hints (("Goal" :in-theory (enable i-close)))
   :rule-classes :forward-chaining)

;;; This second one is not needed for the proof of
;;; between-i-close-implies-i-close, but it is potentially useful
;;; nonetheless.
(defthm i-close-squeeze-2
   (implies (and (between z x y)
                 (realp z)
                 (realp x)
                 (realp y)
                 (i-close x y))
            (i-close y z))
   :hints (("Goal"
            :in-theory
            (union-theories '(i-close)
                            (disable small-if-<-small))
            :use
            ((:instance small-if-<-small
                        (x (+ x (- y)))
                        (y (+ y (- z)))))))
   :rule-classes :forward-chaining)

(in-theory (disable between))

(defthm between-i-close-implies-i-close
   (implies (and (realp z)
                 (realp x)
                 (realp y)
                 (realp r)
                 (between z x y)
                 (i-close x r)
                 (i-close y r))
            (i-close z r))
   :hints (("Goal"
            :in-theory (union-theories '(i-close-symmetric)
                                       (disable i-close-transitive))
            :use
            ((:instance
              i-close-transitive
              (x x)
              (y r)
              (z y))
             (:instance
              i-close-transitive
              (x r)
              (y x)
              (z z)))))
   :rule-classes nil)



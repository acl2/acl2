(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(include-book "centaur/gl/gl" :dir :system)

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;; From bits.lisp:

(defund bits (x i j)
    (declare (xargs :guard (and (integerp x)
                                (integerp i)
                                (integerp j))
                    :guard-hints (("Goal" :in-theory (e/d
                                                      (bits-mbe-lemma-subgoal-1
                                                       ash
                                                       bits-mbe-lemma-subgoal-2) ())))))
    (mbe :logic (if (or (not (integerp i))
                        (not (integerp j)))
                    0
                  (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
         :exec  (if (< i j)
                    0
                  (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x) (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;;;**********************************************************************

(defthm bits-for-gl
  (equal (bits x i j)
         (if (and (integerp x)
                  (integerp i)
                  (integerp j))
             (if (< i j)
                 0
               (logand (ash x (- j))
                       (1- (ash 1 (1+ (- i j))))))
           (let ((msg (cw "WARNING: guard violation for the function BITS during a GL proof.~%")))
             (declare (ignore msg))
             (if (or (not (integerp i))
                     (not (integerp j)))
                 0
               (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j)))))))
  :rule-classes ())

(gl::set-preferred-def bits bits-for-gl)

(defthm bitn-for-gl
  (equal (bitn x n)
         (if (and (integerp x)
                  (integerp n))
             (if (< n 0)
                 0
               (if (logbitp n x) 1 0))
           (let ((msg (cw "WARNING: guard violation for the function BITN during a GL proof.~%")))
             (declare (ignore msg))
             (if (not (integerp n))
                 0
               (fl (/ (mod x (expt 2 (1+ n))) (expt 2 n)))))))
  :rule-classes ())

(gl::set-preferred-def bitn bitn-for-gl)

(defthm binary-cat-for-gl
   (equal (binary-cat x m y n)
          (if (and (natp m)
                   (natp n))
              (logior (ash (BITS X (1- M) 0) n)
                      (BITS Y (1- N) 0))
            0))
   :rule-classes ())

(gl::set-preferred-def binary-cat binary-cat-for-gl)

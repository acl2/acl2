(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(include-book "centaur/gl/gl" :dir :system)

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")
(include-book "rac")

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

(defthm expo-for-gl
  (equal (expo x)
         (if (integerp x)
	     (if (= x 0)
	         0
	       (1- (integer-length (abs x))))
           (let ((msg (cw "WARNING: guard violation for the function EXPO during a GL proof.~%")))
             (declare (ignore msg))
             (expo x))))
  :rule-classes ())

(gl::set-preferred-def expo expo-for-gl)

(gl::def-gl-rewrite ag-of-as
  (equal (ag a (as wa v r))
         (if (equal a wa) v (ag a r))))

(gl::gl-set-uninterpreted ag)

(gl::gl-set-uninterpreted as)


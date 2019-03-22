(in-package "RTL")

(include-book "centaur/gl/gl" :dir :system)
(include-book "definitions")
(local (include-book "bits"))
(local (include-book "log"))
(local (include-book "float"))
(include-book "rac")

(local (include-book "basic"))
(local (include-book "arithmetic-5/top" :dir :system))

;;;**********************************************************************

(defrule bits-for-gl
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
  :enable (bits bits-exec)
  :disable (ash mod)
  :use bits-mbe-lemma
  :rule-classes ())

;; Tell GL to actually use our definition
(gl::set-preferred-def bits bits-for-gl)

(defrule bitn-for-gl
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
  :enable (bitn bitn-exec)
  :disable (bits-n-n-rewrite ash mod bits floor)
  :cases ((and (integerp x) (integerp n)))
  :hints (
    ("subgoal 2" :in-theory (enable bits))
    ("subgoal 1" :use bitn-mbe-lemma))
  :rule-classes ())

(gl::set-preferred-def bitn bitn-for-gl)

(defrule binary-cat-for-gl
   (equal (binary-cat x m y n)
          (if (and (natp m)
                   (natp n))
              (logior (ash (bits x (1- m) 0) n)
                      (bits y (1- n) 0))
            0))
   :enable (binary-cat logior-expt-cor ash)
   :disable (logior-commutative acl2::|(logior y x)|)
   :rule-classes ())

(gl::set-preferred-def binary-cat binary-cat-for-gl)

(defrule expo-for-gl
  (equal (expo x)
         (if (integerp x)
	     (if (= x 0)
	         0
	       (1- (integer-length (abs x))))
           (let ((msg (cw "WARNING: guard violation for the function EXPO during a GL proof.~%")))
             (declare (ignore msg))
             (expo x))))
  :prep-books ((include-book "centaur/bitops/integer-length" :dir :system))
  :use (:instance expo-unique (n (1- (integer-length (abs x)))))
  :rule-classes ())

(gl::set-preferred-def expo expo-for-gl)

(gl::gl-set-uninterpreted ag)

(gl::gl-set-uninterpreted as)

(gl::def-gl-rewrite ag-of-as
  (equal (ag a (as wa v r))
         (if (equal a wa) v (ag a r))))

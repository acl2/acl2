;;;;; Some functions for mathematical vectors.
;;;;;
;;;;; Includes functions for creating zero vector, vector addition, negation,
;;;;; subtraction, multiplication by scalar, and dot product and basic
;;;;; theorems about those functions.

(in-package "ACL2")

(include-book "../../../../arithmetic/top-with-meta")

;;; Returns true if v is a true-list of numbers.
(defun mvectorp (v)
  (declare (xargs :verify-guards t))
  (if (consp v)
      (and (acl2-numberp (car v))
           (mvectorp (cdr v)))
    (eq v nil)))

(defthm vector-is-true-list
  (implies (mvectorp l)
	   (true-listp l))
  :rule-classes :compound-recognizer)

;;;; Zero vector and basic theorems.

;;; Returns a list of length len of zeros - a zero vector.
(defun vzero (len)
  (declare (xargs :guard (and (integerp len) (<= 0 len))))
  (if (zp len)
      nil
    (cons 0 (vzero (1- len)))))

;;; Theorem proving the zero vector is a vector.
(defthm mvectorp-vzero
  (mvectorp (vzero n))
  :rule-classes (:rewrite :type-prescription))

(defthm consp-vzero
  (equal (consp (vzero n))
         (not (zp n))))

;;; Length of zero vector equals its argument.
(defthm len-vzero
  (equal (len (vzero n))
         (nfix n)))

;;;; Vector addition and basic properties.

;;; v+ (vector addition) should take two lists of equal length.
(defmacro v+-guard (k l)
  `(and (mvectorp ,k)
        (mvectorp ,l)
        (equal (len ,k) (len ,l))))

;;; Returns the sum of two vectors -  Recursively iterates down each argument.
(defun v+ (k l)
  (declare (xargs :guard (v+-guard k l)))
  (if (endp k)
      nil
    (cons (+ (car k) (car l))
          (v+ (cdr k) (cdr l)))))

(defthm mvectorp-v+
  (mvectorp (v+ k l)))

(defthm consp-v+
  (equal (consp (v+ k l))
         (consp k)))

(defthm len-v+
  (equal (len (v+ k l))
         (len k)))

;;;; Vector addition is associative and commutative.
(defthm v+-assoc
  (implies (<= (len j) (len k))
           (equal (v+ (v+ j k) l)
                  (v+ j (v+ k l)))))

(defthm v+-assoc2
  (implies (equal (len j) (len k))
           (equal (v+ j (v+ k l))
                  (v+ k (v+ j l)))))

(defthm v+-comm
  (implies (equal (len k) (len l))
           (equal (v+ k l)
                  (v+ l k))))

;;;; Adding the zero vector to a vector does not affect the vector if
;;;; the lengths are the same.

(defthm v+-nil
  (implies (mvectorp v)
           (equal (v+ v nil) v)))

(defthm v+-zero-left
  (implies (and (mvectorp v)
                (equal (len v) n))
           (equal (v+ (vzero n) v) v)))

(defthm v+zero-right
  (implies (and (mvectorp v)
                (equal (len v) n))
           (equal (v+ v (vzero n)) v))
  :hints (("Goal" :induct (nth n v))))

(defthm nth-v+
  (equal (nth i (v+ u v))
         (if (< (nfix i) (len u))
             (+ (nth i u) (nth i v))
           nil))
  :hints (("Goal" :induct (and (nth i u)
                               (v+ u v)))))

;;;; Multiplication of a vector by a scalar.

(defun sv* (s v)
  (declare (xargs :guard (and (acl2-numberp s) (mvectorp v))))
  (if (endp v)
      nil
    (cons (* s (car v))
          (sv* s (cdr v)))))

(defthm vector-sv*
  (mvectorp (sv* s v)))

(defthm len-sv*
  (equal (len (sv* s v))
         (len v)))

(defthm consp-sv*
  (equal (consp (sv* s v))
         (consp v)))

;;;; Multiplying by zero results in a zero vector.
(defthm sv*-0-left
  (equal (sv* 0 v)
         (vzero (len v))))

(defthm sv*-0-right
  (equal (sv* s (vzero n))
         (vzero n)))

;;; Multiplying by 1 does not change a vector.
(defthm sv*-1
  (implies (mvectorp v)
           (equal (sv* 1 v) v)))

;;; Collect 2 scalar multiplications into a single multiplication.
(defthm sv*-sv*
  (equal (sv* a (sv* b l))
         (sv* (* a b) l)))

;;;; Collect vector addition where one vector is a scalar multiple of
;;;; the other into a single scalar multiplication.
(defthm sv*-collect
  (equal (v+ v v)
         (sv* 2 v)))

(defthm sv*-collect-left
  (equal (v+ (sv* a v) v)
         (sv* (1+ a) v)))

(defthm sv*-collect-right
  (equal (v+ v (sv* a v))
         (sv* (1+ a) v)))

(defthm sv*-collect-both
  (equal (v+ (sv* a v) (sv* b v))
         (sv* (+ a b) v)))

(local
 (defthm sv*-dist-nil
   (equal (sv* a (v+ u nil))
          (sv* a u))))

(defthm sv*-dist
  (equal (sv* a (v+ u v))
         (v+ (sv* a u) (sv* a v))))

(defthm nth-sv*
  (equal (nth i (sv* a v))
         (if (< (nfix i) (len v))
             (* a (nth i v))
           nil)))

;;; Define v- to negate with a single argument and subtract with binary
;;; arguments.
(defmacro v- (l &optional (k 'nil binary-casep))
  (if binary-casep
      `(v+ ,l (sv* -1 ,k))
    `(sv* -1 ,l)))

;;;; Dot product function and basic theorems.
(defun dot* (u v)
  (declare (xargs :guard (and (mvectorp u)
                              (mvectorp v)
                              (equal (len u) (len v)))))
  (if (endp u)
      0
    (+ (* (car u) (car v))
       (dot* (cdr u) (cdr v)))))

(defthm numberp-dot*
  (acl2-numberp (dot* l k))
  :rule-classes :type-prescription)

(defthm dot*-nil-left
  (equal (dot* l nil) 0))

(defthm dot*-nil-right
  (equal (dot* nil l) 0))

(defthm dot*-comm
  (equal (dot* l k)
         (dot* k l)))

;;; This is used for generating the induction.  It seems like an easier
;;; way to do this should exist, but I do not yet understand the
;;; induction heuristics.
(local
 (defun zero-dot*-recursion (n l)
   (if (zp n)
       l
     (zero-dot*-recursion (1- n) (cdr l)))))

(defthm dot*-zero-left
  (equal (dot* (vzero n) l) 0)
  :hints (("Goal" :induct (zero-dot*-recursion n l))))

(defthm dot*-zero-right
  (equal (dot* l (vzero n)) 0)
  :hints (("Goal" :induct (nth n l))))

;;; Distribute the dot product of vector addition.
(defthm dist-dot*-v+-left
  (implies (equal (len j) (len k))
           (equal (dot* (v+ k l) j)
                  (+ (dot* k j) (dot* l j)))))

(defthm dist-dot*-v+-right
  (implies (equal (len j) (len k))
           (equal (dot* j (v+ k l))
                  (+ (dot* j k) (dot* j l)))))

;;; Distribute the dot production of scalar vector multiplication.
(defthm dot*-sv*-left
  (equal (dot* (sv* a l) k)
         (* a (dot* l k))))

(defthm dot*-sv*-right
  (equal (dot* l (sv* a k))
         (* a (dot* l k))))


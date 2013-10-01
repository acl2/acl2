(in-package "ACL2")

;This book contains arithmetic hacks removed from basic.lisp

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(local (include-book "fp2"))

(defthm delta1-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (* y d) (* (- x y) d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance *-weakly-monotonic (x d) (y+ (- x y)))))))


(defthm delta1-a
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (>= (- x (* y (+ 1 d)))
		 (* (- x y) (- 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta1-b
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= y 0)
		  (>= x (+ y y))
		  (>= d 0))
	     (<= (- x (* y (- 1 d)))
		 (* (- x y) (+ 1 d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance delta1-1)))))

(defthm delta2
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp d)
		  (>= (* x d) 0))
	     (>= (+ x (* y (- 1 d)))
		 (* (+ x y) (- 1 d))))
  :rule-classes ())

(defthm natp-
    (implies (and (natp x)
		  (natp y)
		  (>= x y))
	     (natp (+ x (* -1 y))))
  :hints (("Goal" :in-theory (enable natp))))

;disable, since we intend to keep natp enabled?
(defthmd natp>=0
  (implies (natp x)
           (>= x 0)))
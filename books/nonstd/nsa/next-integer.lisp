;;; In many of the theories developed in this section, we need to
;;; refer to an integer greater than x, but not too much bigger than
;;; x.  That's almost the same function as "ceiling", except ceiling
;;; can sometimes returns x itself.

;;; In this book, we build a theory of a function that meets the
;;; needed spec, namely "next-integer".


(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/abs" :dir :system))

(include-book "nsa")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; Next-integer is defined as 1+floor.  Note, this is not the same as
;; "ceiling", because they differ on the integers (and only on the
;; integers).

(defun next-integer (x)
  (1+ (floor1 x)))

;; We show that next-integer(x) isn't much bigger than x -- in fact,
;; it's no larger than x+1.

(defthm next-integer-<=-x+1
  (implies (realp x)
	   (not (< (+ 1 x) (next-integer x))))
  :otf-flg t
  :rule-classes (:linear :rewrite))

;; On the other hand, we show that x is always smaller than
;; next-integer(x)

(defthm x-<-next-integer
  (implies (realp x)
	   (< x (next-integer x)))
  :rule-classes (:linear :rewrite))

;; A simple consequence is that next-integer(abs(x)) must be
;; non-negative, since abs(x) is non-negative....

(defthm next-integer-positive
  (implies (realp x)
	   (not (< (next-integer (abs x)) 0)))
  :rule-classes (:linear :rewrite))

;; ...and thinking just a little harder, we see that
;; next-integer(abs(x)) can't be 0, so it must always be positive.

(defthm next-integer-positive-stronger
  (implies (realp x)
	   (< 0 (next-integer (abs x))))
  :rule-classes (:linear :rewrite))

(in-theory (disable next-integer))

;; Now we prove a formal result claiming that next-integer preserves
;; the "limited" scale.  That is, if next-integer(x) is large, then it
;; must be the case that x is large also.

(encapsulate
 ()

 ;; First, if x isn't large, then 1+x is limited, since otherwise we
 ;; would have a least large integer -- a contradiction.

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (not (i-large x)))
	     (i-limited (+ 1 x)))
    :hints (("Goal" :use ((:instance i-limited-plus (x 1) (y x)))
	     :in-theory (disable i-limited-plus)))))

 ;; Moreover, if x is large, so is next-integer(x) (since it's bigger).

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (<= 0 x))
	     (implies (i-large x)
		      (i-large (next-integer x))))))
 ;; Since x+2 is larger than next-integer(x), we can conclude that the
 ;; former is i-large when the latter is i-large.

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (<= 0 x))
	     (implies (i-large (next-integer x))
		      (i-large (+ x 2))))
    :hints (("Goal"
	     :use ((:instance large-if->-large
			      (x (next-integer x))
			      (y (+ x 2))))
	     :in-theory (disable large-if->-large)))))

 ;; In turn, that allows us to conclude that if next-integer(x) is
 ;; i-large, so is x.

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (<= 0 x))
	     (implies (i-large (next-integer x))
		      (i-large x)))
    :hints (("Goal"
	     :use ((:instance limited+large->large
			      (x -2)
			      (y (+ x 2))))
	     :in-theory (disable limited+large->large)))))

 ;; But that means that next-integer(x) is i-large if and only if x is
 ;; i-large!

 (local
  (defthm lemma-5
    (implies (and (realp x)
		  (<= 0 x))
	     (iff (i-large (next-integer x))
		  (i-large x)))
    :hints (("Goal"
	     :use ((:instance lemma-2)
		   (:instance lemma-4))
	     :in-theory nil))))

 ;; And so, we state in our main theorem:

 (defthm large-next-integer
   (implies (and (realp x)
		 (<= 0 x))
	    (equal (i-large (next-integer x))
		   (i-large x)))
   :hints (("Goal"
	    :use ((:instance lemma-5))
	    :in-theory (disable lemma-5))))
 )


; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;
;; prefer-times.lisp
;;


;
;  This is a small theory of rules that eliminate / from equalites and
;  inequalities in favor of *, e.g., x < y/z is rewritten to x*y < z for
;  positive z.  This theory is compatible with the other theories, i.e.,
;  it should not cause looping.
;
;  These rules are not included by default bacause it is not clear
;  that we should prefer x*y < z to x < y/z, or x*y = z to x = y/z';
;  in fact, the whole point of the proofs using these libraries may
;  have to do with a representation involving /.
;
;  So, unless someone provides a convincing reason to the contrary,
;  these rules will remain separate from the rest of the theory.
;
;  Note, however, that in certain cases this theory is just the thing that
;  needs to be ENABLEd to make the proofs work.  Keep it in mind.
;

(in-package "ACL2")

(local (include-book "basic-arithmetic"))

(local (include-book "inequalities"))

(local
 (defthm iff-equal
   (equal (equal (< w x) (< y z))
	  (iff (< w x) (< y z)))))

(defthm equal-*-/-1
  (equal (equal (* (/ x) y) z)
	 (if (equal (fix x) 0)
	     (equal z 0)
	     (and (acl2-numberp z)
		  (equal (fix y) (* x z))))))

(defthm equal-*-/-2
  (equal (equal (* y (/ x)) z)
	 (if (equal (fix x) 0)
	     (equal z 0)
	     (and (acl2-numberp z)
		  (equal (fix y) (* z x))))))

(local
 (defthm times-one
   (implies (acl2-numberp x)
	    (equal (* 1 x)
		   x))))

(local
 (defthm times-minus-one
   (implies (acl2-numberp x)
	    (equal (* -1 x)
		   (- x)))))

(defthm normalize-<-/-to-*-1
  (implies (and (real/rationalp x)
		(real/rationalp y))
	   (equal (< x (/ y))
		  (cond ((< y 0) (< 1 (* x y)))
			((< 0 y) (< (* x y) 1))
			(t (< x 0)))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                        (x x)
                                        (y (/ y))
                                        (z y))
                        (:instance right-cancellation-for-*
                                        (x x)
                                        (y (/ y))
                                        (z y)))
                  :in-theory (disable equal-/))))

(defthm normalize-<-/-to-*-2
  (implies (and (real/rationalp x)
		(real/rationalp y))
		(equal (< (/ y) x)
		       (cond ((< y 0) (< (* x y) 1))
			     ((< 0 y) (< 1 (* x y)))
			     (t (< 0 x)))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                        (x (/ y))
                                        (y x)
                                        (z y))
                        (:instance right-cancellation-for-*
                                        (x (/ y))
                                        (y x)
                                        (z y)))
                  :in-theory (disable equal-/ normalize-<-/-to-*-1))))

(defthm normalize-<-/-to-*-3-1
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z))
	   (equal (< x (* y (/ z)))
		  (cond ((< z 0) (< y (* x z)))
			((< 0 z) (< (* x z) y))
			(t (< x 0)))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                        (x x)
                                        (y (* y (/ z)))
                                        (z z))))))

(defthm normalize-<-/-to-*-3-2
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z))
	   (equal (< x (* (/ z) y))
		  (cond ((< z 0) (< y (* x z)))
			((< 0 z) (< (* x z) y))
			(t (< x 0))))))

(defthm normalize-<-/-to-*-3-3
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z))
	   (equal (< (* y (/ z)) x)
		  (cond ((< z 0) (< (* x z) y))
			((< 0 z) (< y (* x z)))
			(t (< 0 x)))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                        (x (* y (/ z)))
                                        (y x)
                                        (z z)))
                  :in-theory (disable NORMALIZE-<-/-TO-*-3-1))))

(defthm normalize-<-/-to-*-3-4
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z))
	   (equal (< (* (/ z) y) x)
		  (cond ((< z 0) (< (* x z) y))
			((< 0 z) (< y (* x z)))
			(t (< 0 x))))))

(deftheory prefer-*-to-/
  '(equal-*-/-1 equal-*-/-2
    normalize-<-/-to-*-1 normalize-<-/-to-*-2
    normalize-<-/-to-*-3-1 normalize-<-/-to-*-3-2
    normalize-<-/-to-*-3-3 normalize-<-/-to-*-3-4))

(in-theory (disable prefer-*-to-/))

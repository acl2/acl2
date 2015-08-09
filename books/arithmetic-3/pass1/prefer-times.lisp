; See the top-level arithmetic-3 LICENSE file for authorship,
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


(set-default-hints
 '((nonlinearp-default-hint-pass1 stable-under-simplificationp
                                  hist pspv)))


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

(local
 (in-arithmetic-theory '((:rewrite COMMUTATIVITY-OF-*)
			(:REWRITE COMMUTATIVITY-2-OF-*)
			(:REWRITE INVERSE-OF-*)
			(:REWRITE TIMES-ONE)
			(:REWRITE TIMES-MINUS-ONE))))

(defthm normalize-<-/-to-*-1
  (implies (and (rationalp x)
		(rationalp y))
	   (equal (< x (/ y))
		  (cond ((< y 0) (< 1 (* x y)))
			((< 0 y) (< (* x y) 1))
			(t (< x 0))))))

(defthm normalize-<-/-to-*-2
  (implies (and (rationalp x)
		(rationalp y))
		(equal (< (/ y) x)
		       (cond ((< y 0) (< (* x y) 1))
			     ((< 0 y) (< 1 (* x y)))
			     (t (< 0 x))))))

(defthm normalize-<-/-to-*-3-1
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z))
	   (equal (< x (* y (/ z)))
		  (cond ((< z 0) (< y (* x z)))
			((< 0 z) (< (* x z) y))
			(t (< x 0))))))

(defthm normalize-<-/-to-*-3-2
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z))
	   (equal (< x (* (/ z) y))
		  (cond ((< z 0) (< y (* x z)))
			((< 0 z) (< (* x z) y))
			(t (< x 0))))))

(defthm normalize-<-/-to-*-3-3
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z))
	   (equal (< (* y (/ z)) x)
		  (cond ((< z 0) (< (* x z) y))
			((< 0 z) (< y (* x z)))
			(t (< 0 x))))))

(defthm normalize-<-/-to-*-3-4
  (implies (and (rationalp x)
		(rationalp y)
		(rationalp z))
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

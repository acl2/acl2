;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod-helper.lisp
;;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(IN-PACKAGE "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "forcing-types"))

(local
 (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT++ ID STABLE-UNDER-SIMPLIFICATIONP
						 HIST NIL))))




;; Jared added this to speed up the proofs
(local (in-theory (disable not-integerp-type-set-rules
                           mod-x-y-=-x+y
                           simplify-terms-such-as-ax+bx-=-0
                           reduce-additive-constant-equal
                           floor-zero
                           floor-=-x/y
                           simplify-products-gather-exponents-<

                           integerp-mod-1
                           integerp-mod-2
                           integerp-mod-3
                           rationalp-mod
                           )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()
 (local
  (defthm floor-sum-cases-helper-a
    (implies (and (rationalp (/ x z))
		  (rationalp (/ y z)))
	     (<= (floor (+ x y) z)
		 (cond ((not (acl2-numberp z))
			0)
		       ((equal z 0)
			0)
		       ((< 0 z)
			(if (< (+ (mod x z) (mod y z)) z)
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z))))
		       (t
			(if (< z (+ (mod x z) (mod y z)))
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z)))))))
    :hints (("Goal" :in-theory (enable mod)))))

 (local
  (defthm floor-sum-cases-helper-b
    (implies (and (rationalp (/ x z))
		  (rationalp (/ y z)))
	     (<= (cond ((not (acl2-numberp z))
			0)
		       ((equal z 0)
			0)
		       ((< 0 z)
			(if (< (+ (mod x z) (mod y z)) z)
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z))))
		       (t
			(if (< z (+ (mod x z) (mod y z)))
			    (+ (floor x z) (floor y z))
			  (+ 1 (floor x z) (floor y z)))))
		 (floor (+ x y) z)))
    :hints (("Goal" :in-theory (enable mod)))))

 (local
  (in-theory (disable floor-sum-cases-helper-a
		      floor-sum-cases-helper-b)))

 (defthm |(floor (+ x y) z)|
   (implies (and (rationalp (/ x z))
		 (rationalp (/ y z)))
	    (equal (floor (+ x y) z)
		   (cond ((not (acl2-numberp z))
			  0)
			 ((equal z 0)
			  0)
			 ((< 0 z)
			  (if (< (+ (mod x z) (mod y z)) z)
			      (+ (floor x z) (floor y z))
			    (+ 1 (floor x z) (floor y z))))
			 (t
			  (if (< z (+ (mod x z) (mod y z)))
			      (+ (floor x z) (floor y z))
			    (+ 1 (floor x z) (floor y z)))))))
   :hints (("Goal" :use ((:instance floor-sum-cases-helper-a)
			 (:instance floor-sum-cases-helper-b)))))

 )

(defthm |(mod (+ x y) z)|
  (implies (and (rationalp (/ x z))
                (rationalp (/ y z)))
           (equal (mod (+ x y) z)
		  (if (<= 0 z)
		      (if (< (+ (mod x z) (mod y z)) z)
			  (+ (mod x z) (mod y z))
			(+ (mod x z) (mod y z) (- z)))
		    (if (< z (+ (mod x z) (mod y z)))
			(+ (mod x z) (mod y z))
		      (+ (mod x z) (mod y z) (- z))))))
  :hints (("Goal" :in-theory (enable mod))))






;; Jared added this to speed up the proofs
(local (in-theory (e/d (floor-=-x/y)
                       (default-plus-2
                         default-times-2
                         default-plus-1
                         default-times-1
                         reduce-rationalp-*
                         prefer-positive-exponents-scatter-exponents-<-2
                         prefer-positive-exponents-scatter-exponents-<
                         normalize-factors-scatter-exponents
                         integerp-minus-x
                         normalize-terms-such-as-a/a+b-+-b/a+b
                         meta-integerp-correct
                         rationalp-minus-x
                         mod-x-y-=-x-y
                         floor-negative
                         floor-positive))))


(encapsulate
 ()
 (local
  (defthm crock-xxx33-helper
    ;; Jared reordered hyps to speed up the proofs
    (implies (and (equal 0 (+ md0 (* j z)))
                  (not (equal z 0))
                  (acl2-numberp md0)
		  (acl2-numberp j)
		  (acl2-numberp z))
	     (equal (* md0 (/ z)) 
                    (- j)))
    :rule-classes nil))

 (local
  (defthm crock-xxx33a
    ;; Jared reordered hyps to speed up the proofs
    (implies (and (equal 0 (+ md0 (* j z)))
                  (not (equal z 0))
                  (acl2-numberp md0)
		  (integerp j)
		  (acl2-numberp z))
	     (integerp (* md0 (/ z))))
    :hints (("Goal" :use crock-xxx33-helper))))

 (defthm rewrite-floor-mod
   (implies (and (rationalp (/ x y))
		 (rationalp (/ x z))
		 (rationalp (/ (mod x y) z))
		 (equal i (/ y z))
		 (integerp i))
	    (equal (floor (mod x y) z)
		   (- (floor x z) (* i (floor x y))))))

 (defthm rewrite-mod-mod
   (implies (and (acl2-numberp z)
		 (rationalp (/ x y))
		 (rationalp (/ x z))
		 (not (equal z 0))
		 (equal i (/ y z))
		 (integerp i))
	    (equal (mod (mod x y) z)
		   (mod x z)))
   :hints (("Subgoal 1" :in-theory (enable mod)))))


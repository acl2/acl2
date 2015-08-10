; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

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
 (local (in-theory (disable floor-positive
                            floor-negative
                            default-less-than-1
                            default-less-than-2
                            default-times-1
                            default-times-2
                            floor-x-y-=--1
                            floor-x-y-=-1
                            rationalp-x
                            default-floor-ratio
                            reduce-rationalp-*
                            acl2-numberp-x
                            linear-floor-bounds-3
                            mod-zero
                            mod-positive
                            mod-negative
                            mod-nonpositive
                            mod-nonnegative
                            floor-nonnegative
                            floor-nonpositive
                            rfix
                            normalize-factors-scatter-exponents
                            normalize-terms-such-as-a/a+b-+-b/a+b
                            mod-x-y-=-x
                            mod-x-y-=-x-y)))

 (local
  (defthm floor-sum-cases-helper-a
    (implies (and (real/rationalp (/ x z))
		  (real/rationalp (/ y z)))
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
    (implies (and (real/rationalp (/ x z))
		  (real/rationalp (/ y z)))
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
   (implies (and (real/rationalp (/ x z))
		 (real/rationalp (/ y z)))
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

(encapsulate
 ()
 (local (in-theory (disable floor-positive
                            floor-negative
                            default-less-than-1
                            default-less-than-2
                            default-times-1
                            default-times-2
                            floor-x-y-=--1
                            floor-x-y-=-1
                            rationalp-x
                            default-floor-ratio
                            reduce-rationalp-*
                            acl2-numberp-x
                            linear-floor-bounds-3
                            mod-zero
                            mod-positive
                            mod-negative
                            mod-nonpositive
                            mod-nonnegative
                            floor-nonnegative
                            floor-nonpositive
                            rfix
                            normalize-factors-scatter-exponents
                            normalize-terms-such-as-a/a+b-+-b/a+b
                            mod-x-y-=-x
                            mod-x-y-=-x-y)))
 (defthm |(mod (+ x y) z)|
   (implies (and (real/rationalp (/ x z))
                 (real/rationalp (/ y z)))
            (equal (mod (+ x y) z)
                   (if (<= 0 z)
                       (if (< (+ (mod x z) (mod y z)) z)
                           (+ (mod x z) (mod y z))
                         (+ (mod x z) (mod y z) (- z)))
                     (if (< z (+ (mod x z) (mod y z)))
                         (+ (mod x z) (mod y z))
                       (+ (mod x z) (mod y z) (- z))))))
   :hints (("Goal" :in-theory (enable mod)))))






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

#+non-standard-analysis
(local
 (defthm crock-xxx33b
   ;; Jared reordered hyps to speed up the proofs
   (implies (and (equal 0 (+ md0 (* j z)))
                 (not (equal z 0))
                 (acl2-numberp md0)
                 (integerp j)
                 (acl2-numberp z))
            (realp (* md0 (/ z))))
   :hints (("Goal" :use crock-xxx33a))))

(encapsulate
  ()

  (local (in-theory (e/d ()
                         (normalize-factors-scatter-exponents
                          normalize-factors-gather-exponents
                          default-mod-ratio
                          normalize-terms-such-as-1/ax+bx
                          |(* c (* d x))|
                          default-less-than-2
                          default-less-than-1
                          reduce-rational-multiplicative-constant-<
                          reduce-multiplicative-constant-<
                          remove-strict-inequalities
                          reduce-additive-constant-<
                          integerp-<-constant
                          constant-<-integerp
                          prefer-positive-exponents-scatter-exponents-<
                          mod-zero rationalp-/
                          (:REWRITE |(< c (/ x)) positive c --- present in goal|)
                          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|)
                          (:REWRITE |(< c (/ x)) negative c --- present in goal|)
                          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|)
                          (:REWRITE |(< c (- x))|)
                          (:REWRITE |(< (/ x) c) positive c --- present in goal|)
                          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|)
                          (:REWRITE |(< (/ x) c) negative c --- present in goal|)
                          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|)
                          (:REWRITE |(< (/ x) (/ y))|)
                          (:REWRITE |(< (- x) c)|)
                          (:REWRITE |(< (- x) (- y))|)
                          (:rewrite floor-=-x/y . 2)
                          default-divide
                          simplify-terms-such-as-ax+bx-<-0-rational-remainder
                          meta-rationalp-correct
                          simplify-terms-such-as-ax+bx-<-0-rational-common
                          simplify-terms-such-as-0-<-ax+bx-rational-remainder
                          simplify-terms-such-as-0-<-ax+bx-rational-common
                          mod-positive
                          mod-nonpositive
                          mod-nonnegative
                          mod-negative
                          linear-floor-bounds-2
                          |(equal (if a b c) x)|
                          |(< (/ x) 0)|
                          |(< (* x y) 0)|
                          (:REWRITE |(< 0 (* x y))|)
                          (:REWRITE |(< 0 (/ x))|)
                          (:REWRITE |(equal (- x) (- y))|)
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE)
                          (:REWRITE |(equal c (/ x))|)
                          (:REWRITE |(equal c (- x))|)
                          (:REWRITE |(equal (/ x) c)|)
                          (:REWRITE |(equal (/ x) (/ y))|)
                          (:REWRITE |(equal (- x) c)|)
                          (:REWRITE |(< (+ c/d x) y)|)
                          (:REWRITE |(< (+ (- c) x) y)|)
                          (:REWRITE ACL2-NUMBERP-X)
                          )
                         ((:rewrite mod-zero . 3)))))



  (defthm rewrite-floor-mod
    (implies (and (real/rationalp (/ x y))
                  (real/rationalp (/ x z))
                  (real/rationalp (/ (mod x y) z))
                  (equal i (/ y z))
                  (integerp i))
             (equal (floor (mod x y) z)
                    (- (floor x z) (* i (floor x y)))))))



(encapsulate
  ()

  (local (in-theory (e/d ()
                         (normalize-factors-scatter-exponents
                          normalize-factors-gather-exponents
                          default-mod-ratio
                          normalize-terms-such-as-1/ax+bx
                          |(* c (* d x))|
                          default-less-than-2
                          default-less-than-1
                          reduce-rational-multiplicative-constant-<
                          reduce-multiplicative-constant-<
                          remove-strict-inequalities
                          reduce-additive-constant-<
                          integerp-<-constant
                          constant-<-integerp
                          prefer-positive-exponents-scatter-exponents-<
                          floor-zero rationalp-/
                          (:REWRITE |(< c (/ x)) positive c --- present in goal|)
                          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|)
                          (:REWRITE |(< c (/ x)) negative c --- present in goal|)
                          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|)
                          (:REWRITE |(< c (- x))|)
                          (:REWRITE |(< (/ x) c) positive c --- present in goal|)
                          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|)
                          (:REWRITE |(< (/ x) c) negative c --- present in goal|)
                          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|)
                          (:REWRITE |(< (/ x) (/ y))|)
                          (:REWRITE |(< (- x) c)|)
                          (:REWRITE |(< (- x) (- y))|)
                          (:rewrite floor-=-x/y . 2)
                          default-divide
                          simplify-terms-such-as-ax+bx-<-0-rational-remainder
                          meta-rationalp-correct
                          simplify-terms-such-as-ax+bx-<-0-rational-common
                          simplify-terms-such-as-0-<-ax+bx-rational-remainder
                          simplify-terms-such-as-0-<-ax+bx-rational-common
                          floor-positive
                          floor-nonpositive
                          floor-nonnegative
                          floor-negative
                          linear-floor-bounds-2
                          |(equal (if a b c) x)|
                          |(< (/ x) 0)|
                          |(< (* x y) 0)|
                          (:REWRITE |(< 0 (* x y))|)
                          (:REWRITE |(< 0 (/ x))|)
                          (:REWRITE |(equal (- x) (- y))|)
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE)
                          (:REWRITE |(equal c (/ x))|)
                          (:REWRITE |(equal c (- x))|)
                          (:REWRITE |(equal (/ x) c)|)
                          (:REWRITE |(equal (/ x) (/ y))|)
                          (:REWRITE |(equal (- x) c)|)
                          (:REWRITE |(< (+ c/d x) y)|)
                          (:REWRITE |(< (+ (- c) x) y)|)
                          (:REWRITE ACL2-NUMBERP-X)
                          )
                         ((:rewrite mod-zero . 3)))))

 (defthm rewrite-mod-mod
   (implies (and (acl2-numberp z)
		 (real/rationalp (/ x y))
		 (real/rationalp (/ x z))
		 (not (equal z 0))
		 (equal i (/ y z))
		 (integerp i))
	    (equal (mod (mod x y) z)
		   (mod x z)))
   :hints (("Subgoal 1" :in-theory (enable mod)))))


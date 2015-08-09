; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; natp-posp.lisp
;;;
;;; This book is a modified copy of that in arithmetic/natp-posp.  I
;;; discourage the use of natp and posp, except as abbreviations in
;;; a functions definition.  I have no good examples to justify this,
;;; however, so use your own judgement.
;;;
;;; I include this book for those who want to use natp and posp.
;;; Use (enable-natp-posp-theory) and (disable-natp-posp-theory)
;;; to toggle the rules in this book.  See top.lisp for their
;;; definition.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "../../support/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A few simple forward-chaining and rewrite rules to allow
;;; basic reasoning about natp and posp.

(defthm natp-fc-1
  (implies (natp x)
	   (<= 0 x))
  :rule-classes :forward-chaining)

(defthm natp-fc-2
  (implies (natp x)
	   (integerp x))
  :rule-classes :forward-chaining)

(defthm posp-fc-1
  (implies (posp x)
	   (< 0 x))
  :rule-classes :forward-chaining)

(defthm posp-fc-2
  (implies (posp x)
	   (integerp x))
  :rule-classes :forward-chaining)

(defthm natp-rw
  (implies (and (integerp x)
		(<= 0 x))
	   (natp x)))

(defthm posp-rw
  (implies (and (integerp x)
		(< 0 x))
	   (posp x)))

(defthm natp-posp
 (implies (and (natp a)
	       (not (equal a 0)))
	  (posp a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We include a few simple rules for reducing natp or
;;; posp expressions to simpler ones.

;;; We generalize |(natp a)  <=>  (posp a+1)| and natp-posp--1

(defthm |(posp (+ c x))|
  (implies (and (syntaxp (quotep c))
		(< 0 c)
		(integerp a))
	   (equal (posp (+ c a))
		  (natp (+ (- c 1) a)))))

(defthm |(natp (+ c x))|
  (implies (and (syntaxp (quotep c))
		(< c 0)
		(integerp a))
	   (equal (natp (+ c x))
		  (posp (+ (+ c 1) x)))))

;;; We break natp-* into two rules.  One which induces a case-split
;;; similar to that for |(< 0 (* x y))| to be used while rewriting a
;;; goal literal, the other duplicates natp-* and is used during
;;; back-chaining.

(defthm |(natp (* x y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp x)
		(integerp y))
	   (equal (natp (* x y))
		  (or (and (natp x)
			   (natp y))
		      (and (natp (- x))
			   (natp (- y)))))))

(defthm |(natp (* x y)) backchaining|
  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
		(natp x)
		(natp y))
	   (natp (* x y))))

;;; We do the same for posp.  This was missing from
;;; arithmetic/natp-posp.lisp.

(defthm |(posp (* x y))|
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp x)
		(integerp y))
	   (equal (posp (* x y))
		  (or (and (posp x)
			   (posp y))
		      (and (posp (- x))
			   (posp (- y)))))))

(defthm |(posp (* x y)) backchaining|
  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
		(posp x)
		(posp y))
	   (posp (* x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of simple type-prescription rules for natp and posp
;;; of differences.

(defthm |x < y  =>  0 < -x+y|
  (implies (and (integerp x) (integerp y) (< x y))
	   (posp (+ (- x) y)))
  :rule-classes ((:type-prescription)))

(defthm |x < y  =>  0 < y-x|
  (implies (and (integerp x) (integerp y) (< x y))
	   (posp (+ y (- x))))
  :rule-classes ((:type-prescription)))

;;; We do the same for posp.  This was missing from
;;; arithmetic/natp-posp.lisp.

(defthm |x < y  =>  0 <= -x+y|
  (implies (and (integerp x) (integerp y) (<= x y))
	   (natp (+ (- x) y)))
  :rule-classes ((:type-prescription)))

(defthm |x < y  =>  0 <= y-x|
  (implies (and (integerp x) (integerp y) (<= x y))
	   (natp (+ y (- x))))
  :rule-classes ((:type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We do not include the following:

#|
(defthm posp-natp
  (implies (posp (+ -1 x))
	   (natp (+ -2 x))))
|#

;;; It is claimed that it was needed for a couple of proofs,
;;; but we did not find this to be the case in ACL2 v-3.0.1.  The hint
#|
	  ("Subgoal *1/3.3" :use (:instance map-lemma-3.7
					    (i 0)
					    (j (CAR V))))
|#
;;; did, however, have to be added to map-lemma-4 in
;;; books/workshops/2003/sustik/support/dickson,lisp
;;; (This test was done with the arithmetic/natp-posp book,
;;; not this one which contains a generalization of the above:
;;; |(posp (+ c x))|

(in-theory (disable natp posp))

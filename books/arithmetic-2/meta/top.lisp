; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;
;;; This book collects all the other books together in one place,
;;; establishes a couple of usefull theory collections, and sets up
;;; a default starting point.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We include all the books we want.

(include-book "pre")

(include-book "integerp")

(include-book "integerp-meta")

(include-book "cancel-terms-meta")

(include-book "collect-terms-meta")

(include-book "numerator-and-denominator")

(include-book "expt")

(include-book "non-linear")

(include-book "mini-theories")

(include-book "post")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Choose one of the two following theories, scatter-exponents or
; gather-exponents, to be enabled.  The other must be disabled.

; Gather-exponents will "gather" (* (expt x i) (expt x j))
; to (expt (+ i j)), whilst scatter-exponents will scatter
; (expt x (+ i j)) to (* (expt x i) (expt x j)).

; By default, gather-exponents is enabled and scatter-exponents
; is disabled.

(deftheory scatter-exponents
  '(collect-factors-scatter-exponents-thm
    cancel-factors-scatter-exponents-equal-thm
    cancel-factors-scatter-exponents-<-thm
    |(expt x (+ i j))|
    |(expt x (+ i j)) with non-negative exponents|
    |(expt x (+ i j)) with non-positive exponents|
    |(expt x (+ i j)) with non-zero base|))

(deftheory gather-exponents
  '(collect-factors-gather-exponents-thm
    cancel-factors-gather-exponents-equal-thm
    cancel-factors-gather-exponents-<-thm))

(in-theory (disable scatter-exponents))

(in-theory (enable gather-exponents))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One may choose to enable the appropriate one of
; prefer-positive-exponents-scatter-exponents or
; prefer-positive-exponents-gather-exponents.  These two
; theories transform expressions such as
; (equal (* a b (/ c))
;        (* (expt x (* -3 n)) (expt y i))))
; to
; (equal (* a b (expt x (* 3 n)))
;        (* c (expt y i))).
; By default, they are disabled.

(deftheory prefer-positive-exponents-scatter-exponents
  '(prefer-positive-factors-scatter-exponents-equal-thm
    prefer-positive-factors-scatter-exponents-<-thm))

(in-theory (disable prefer-positive-exponents-scatter-exponents))

(deftheory prefer-positive-exponents-gather-exponents
  '(prefer-positive-factors-gather-exponents-equal-thm
    prefer-positive-factors-gather-exponents-<-thm))

(in-theory (disable prefer-positive-exponents-gather-exponents))

; Also, one may enable prefer-positive-sums.  It transforms
; terms such as:
; (< (+ a b (- c))
;    (+ x (* -3 y)))
; to
; (< (+ a b (* 3 y))
;    (+ x c)).
; It is enabled by default.

(deftheory prefer-positive-sums
  '(prefer-positive-addends-equal-thm
    prefer-positive-addends-<-thm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These rules are too expensive for normal use, but are occasionally
; useful.  See expt.lisp.

(in-theory (disable strong-expt-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Finally, a couple of small theories which are occasionally
; useful.

; Some proofs of linear equalities don't work when presented as
; equalities.  This lemma allows you to state the equality as
; an equality rewrite rule, but breaks the equality apart for
; the proof.
;
; Try the following lemma with and without
; rewrite-linear-equalities-to-iff to see what is meant by the
; above paragraph:

#|(defthm <-*-0
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))|#

; The same technique is sometimes needed for other boolean
; operators.

(in-theory (disable rewrite-linear-inequalities-to-iff))



; Ratio-theory-of-1 contains rules such as the following:
#|
(defthm ratio-theory-of-1-a
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (<= 0 x)
                (< 0 y)
                (<= x y))
           (and (<= 0 (/ x y))
                (<= (/ x y) 1)))
   :rule-classes :linear)
|#

; about when a ratio is greater or lesser than one.
; We leave them disabled by default, because they can cause excessive
; thrashing in linear arithmetic.

(in-theory (disable ratio-theory-of-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some clean up to make sure of our setup.

(in-theory (disable expt))

(in-theory (enable un-hide-times
		   collect-times-0a collect-times-0b
		   collect-times-1a collect-times-1b
		   collect-times-1c collect-times-1d
		   collect-times-2a collect-times-2b
		   collect-times-2c collect-times-2d
		   collect-times-2e collect-times-2f
		   collect-times-3a collect-times-3b
		   collect-times-3c collect-times-3d
		   collect-times-4))

(in-theory (enable un-hide-plus collect-plus-0a
		   collect-plus-1a collect-plus-1b
		   collect-plus-1c collect-plus-1d
		   collect-plus-2a collect-plus-2b
		   collect-plus-2c collect-plus-2d
		   collect-plus-3))

(in-theory (disable collect-+ collect-*
		    un-hide-+ un-hide-*))

; These next rules have caused problems at one point or another.
; I might want to reconsider what to do later.

(in-theory (disable Default-+-1 Default-+-2
                    Default-unary-minus
                    Default-*-1 Default-*-2
                    Default-unary-/
                    Commutativity-of-+
                    Commutativity-of-*

		    Associativity-of-+
                    Unicity-of-0
		    Associativity-of-*
		    Unicity-of-1
		    Distributivity

		    Inverse-of-+ Rationalp-+
		    Rationalp-unary--
		    Inverse-of-* Rationalp-*
		    Rationalp-unary-/
		    Nonnegative-product
		    Rationalp-implies-acl2-numberp
                    Rational-implies2
		    Expt-type-prescription-non-zero-base))


; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; top.lisp
;;;
;;;
;;; This book collects all the other books together in one place,
;;; establishes a couple of useful theory collections, and sets up
;;; a default starting point.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Notes: 1 |(integerp (* c x))| in integerp.lisp should not be
;;; nneded after my type-set patch gets in ACL2.  Fix comment about
;;; version number.  Otherwise, prove some guards for it and uncomment
;;; it.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftheory base
  (current-theory :here))

;;; marker for determining whether this library is active

(include-book "we-are-here")

;;; We want these to be the last rules seen:
;;; See comments in basic.lisp.

(include-book "distributivity")

;;(include-book "elim-hint")

(include-book "default-hint")

(include-book "building-blocks")

(include-book "common")

(include-book "normalize")

(include-book "simplify")

(deftheory minimal-start-a
  (current-theory :here))

; (depends-on "build/ground-zero-theory.certdep" :dir :system)
(deftheory-static arithmetic-5-minimal-start-a
  (current-theory :here))

(include-book "mini-theories")

(include-book "numerator-and-denominator")

(deftheory natp-posp-start
  (current-theory :here))

(include-book "natp-posp")

(deftheory natp-posp-end
  (current-theory :here))

(include-book "integerp-meta")

(include-book "integerp")

(include-book "basic")

(include-book "expt")

(deftheory minimal-end-a
  (current-theory :here))

(deftheory-static arithmetic-5-minimal-end-a
  (current-theory :here))

(include-book "collect")

(include-book "remove-weak-inequalities")

(include-book "arithmetic-theory")

(include-book "types")

(deftheory minimal-start-b
  (current-theory :here))

(deftheory-static arithmetic-5-minimal-start-b
  (current-theory :here))

(include-book "simple-equalities-and-inequalities")

;;; We want these to be the first rules seen:

(include-book "if-normalization")

(include-book "forcing-types")

(deftheory minimal-end-b
  (current-theory :here))

(deftheory-static arithmetic-5-minimal-end-b
  (current-theory :here))

(deftheory full
  (current-theory :here))

(deftheory minimal-arithmetic-theory
   (union-theories
    (theory 'base)
    (union-theories (set-difference-theories (theory 'minimal-end-a)
					     (theory 'minimal-start-a))
		    (set-difference-theories (theory 'minimal-end-b)
					     (theory 'minimal-start-b)))))

(deftheory natp-posp-theory
  (set-difference-theories (theory 'natp-posp-end)
			   (theory 'natp-posp-start)))

(defmacro enable-natp-pposp-theory ()
  '(progn
     (in-theory (enable natp-posp-theory))
     (in-theory (disable natp posp))))

(defmacro disable-natp-posp-theory ()
  '(progn
     (in-theory (disable natp-posp-theory))
     (in-theory (enable natp posp))))

(disable-natp-posp-theory)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; There are two basic ways of normalizing terms such as
;;; (expt x (+ m n)) and (* (expt x m) (expt x n)).  One can choose the
;;; first of these as the normal form and gather-exponents, or one can
;;; choose the second as the normal form and scatter-exponents.
;;; We here define some macros to make things easier, and recommend
;;; that they be used.

(deftheory gather-exponents-theory
    '(normalize-factors-gather-exponents
      simplify-products-gather-exponents-equal
      simplify-products-gather-exponents-<))

;;; Keep this in sync with arithmetic-default-hint
;;; in default-hint.lisp.

(deftheory scatter-exponents-theory
    '(|(expt x (+ m n))|
      |(expt x (+ m n)) non-zero (+ m n)|
      |(expt x (+ m n)) non-zero x|
      ;;|(expt x (+ m n)) non-pos m and n|
      ;;|(expt x (+ m n))) non-neg m and n|
      normalize-factors-scatter-exponents
      simplify-products-scatter-exponents-equal
      simplify-products-scatter-exponents-<))

(deftheory prefer-positive-addends-theory
    '(prefer-positive-addends-equal
      prefer-positive-addends-<
      |(equal (+ (- c) x) y)|
      |(< (+ (- c) x) y)|
      |(< y (+ (- c) x))|))

;;; Keep this in sync with arithmetic-default-hint
;;; in default-hint.lisp.

(deftheory prefer-positive-exponents-scatter-exponents-theory
    '(prefer-positive-exponents-scatter-exponents-equal
      prefer-positive-exponents-scatter-exponents-<
      PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))

(defmacro gather-exponents ()
  '(progn
    (in-theory (disable scatter-exponents-theory))
    (in-theory (disable prefer-positive-exponents-scatter-exponents-theory))
    (in-theory (enable gather-exponents-theory))))

(defmacro scatter-exponents ()
  '(progn
    (in-theory (disable gather-exponents-theory))
    (in-theory (enable scatter-exponents-theory))))

(defmacro prefer-positive-exponents ()
  '(progn
    (in-theory (disable gather-exponents-theory))
    (in-theory (enable prefer-positive-exponents-scatter-exponents-theory))
    (in-theory (enable scatter-exponents-theory))))

(defmacro do-not-prefer-positive-exponents ()
  '(in-theory (disable prefer-positive-exponents-scatter-exponents-theory)))

(defmacro prefer-positive-addends ()
  '(in-theory (enable prefer-positive-addends-theory)))

(defmacro do-not-prefer-positive-addends ()
  '(in-theory (disable prefer-positive-addends-theory)))

(gather-exponents)

(prefer-positive-addends)

(theory-invariant
 (if (active-runep '(:definition arith-5-active-flag))
     (not (and (active-runep '(:rewrite |(expt x (+ m n))|))
               (active-runep '(:rewrite normalize-factors-gather-exponents))))
   t)
 :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable expt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We wish to set up the theory that will be used when ACL2 is rewriting
;;; an inequality, prepatory to doing linear and non-linear arithmetic.
;;; The user should not have to change any of this.

(in-theory (disable |arith (expt x c)|
                    |arith (- (- x))| |arith (- (+ x y))|
                    |arith (* y x)| |arith (* y (* x z))|
                    |arith (* (* x y) z)| |arith (* 1 x)|
                    |arith (* x 1)| |arith (* 0 x)|
                    |arith (* x 0)| |arith (* -1 x)|
                    |arith (/ (/ x))| |arith (/ (* x y))|
                    |arith (* x (+ y z))| |arith (* (+ x y) z)|
                    |arith (* x (- y))| |arith (* (- x) y)|
                    |arith (- (* c x))| |arith (/ (- x))|
                    |arith (expt (+ x y) 2)| |arith (expt (+ x y) 3)|
                    |arith (expt x 0)|
                    |arith (expt 0 n)| |arith (expt x 1)|
                    |arith (expt 1 n)| |arith (expt x -1)|
                    ;|arith (expt (/ x) n)| |arith (expt x (- n))|
                    ;|arith (expt (/ x) (- c))|
                    ;|arith (expt 1/c n)|
		    |arith (expt (/ x) n)|
		    |arith (/ (expt x n))|
		    |arith (expt 1/c n)|
                    |arith (expt 4 n)| |arith (expt 8 n)|
                    |arith (expt 16 n)|
                    |arith (expt (* x y) n)|
                    |arith (expt (expt x m) n)| |arith (expt x (+ m n))|
                    ;;|arith (expt x (+ m n)) non-pos m and n|
                    ;;|arith (expt x (+ m n))) non-neg m and n|
                    |arith (expt x (+ m n)) non-zero x|
                    |arith (fix x)| |arith (* (expt x n) (expt y n))|
                    |arith (* x x)| |arith (* x (/ x))|
                    |arith (* x (expt x n))| |arith (* x (expt (- x) n))|
		    |arith (* x (expt x (- n)))|
                    |arith (* x (/ (expt x n)))|
                    |arith (* (numerator x) (/ (denominator x)))|
                    |arith (* c (* d x))|
		    |arith (* x (expt (- x) (- n)))|
		    |arith (* x (/ (expt (- x) n)))|
                    |arith (* (/ x) (expt x n))| |arith (* (/ x) (expt (- x) n))|
                    |arith (* (expt x m) (expt x n))|
                    |arith (* (expt (- x) m) (expt x n))|
                    |arith (* (expt x m) (expt (- x) n))|
		    |arith (* (expt x (- m)) (expt x n))|
                    |arith (* (/ (expt x m)) (expt x n))|
		    |arith (* (expt x m) (expt x (- n)))|
		    |arith (* (expt (- x) (- m)) (expt x n))|
                    |arith (* (/ (expt (- x) m)) (expt x n))|
		    |arith (* (expt x (- m)) (expt (- x) n))|
                    |arith (* (/ (expt x m)) (expt (- x) n))|
                    |arith (* (expt x m) (/ (expt x n)))|
                    |arith (* (expt (- x) m) (/ (expt x n)))|
		    |arith (* (expt (- x) m) (expt x (- n)))|
		    |arith (* (expt x m) (expt (- x) (- n)))|
                    |arith (* (expt x m) (/ (expt (- x) n)))|
                    |arith (* (expt c n) (expt d n))|
                    |arith (+ c (+ d x))|
                    |arith (+ x x)| |arith (+ x (- x))|
                    |arith (+ x (* c x))| |arith (+ (- x) (* c x))|
                    |arith (+ (* c x) (* d x))|
                    arith-collect-+ arith-collect-+-problem-finder
                    arith-collect-* arith-collect-*-problem-finder
                    arith-bubble-down
                    arith-bubble-down-+-problem-finder
                    arith-bubble-down-+-bubble-down
                    arith-bubble-down-+-match-1
                    arith-bubble-down-+-match-2
                    arith-bubble-down-+-match-3
                    arith-bubble-down-*-problem-finder
                    arith-bubble-down-*-bubble-down
                    arith-bubble-down-*-match-1
                    arith-bubble-down-*-match-2
                    arith-bubble-down-*-match-3
                    |(arith-collect-* y x)| |(arith-collect-+ y x)|
                    arith-find-matching-factor-scatter-exponents
                    arith-normalize-factors-scatter-exponents
                    arith-normalize-addends
		    arith-find-matching-addend))

(in-arithmetic-theory '(|arith (expt x c)|
			|arith (- (- x))| |arith (- (+ x y))|
			|arith (* y x)| |arith (* y (* x z))|
			|arith (* (* x y) z)| |arith (* 1 x)|
			|arith (* x 1)| |arith (* 0 x)|
			|arith (* x 0)| |arith (* -1 x)|
			|arith (/ (/ x))| |arith (/ (* x y))|
			|arith (* x (+ y z))| |arith (* (+ x y) z)|
			|arith (* x (- y))| |arith (* (- x) y)|
			|arith (- (* c x))| |arith (/ (- x))|
			|arith (expt (+ x y) 2)| |arith (expt (+ x y) 3)|
			|arith (expt x 0)|
			|arith (expt 0 n)| |arith (expt x 1)|
			|arith (expt 1 n)| |arith (expt x -1)|
					;|arith (expt (/ x) n)| |arith (expt x (- n))|
					;|arith (expt (/ x) (- c))|
					;|arith (expt 1/c n)|
			|arith (expt (/ x) n)|
			|arith (/ (expt x n))|
			|arith (expt 1/c n)|
			|arith (expt 4 n)| |arith (expt 8 n)|
			|arith (expt 16 n)|
			|arith (expt (* x y) n)|
			|arith (expt (expt x m) n)| |arith (expt x (+ m n))|
			;;|arith (expt x (+ m n)) non-pos m and n|
			;;|arith (expt x (+ m n))) non-neg m and n|
			|arith (expt x (+ m n)) non-zero x|
			|arith (fix x)| |arith (* (expt x n) (expt y n))|
			|arith (* x x)| |arith (* x (/ x))|
			|arith (* x (expt x n))| |arith (* x (expt (- x) n))|
			|arith (* x (expt x (- n)))|
			|arith (* x (/ (expt x n)))|
			|arith (* (numerator x) (/ (denominator x)))|
			|arith (* c (* d x))|
			|arith (* x (expt (- x) (- n)))|
			|arith (* x (/ (expt (- x) n)))|
			|arith (* (/ x) (expt x n))| |arith (* (/ x) (expt (- x) n))|
			|arith (* (expt x m) (expt x n))|
			|arith (* (expt (- x) m) (expt x n))|
			|arith (* (expt x m) (expt (- x) n))|
			|arith (* (expt x (- m)) (expt x n))|
			|arith (* (/ (expt x m)) (expt x n))|
			|arith (* (expt x m) (expt x (- n)))|
			|arith (* (expt (- x) (- m)) (expt x n))|
			|arith (* (/ (expt (- x) m)) (expt x n))|
			|arith (* (expt x (- m)) (expt (- x) n))|
			|arith (* (/ (expt x m)) (expt (- x) n))|
			|arith (* (expt x m) (/ (expt x n)))|
			|arith (* (expt (- x) m) (/ (expt x n)))|
			|arith (* (expt (- x) m) (expt x (- n)))|
			|arith (* (expt x m) (expt (- x) (- n)))|
			|arith (* (expt x m) (/ (expt (- x) n)))|
			|arith (* (expt c n) (expt d n))|
			|arith (+ c (+ d x))|
			|arith (+ x x)| |arith (+ x (- x))|
			|arith (+ x (* c x))| |arith (+ (- x) (* c x))|
			|arith (+ (* c x) (* d x))|
			;arith-collect-+
			arith-collect-+-problem-finder
			;arith-collect-*
			arith-collect-*-problem-finder
			;arith-bubble-down
			arith-bubble-down-+-problem-finder
			arith-bubble-down-+-bubble-down
			arith-bubble-down-+-match-1
			arith-bubble-down-+-match-2
			arith-bubble-down-+-match-3
			arith-bubble-down-*-problem-finder
			arith-bubble-down-*-bubble-down
			arith-bubble-down-*-match-1
			arith-bubble-down-*-match-2
			arith-bubble-down-*-match-3
			|(arith-collect-* y x)| |(arith-collect-+ y x)|
			;arith-find-matching-factor-scatter-exponents
			arith-normalize-factors-scatter-exponents
			arith-normalize-addends
			;arith-find-matching-addend
			))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next rules have caused problems at one point or another, or
;;; are superseded by rules in this library. I might want to
;;; reconsider what to do later.

(in-theory (disable Associativity-of-+ Commutativity-of-+
		    Unicity-of-0 Inverse-of-+ Rationalp-+
		    Rationalp-unary-- Unicity-of-1
		    Associativity-of-* Commutativity-of-*
		    Inverse-of-* Rationalp-*
		    Rationalp-unary-/
		    Distributivity
		    Nonnegative-product
		    Rationalp-implies-acl2-numberp
		    Expt-type-prescription-non-zero-base
		    default-+-1 default-+-2
		    default-*-1 default-*-2
		    default-unary-minus default-unary-/
		    default-<-1 default-<-2
		    default-denominator default-numerator))

(deftheory default-arithmetic-theory
  (current-theory :here))

(defmacro set-default-arithmetic-theory ()
  `(in-theory (union-theories (set-difference-theories (current-theory :here)
                                                       (theory 'full))
                              (theory 'default-arithmetic-theory))))

(defmacro set-minimal-arithmetic-theory ()
  `(in-theory (union-theories (set-difference-theories (current-theory :here)
                                                       (theory 'full))
                              (theory 'minimal-arithmetic-theory))))

(include-book "banner"
; Avoid printing banner twice:
              :load-compiled-file nil)


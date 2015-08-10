; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

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

(deftheory arithmetic-3-bind-free-base
  (current-theory :here))

(include-book "default-hint")

(include-book "building-blocks")

(include-book "mini-theories")

(include-book "common")

(include-book "normalize")

(include-book "simplify")

(include-book "numerator-and-denominator")

(include-book "integerp")

(include-book "integerp-meta")

(deftheory pre-basic
  (current-theory :here))

(include-book "basic")

(deftheory post-basic
  (current-theory :here))

(include-book "collect")

(include-book "remove-weak-inequalities")

(include-book "arithmetic-theory")

(deftheory full
  (current-theory :here))

(deftheory minimal-arithmetic-theory
   (union-theories (theory 'arithmetic-3-bind-free-base)
                   (set-difference-theories (theory 'post-basic)
                                            (theory 'pre-basic))))

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

(deftheory scatter-exponents-theory
    '(|(expt x (+ m n))|
      |(expt x (+ m n)) non-zero x|
      |(expt x c)|
      ;;|(expt x (+ m n)) non-pos m and n|
      ;;|(expt x (+ m n))) non-neg m and n|
      normalize-factors-scatter-exponents
      simplify-products-scatter-exponents-equal
      simplify-products-scatter-exponents-<))

(deftheory prefer-positive-addends-theory
    '(prefer-positive-addends-equal
      prefer-positive-addends-<
      ))
;;;      |(equal (+ (- c) x) y)|
;;;      |(< (+ (- c) x) y)|
;;;      |(< y (+ (- c) x))|))

(deftheory prefer-positive-exponents-scatter-exponents-theory
    '(prefer-positive-exponents-scatter-exponents-equal
      prefer-positive-exponents-scatter-exponents-<))

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
 (not (and (active-runep '(:rewrite |(expt x (+ m n))|))
           (active-runep '(:rewrite normalize-factors-gather-exponents))))
 :error nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable expt))

;;; These next rules are somewhat expensive for daily wear, but are
;;; occasionally useful.  See mini-theories for the rules themselves.

(deftheory strong-expt-type-prescription-rules
    '(expt-type-prescription-negative-base-even-exponent
      expt-type-prescription-negative-base-odd-exponent
      expt-type-prescription-nonpositive-base-even-exponent
      expt-type-prescription-nonpositive-base-odd-exponent
      expt-negative-base-even-exponent
      expt-negative-base-odd-exponent))

(in-theory (disable strong-expt-type-prescription-rules))

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
                    |arith (expt (/ x) n)| |arith (expt x (- n))|
                    ;;|arith (expt (/ x) (- c))|
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
                    |arith (* x (/ (expt x n)))|
                    |arith (* (numerator x) (/ (denominator x)))|
                    |arith (* c (* d x))| |arith (* x (/ (expt (- x) n)))|
                    |arith (* (/ x) (expt x n))| |arith (* (/ x) (expt (- x) n))|
                    |arith (* (expt x m) (expt x n))|
                    |arith (* (expt (- x) m) (expt x n))|
                    |arith (* (expt x m) (expt (- x) n))|
                    |arith (* (/ (expt x m)) (expt x n))|
                    |arith (* (/ (expt (- x) m)) (expt x n))|
                    |arith (* (/ (expt x m)) (expt (- x) n))|
                    |arith (* (expt x m) (/ (expt x n)))|
                    |arith (* (expt (- x) m) (/ (expt x n)))|
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
                    arith-find-matching-factor-gather-exponents
                    arith-normalize-factors-gather-exponents
                    arith-find-matching-factor-scatter-exponents
                    arith-normalize-factors-scatter-exponents
                    arith-find-matching-addend arith-normalize-addends))

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
                        |arith (expt (/ x) n)| |arith (expt x (- n))|
                        ;;|arith (expt (/ x) (- c))|
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
                        |arith (* x (/ (expt x n)))|
                        |arith (* (numerator x) (/ (denominator x)))|
                        |arith (* c (* d x))| |arith (* x (/ (expt (- x) n)))|
                        |arith (* (/ x) (expt x n))| |arith (* (/ x) (expt (- x) n))|
                        |arith (* (expt x m) (expt x n))|
                        |arith (* (expt (- x) m) (expt x n))|
                        |arith (* (expt x m) (expt (- x) n))|
                        |arith (* (/ (expt x m)) (expt x n))|
                        |arith (* (/ (expt (- x) m)) (expt x n))|
                        |arith (* (/ (expt x m)) (expt (- x) n))|
                        |arith (* (expt x m) (/ (expt x n)))|
                        |arith (* (expt (- x) m) (/ (expt x n)))|
                        |arith (* (expt x m) (/ (expt (- x) n)))|
                        |arith (* (expt c n) (expt d n))|
                        |arith (+ c (+ d x))|
                        |arith (+ x x)| |arith (+ x (- x))|
                        |arith (+ x (* c x))| |arith (+ (- x) (* c x))|
                        |arith (+ (* c x) (* d x))|
                        arith-bubble-down-*-bubble-down
                        arith-bubble-down-*-match-1
                        arith-bubble-down-*-match-2
                        arith-bubble-down-*-match-3
                        arith-bubble-down-+-bubble-down
                        arith-bubble-down-+-match-1
                        arith-bubble-down-+-match-2
                        arith-bubble-down-+-match-3
                        |(arith-collect-* y x)| |(arith-collect-+ y x)|
                        arith-normalize-factors-scatter-exponents
                        arith-normalize-addends))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These next rules have caused problems at one point or another.
;;; I might want to reconsider what to do later.

(in-theory (disable Associativity-of-+ Commutativity-of-+
		    Unicity-of-0 Inverse-of-+ Rationalp-+
		    Rationalp-unary-- Unicity-of-1
		    Associativity-of-* Commutativity-of-*
                    Rational-implies2
		    Inverse-of-* Rationalp-*
		    Rationalp-unary-/
		    Distributivity
		    Nonnegative-product
		    Rationalp-implies-acl2-numberp
		    Expt-type-prescription-non-zero-base))

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

; Avoid printing banner twice:
(include-book "banner" :load-compiled-file nil)

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "quantification/quantification")
(include-book "quantification/quantified-congruence")
(include-book "quantification/quantified-equivalence")
(include-book "util/rewrite-equiv")
(include-book "adviser/adviser")

(defxdoc linear-arithmetic-with-complex-coefficients
  :parents (linear linear-arithmetic)
  :short "Some books for reasoning about arithmetic expressions with complex coefficients"
  :long "<h1>Linear Reasoning and Complex Coefficients</h1>

<p>Per the following comment from the ACL2 sources, ACL2's built-in
linear arithmetic decision procedure @(see linear-arithmetic) is not
applied to polys with complex coefficients.</p>

@({
; Note that in Multiplication by Positive Preserves Inequality we require the
; positive to be rational.  Multiplication by a 'positive' complex rational
; does not preserve the inequality.  For example, the following evaluates
; to nil:
; (let ((c #c(1 -10))
;       (x #c(1 1))
;       (y #c(2 -2)))
;  (implies (and ; (rationalp c)          ; omit the rationalp hyp
;                  (< 0 c))
;           (iff (< x y)                  ; t
;                (< (* c x) (* c y)))))   ; nil

; Thus, the coefficients in our polys must be rational.
})

<p>If you are in the admittedly unusal situation of needing to perform
linear reasoning over such expressions, you may find the following
books helpful.  It is also possible that these books would prove
useful for reasoning about theorems involving complex numbers in
general.</p>

<h2>Linearize Complex Polys</h2>

@({
(include-book \"coi/util/linearize-complex-polys\" :dir :system)
})

<p>The 'linearize-complex-polys' book introduces the nullary
function (imaginary) and rules, such as those below, that transform
complex expressions into expressions in terms of (imaginary).  In
particular, the product rule rationalizes the coefficients of complex
polys so that they can be processed by ACL2's linear decision
procedure.</p>

@({
(defthm complex-to-imaginary
  (equal (complex real imag)
         (+ (rfix real) (* (rfix imag) (imaginary)))))
})

@({
(defthm reduce-complex-coefficient
  (implies
   (and
    (syntaxp (quotep c))
    (complex-rationalp c))
   (equal (* c x)
          (+ (* (realpart c) x) (* (imagpart c) (imaginary) x)))))
})


<h2>Eliminate Complex Polys</h2>

@({
(include-book \"coi/util/eliminate-complex-polys\" :dir :system)
})

<p>The 'eliminate-complex-polys' book aggressively reduces
linear expressions involving complex coefficients into linear
expressions with rational coefficients.</p>

")

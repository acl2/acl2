; sin-cos.lisp  --  series approximations to SIN and COS
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    sin-cos.lisp
;;;
;;;    Unlimited series approximations to SIN and COS, plus functions for
;;;    creating SIN/COS tables.
;;;
;;;    Bishop Brock and Calvin Harrison
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    brock@cli.com
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

; Modified by Jared, 2014-10, to port documentation to xdoc.

;;;****************************************************************************
;;;
;;;  Environment
;;;
;;;****************************************************************************

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc sin-cos
  :parents (miscellaneous)
  :short "SIN/COS approximations.")

;;;****************************************************************************
;;;
;;;  Series approximations of sin/cos.
;;;
;;;****************************************************************************

(defsection compute-series
  :parents (sin-cos)
  :short "Series approximation to SIN/COS."
  :long #{"""<p>This function is used to calculate the following Maclaurin series.
To compute SIN:</p>

@([
    x - \frac{x^3}{3!} + \frac{x^5}{5!} - \frac{x^7}{7!} + ...
])

<p>To compute COS:</p>

@([
    1- \frac{x^2}{2!} + \frac{x^4}{4!} - \frac{x^6}{6!} + ...
])

<p>Arguments:</p>

<ul>
<li> x      -- x</li>
<li> parity -- T to add the new term, NIL to subtract the new term.</li>
<li> ex     -- @($x^{num}$)</li>
<li> fact   -- @($num!$)</li>
<li> itr    -- Number of iterations</li>
<li> ans    -- Accumulated answer.</li>
</ul>"""}

  (defun compute-series (x parity ex fact num itr ans)
    (declare (xargs :guard (and (rationalp x)
                                (booleanp parity)
                                (rationalp ex)
                                (integerp fact)
                                (> fact 0)
                                (integerp num)
                                (>= num 0)
                                (integerp itr)
                                (>= itr 0)
                                (rationalp ans))))
    (if (zp itr)
        ans
      (compute-series x (not parity) (* x x ex) (* (+ 2 num) (+ 1 num) fact)
                      (+ 2 num) (1- itr) (if parity
                                             (+ ans (/ ex fact))
                                           (- ans (/ ex fact)))))))

(local
 (defthm type-of-compute-series
  (implies
   (and (rationalp x)
	(rationalp ex)
	(integerp fact)
	(integerp num)
	(rationalp ans))
   (rationalp (compute-series x parity ex fact num itr ans)))
  :rule-classes :type-prescription))

(defsection fast-compute-series
  :parents (sin-cos)
  :short "Efficient series approximation to SIN/COS."
  :long #{"""<p>This function is used to calculate the following Maclaurin series.
To compute SIN:</p>

@([
    x - \frac{x^3}{3!} + \frac{x^5}{5!} - \frac{x^7}{7!} + ...
])

<p>To compute COS:</p>

@([
    1- \frac{x^2}{2!} + \frac{x^4}{4!} - \frac{x^6}{6!} + ...
])

<p>Rather than accumulating each term as shown, we instead compute the
numerator and denominator of the sum, and return these two values.  This avoids
the necessity of reducing each rational as it is accumulated.  On one set of
examples this procudure was almost an order of magnitude faster than the simple
summation given by @(see COMPUTE-SERIES).</p>

<p>Given @($x^2$) as @($\frac{num-x^2}{denom-x^2}$), and a partial sum
@($\frac{num-sum}{denom-sum}$), we compute the next partial sum as:</p>

@([
\frac{num-sum}{denom-sum}
   *
\frac{
   denom-x^2 (n + 1) (n + 2)
}{ denom-x^2 (n + 1) (n + 2) }
  *
\frac{
    num-x^n num-x^2
}{  denom-x^2 (n + 1) (n + 2)  }

])

<p>Again, the rationals are not actually computed, and instead we simply return
the numerator and denominator of the answer.</p>

<p>Arguments:</p>

<ul>
<li>num-x^2   -- (Numerator of x)^2.</li>
<li>denom-x^2 -- (Denominator of x)^2.</li>
<li>num-x^n   -- @($(num-x)^n$)</li>
<li>num-sum   -- Numerator of partial sum.</li>
<li>denom-sum -- Denominator of partial sum.</li>
<li>n         -- n</li>
<li>parity    -- T to add next term, NIL to subtract next term.</li>
<li>itr       -- Number of iterations to perform.</li>
</ul>"""}

  (defun fast-compute-series
    (num-x^2 denom-x^2 num-x^n num-sum denom-sum n parity itr)
    (declare (xargs :guard (and (integerp num-x^2)
                                (integerp denom-x^2)
                                (not (= denom-x^2 0))
                                (integerp num-x^n)
                                (integerp num-sum)
                                (integerp denom-sum)
                                (not (= denom-sum 0))
                                (integerp n)
                                (<= 0 n)
                                (booleanp parity)
                                (integerp itr)
                                (<= 0 itr))
                    :guard-hints (("Goal" :in-theory (disable DISTRIBUTIVITY)))))

    (if (zp itr)
        (mv num-sum denom-sum)
      (let*
          ((n+1*n+2          (* (+ n 1) (+ n 2)))
           (multiplier       (* denom-x^2 n+1*n+2))
           (new-denom-sum    (* denom-sum multiplier))
           (adjusted-num-sum (* num-sum multiplier))
           (new-num-x^n      (* num-x^n num-x^2))
           (new-num-sum      (if parity
                                 (+ adjusted-num-sum new-num-x^n)
                               (- adjusted-num-sum new-num-x^n))))

        (fast-compute-series num-x^2 denom-x^2 new-num-x^n
                             new-num-sum new-denom-sum
                             (+ 2 n) (not parity) (1- itr))))))

(local
 (defthm type-of-fast-compute-series
  (implies
   (and (integerp num-x^2)
	(integerp denom-x^2)
	(not (= denom-x^2 0))
	(integerp num-x^n)
	(integerp num-sum)
	(integerp denom-sum)
	(not (= denom-sum 0))
	(integerp n)
	(<= 0 n)
	(booleanp parity)
	(integerp itr)
	(<= 0 itr))
   (and
    (integerp
     (mv-nth 0 (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
    (integerp
     (mv-nth 1 (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
    (not
     (equal
      (mv-nth 1
	      (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				   n parity itr))
      0))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies
     (and (integerp num-x^2)
	  (integerp denom-x^2)
	  (not (= denom-x^2 0))
	  (integerp num-x^n)
	  (integerp num-sum)
	  (integerp denom-sum)
	  (not (= denom-sum 0))
	  (integerp n)
	  (<= 0 n)
	  (booleanp parity)
	  (integerp itr)
	  (<= 0 itr))
     (integerp
      (mv-nth 0
	      (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				   n parity itr)))))
   (:type-prescription
    :corollary
    (implies
     (and (integerp num-x^2)
	  (integerp denom-x^2)
	  (not (= denom-x^2 0))
	  (integerp num-x^n)
	  (integerp num-sum)
	  (integerp denom-sum)
	  (not (= denom-sum 0))
	  (integerp n)
	  (<= 0 n)
	  (booleanp parity)
	  (integerp itr)
	  (<= 0 itr))
     (and
      (integerp
       (mv-nth 1
	       (fast-compute-series num-x^2 denom-x^2 num-x^n num-sum denom-sum
				    n parity itr)))
      (not
       (equal
	(mv-nth 1
		(fast-compute-series num-x^2 denom-x^2 num-x^n
				     num-sum denom-sum n parity itr))
	0))))))

  :hints
  (("Goal"
    :in-theory (disable distributivity))))) ;Too slow

(defsection fast-compute-cos
  :parents (sin-cos)
  :short "This function returns the numerator and denominator of a rational
approximation to cos(x) (in radians) by itr iterations of @(see
FAST-COMPUTE-SERIES)."

  (defun fast-compute-cos (x itr)
    (declare (xargs :guard (and (rationalp x)
                                (integerp itr)
                                (>= itr 0))))
    (fast-compute-series (* (numerator x) (numerator x))
                         (* (denominator x) (denominator x))
                         1 1 1 0 nil itr)))

(defsection fast-compute-sin
  :parents (sin-cos)
  :short "This function returns the numerator and denominator of a rational
approximation to sin(x) (in radians) by itr iterations of @(see
FAST-COMPUTE-SERIES)."

  (defun fast-compute-sin (x itr)
    (declare (xargs :guard (and (rationalp x)
                                (integerp itr)
                                (>= itr 0))))
    (fast-compute-series (* (numerator x) (numerator x))
                         (* (denominator x) (denominator x))
                         (numerator x) (numerator x) (denominator x) 1 nil itr)))

(defsection truncated-integer-cos
  :parents (sin-cos)
  :short "Integer approximation to @($cos(x) * scale$)."
  :long "<p>A rational approximation to @($cos(x)$), scaled up by scale, and
then @(see truncate)d to an integer.</p>"

  (defun truncated-integer-cos (x itr scale)
    (declare (xargs :guard (and (rationalp x)
                                (integerp itr)
                                (<= 0 itr)
                                (rationalp scale))
                    :guard-hints (("Goal" :in-theory (disable mv-nth)))))
    (mv-let (num denom) (fast-compute-cos x itr)
      (truncate (* num scale) denom))))

(defsection truncated-integer-sin
  :parents (sin-cos)
  :short "Integer approximation to @($sin(x) * scale$)."
  :long "<p>A rational approximation to @($cos(x)$), scaled up by scale, and
then @(see truncate)d to an integer.</p>"

  (defun truncated-integer-sin (x itr scale)
    (declare (xargs :guard (and (rationalp x)
                                (integerp itr)
                                (<= 0 itr)
                                (rationalp scale))
                    :guard-hints (("Goal" :in-theory (disable mv-nth)))))
    (mv-let (num denom) (fast-compute-sin x itr)
      (truncate (* num scale) denom))))

(defsection truncated-integer-sin/cos-table-fn
  :parents (sin-cos)
; Matt K. mod: The following was a broken link, but I don't know the right fix,
; so I've simply removed the link.
; :short "Helper for @(see SIN/COS-TABLE-FN)."
  :short "Helper for @('SIN/COS-TABLE-FN')."
  :long #{"""<p>Note that this function has special code for @($0$),
@($\pi/2$), @($\pi$), and @($\frac{3}{2}\pi$).  The convergence of the series
at these points is problematic in the context of
truncation (vs. rounding).</p>"""}

  (defun truncated-integer-sin/cos-table-fn (sin/cos i n pie itr scale)
    (declare (xargs :guard (and (or (eq sin/cos :SIN) (eq sin/cos :COS))
                                (integerp i)
                                (<= 0 i)
                                (integerp n)
                                (<= 0 n)
                                (<= i n)
                                (rationalp pie)
                                (integerp itr)
                                (<= 0 itr)
                                (rationalp scale))
                    :measure (ifix (if (<= n i) 0 (- n i)))))
    (cond
     ((zp (- n i)) nil)
     (t (let ((i/n (/ i n)))
          (cons
           (cons i (case sin/cos
                     (:sin
                      (case i/n
                        ((0 1/2) 0)	        ;0, pi
                        (1/4 (truncate scale 1)) ;pi/2
                        (3/4 (truncate scale -1)) ;(3/2)pi
                        (t
                         (truncated-integer-sin (* 2 pie i/n) itr scale))))
                     (t
                      (case i/n
                        (0 (truncate scale 1))  ;0
                        ((1/4 3/4) 0)	        ;pi/2, (3/2)pi
                        (1/2 (truncate scale -1)) ;pi
                        (t
                         (truncated-integer-cos (* 2 pie i/n) itr scale))))))
           (truncated-integer-sin/cos-table-fn
            sin/cos (1+ i) n pie itr scale)))))))

(defsection truncated-integer-sin/cos-table
  :parents (sin-cos)
  :short "Create a scaled, truncated integer sin/cos table from @($0$) to @($2*\\pi$)."
  :long #{"""<p>This function creates a table of approximations to</p>

@([
    sin[cos]( (2 \pi i)/n ) * scale
])

<p>For @($i = 0,...,n-1$).  The result is an alist binding @($i$) to @($sin[cos](i)$).</p>

<p>Arguments:</p>

<ul>
<li>sin/cos -- :SIN or :COS.</li>
<li>n       -- Total number of table entries</li>
<li>pie     -- An approximation to @($\pi$) sufficiently accurate for the user's
               purposes.</li>
<li>itr     -- Required number of iterations of FAST-COMPUTE-SIN[COS]
               sufficient for user's accuracy.</li>
<li>scale   -- Scale factor.</li>
</ul>"""}

  (defun truncated-integer-sin/cos-table (sin/cos n pie itr scale)
    (declare (xargs :guard (and (or (eq sin/cos :SIN) (eq sin/cos :COS))
                                (integerp n)
                                (<= 0 n)
                                (rationalp pie)
                                (integerp itr)
                                (<= 0 itr)
                                (rationalp scale))))
    (truncated-integer-sin/cos-table-fn sin/cos 0 n pie itr scale)))

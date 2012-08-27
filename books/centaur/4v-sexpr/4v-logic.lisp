; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; 4v-logic.lisp
;   - defines our 4-valued logic constants
;   - defines our primitive four-valued logical operators (4v-and, 4v-or, ...)
;   - proves monotonicity of these operators
;   - defines our 4v-<= lattice comparison (and 4v-list-<=)
;   - defines the 4v-lookup operation for reading values from alists

(in-package "ACL2")
(include-book "centaur/misc/witness-cp" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "misc/definline" :dir :system)

;; Local Variables:
;; eval: (put '4vcases 'lisp-indent-function 1)
;; End:

(defsection 4vp
  :parents (4v)
  :short "Recognizer for four-valued logic constants."

  :long "<p>When we are programming and want to refer to a particular logical
value, we generally use <tt>(4vx)</tt>, <tt>(4vz)</tt>, <tt>(4vt)</tt>, and
<tt>(4vf)</tt>.  These are just macros that expand to the symbols X, Z, T, and
F, in the ACL2 package.  We don't write these symbols directly, to try to make
it easy to change their representation if desired.</p>"

  (defmacro 4vx () '(quote x))
  (defmacro 4vz () '(quote z))
  (defmacro 4vt () '(quote t))
  (defmacro 4vf () '(quote f))

  (defun 4vp (x)
    (declare (xargs :guard t))
    (or (eq x (4vt))
        (eq x (4vf))
        (eq x (4vz))
        (eq x (4vx)))))


; BOZO.  These constants are here for historic/compatibility reasons.  It seems
; better to use the macros, since it avoids the cost of a special lookup.

(defconst *4vx* (4vx))
(defconst *4vz* (4vz))
(defconst *4vt* (4vt))
(defconst *4vf* (4vf))

(defsection 4vcases
  :parents (4v)
  :short "Macro for cases on the 4-valued logic constants."

  :long "<p>This looks like a case statement, except that <tt>t</tt>,
<tt>f</tt>, and <tt>z</tt> match with <tt>(4vt)</tt>, <tt>(4vf)</tt>, and
<tt>(4vz)</tt>, respectively.</p>

<p>The <tt>x</tt> case should be the default (last) case.  Anything other than
<tt>t</tt>, <tt>f</tt>, or <tt>z</tt> will result in the default case; we
typically use <tt>&amp;</tt> or <tt>otherwise</tt>.</p>

<p>For example:</p>

<code>
 (defun 4v-not (a)
   (4vcases a
     (t (4vf))
     (f (4vt))
     (&amp; (4vx))))
</code>

<p>Is like writing:</p>

<code>
 (defun 4v-not (a)
   (cond ((eq a (4vt)) (4vf))
         ((eq a (4vf)) (4vt))
         (t (4vx))))
</code>"

  (defun 4vcases-cases (cases)
    (declare (xargs :mode :program))
    (if (endp cases)
        nil
      (cons (list (case (caar cases)
                    ((t) '(eq 4vcases-var (4vt)))
                    (f   '(eq 4vcases-var (4vf)))
                    (z   '(eq 4vcases-var (4vz)))
                    (otherwise   t))
                  `(check-vars-not-free (4vcases-var)
                                        ,(cadar cases)))
            (4vcases-cases (cdr cases)))))

  (defmacro 4vcases (x &rest cases)
    `(let ((4vcases-var ,x))
       (cond . ,(4vcases-cases cases)))))


(defsection 4v-fix
  :parents (4v)
  :short "Fixing function for four-valued constants."

  :long "<p>@(call 4v-fix) interprets <tt>a</tt> as a four-valued constant.
Any non-@(see 4vp) objects are coerced to X.</p>"

  (definline 4v-fix (a)
    (declare (xargs :guard t))
    (mbe :logic
         (if (4vp a) a (4vx))
         :exec
         (if (or (eq a (4vt))
                 (eq a (4vf))
                 (eq a (4vz)))
             a
           (4vx))))

  (defthm 4v-fix-when-4vp
    (implies (4vp x)
             (equal (4v-fix x) x))))


(defxdoc 4v-operations
  :parents (4v)
  :short "Primitive operations in our four-valued logic."

  :long "<p>Note that all of these operations are <see topic='@(url
4v-monotonicity)'>monotonic</see>.</p>")


(defsection 4v-unfloat
  :parents (4v-operations)
  :short "Converts floating (undriven) values to X."

  :long "<p>@(call 4v-unfloat) is a helper routine that is used in the
definitions of many other @(see 4v-operations).  It just coerces Z values into
X, while leaving any other 4-valued logic constants alone.</p>

<p>What is this function for?  Z values have a special role in a few specific
operations, like @(see 4v-res), @(see 4v-pullup), and @(see 4v-tristate).  But
most of the time, e.g., in @(see 4v-not), @(see 4v-and), etc., a Z value on an
input should just be regarded as an X.</p>

<p>To see why, let us consider a simple inverter.</p>

<code>
                      power
                        |
                     ___|
                   ||
            +-----o||
            |      ||___
            |           |
   in ------+           +--------- out
            |        ___|
            |      ||
            +------||
                   ||___
                        |
                        |
                      ground
</code>

<p>When <tt>in</tt> is Z, the behavior of these transistors can't be accurately
predicted.  Hence, we should treat a Z as if it were an X.  The situation for
other kinds of ordinary logic gates (ands, ors, xors) is similar.  So, when we
define operations like @(see 4v-not) and @(see 4v-and) that are intended to
model gates, we generally apply <tt>4v-unfloat</tt> to the inputs so that any Z
values are treated as X.</p>"

  (definline 4v-unfloat (a)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (z (4vx))
           (& (4v-fix a)))
         :exec
         (if (or (eq a (4vt))
                 (eq a (4vf)))
             a
           (4vx))))

  (defthm 4v-unfloat-truth-table
    ;; "Correctness" of 4v-unfloat
    (and (equal (4v-unfloat (4vt)) (4vt))
         (equal (4v-unfloat (4vf)) (4vf))
         (equal (4v-unfloat (4vx)) (4vx))
         (equal (4v-unfloat (4vz)) (4vx)))
    :rule-classes nil))



(defsection 4v-not
  :parents (4v-operations)
  :short "Four-valued semantics for <tt>not</tt> gates."

  :long "<p>@(call 4v-not) returns the value specified by the following
truth table:</p>

<code>
    a  |  out
  -----+-------
    T  |   F
    F  |   T
    X  |   X
    Z  |   X
  -----+-------
</code>

<p>See @(see 4v-unfloat) for an explanation of the Z case.</p>"

  (definline 4v-not (a)
    (declare (xargs :guard t))
    (4vcases a
      (t (4vf))
      (f (4vt))
      (& (4vx))))

  (defthm 4v-not-truth-table
    ;; "Correctness" of 4v-not
    (and (equal (4v-not (4vt)) (4vf))
         (equal (4v-not (4vf)) (4vt))
         (equal (4v-not (4vx)) (4vx))
         (equal (4v-not (4vz)) (4vx)))
    :rule-classes nil))



(defsection 4v-and
  :parents (4v-operations)
  :short "Four-valued semantics for <tt>and</tt> gates."

  :long "<p>@(call 4v-and) returns:</p>

<ul>
 <li>F when either input is F, or</li>
 <li>X when either input is X/Z, or</li>
 <li>T when both inputs are T.</li>
</ul>

<p>See @(see 4v-unfloat) for an explanation of the Z case.</p>"

  (definline 4v-and (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4v-unfloat b))
           (f (4vf))
           (& (4vcases b
                (f (4vf))
                (& (4vx)))))
         :exec
         (cond ((or (eq a (4vf))
                    (eq b (4vf)))
                (4vf))
               ((and (eq a (4vt))
                     (eq b (4vt)))
                (4vt))
               (t
                (4vx))))))


(defsection 4v-or
  :parents (4v-operations)
  :short "Four-valued semantics for <tt>or</tt> gates."

  :long "<p>@(call 4v-or) returns:</p>

<ul>
 <li>T when either input is T, or</li>
 <li>X when either input is X/Z, or</li>
 <li>F when both inputs are F.</li>
</ul>

<p>See @(see 4v-unfloat) for an explanation of the Z case.</p>"

  (definline 4v-or (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4vt))
           (f (4v-unfloat b))
           (& (4vcases b
                (t (4vt))
                (& (4vx)))))
         :exec
         (cond ((or (eq a (4vt))
                    (eq b (4vt)))
                (4vt))
               ((and (eq a (4vf))
                     (eq b (4vf)))
                (4vf))
               (t
                (4vx))))))


(defsection 4v-xor
  :parents (4v-operations)
  :short "Four-valued semantics for <tt>xor</tt> gates."

  :long "<p>@(call 4v-xor) returns:</p>

<ul>
 <li>T when its inputs are Boolean and differ, or</li>
 <li>F when its inputs are Boolean and are the same, or</li>
 <li>X otherwise.</li>
</ul>

<p>See @(see 4v-unfloat) for an explanation of the Z case.</p>"

  (definline 4v-xor (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4v-not b))
           (f (4v-unfloat b))
           (& (4vx)))
         :exec
         (cond ((eq a (4vt))
                (cond ((eq b (4vt)) (4vf))
                      ((eq b (4vf)) (4vt))
                      (t            (4vx))))
               ((eq a (4vf))
                (cond ((eq b (4vt)) (4vt))
                      ((eq b (4vf)) (4vf))
                      (t            (4vx))))
               (t
                (4vx))))))


(defsection 4v-iff
  :parents (4v-operations)
  :short "Four-valued semantics for <tt>xnor</tt> gates."

  :long "<p>@(call 4v-iff) returns:</p>

<ul>
 <li>T when its inputs are Boolean and are the same, or</li>
 <li>F when its inputs are Boolean and differ, or</li>
 <li>X otherwise.</li>
</ul>

<p>See @(see 4v-unfloat) for an explanation of the Z case.</p>"

  (definline 4v-iff (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4v-unfloat b))
           (f (4v-not b))
           (& (4vx)))
         :exec
         (cond ((eq a (4vt))
                (cond ((eq b (4vt)) (4vt))
                      ((eq b (4vf)) (4vf))
                      (t            (4vx))))
               ((eq a (4vf))
                (cond ((eq b (4vt)) (4vf))
                      ((eq b (4vf)) (4vt))
                      (t            (4vx))))
               (t
                (4vx))))))



(defsection 4v-ite
  :parents (4v-operations)
  :short "Less-conservative four-valued semantics for a multiplexor (mux)."

  :long "<p>We have two possible semantics for modeling muxes:</p>

<ul>
 <li>@(call 4v-ite) is a less-conservative semantics, whereas</li>
 <li>@(call 4v-ite*) is a more-conservative version.</li>
</ul>

<p>In both versions, C is the selector, and A/B are data inputs.  The mux we
are modeling would typically be drawn as:</p>

<code>
        A     B
        |     |
     ___|_____|___
     \\           /
 C ---\\         /
       \\_______/
           |
           |
          Out
</code>


<h3>Semantics</h3>

<p>Both versions agree exactly in most cases:</p>

<ul>

<li>When all of these inputs are Boolean, we simply return A or B depending on
the value of C.</li>

<li>When C is Boolean but the selected value is X or Z, we do not know what the
mux will produce so we return X; see @(see 4v-unfloat) for an explanation of
the Z case.</li>

<li>When C is X or Z, it is sometimes clear that we must output X.  For
instance, suppose A = T while B = F.  Then, since we do not know which value
will be selected, we can only say that the output is X.</li>

</ul>

<p>The trickiest case, and the one where <tt>4v-ite</tt> and <tt>4v-ite*</tt>
differ, is when:</p>

<ul>
 <li>C is X or Z, and</li>
 <li>A and B share some Boolean value.</li>
</ul>

<p>In this case,</p>

<ul>
 <li><tt>4v-ite*</tt> (more conservatively) produces an X, whereas</li>
 <li><tt>4v-ite</tt> (less conservatively) produces the value shared by A
and B.</li>
</ul>


<h3>Comparison</h3>

<p>It might be that the <tt>4v-ite</tt> behavior is necessary when analyzing
some circuits.  But we do not think this should be the case very frequently,
and we think you really should probably not design circuits this way.</p>

<p>But unless there is some special reason that <tt>4v-ite</tt> is needed, we
think <tt>4v-ite*</tt> is usually the better way to go.  There are two reasons
for this:</p>


<h5>1. Modeling considerations</h5>

<p>Some mux implementations, specifically those based on pass transistors, may
not produce a good value on their output when the select is undriven.  The
<tt>4v-ite</tt> semantics are <b>totally wrong</b> for such muxes.</p>

<p>The <tt>4v-ite*</tt> semantics are safer, but do not entirely address the
problem because, when the select is undriven, such circuits can have \"backward
flow\" where their output drives the input.  We have no way to model this.</p>

<p>Of course, gate-based mux implementations do not have this problem.  If a
mux is implemented along the lines of <tt>(C &amp; A) | (~C &amp; B)</tt>, then
any Boolean value of C will give us the shared answer as <tt>4v-ite</tt>
produces, so either implementation is probably okay.</p>

<p>BOZO what about if C is Z?  Are the less-conservative semantics okay in this
case, even for a gate-based mux?  This could be iffy.</p>


<h5>2. Symbolic simulation performance.</h5>

<p>The <tt>4v-ite*</tt> semantics may permit faster symbolic simulations.  In
particular, suppose we are interested in analyzing a small part of a large
circuit, and we have set many signals we think are irrelevant to X.
Furthermore, suppose one of these Xed out signals is C, i.e., it is being used
as the select for some mux.</p>

<p>With a <tt>4v-ite</tt> mux, the resulting expression for the output wire
will be some function that involves checking whether the expressions for A and
B have the same value.  This resulting expression will contain the expressions
for A and B, so if these input expressions are large, the resulting expression
will be large.</p>

<p>But with a <tt>4v-ite*</tt> mux, regardless of the expressions on A and B
the result is simply the constant function X.</p>

<p>In other words, <tt>4v-ite*</tt> based muxes have a very nice property: if
the select is X, the output expression is just X and all of the presumably
irrelevant logic driving the mux is discarded, whereas <tt>4v-ite</tt> muxes
don't get to carry out this kind of optimization.</p>"

; BOZO naming.  Consider renaming 4v-ite to 4v-unsafe-ite or something.
; Alternately, consider getting rid of 4v-ite altogether.

  (defxdoc 4v-ite*
    :parents (4v-operations)
    :short "More-conservative four-valued semantics for a multiplexor."
    :long "<p>See @(see 4v-ite) for all documentation.</p>")

  (defun 4v-ite (c a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases c
           (t (4v-unfloat a))
           (f (4v-unfloat b))
           (& (4vcases (4v-iff a b)
                (t a)
                (& (4vx)))))
         :exec
         (cond ((eq c (4vt))
                (if (or (eq a (4vt))
                        (eq a (4vf)))
                    a
                  (4vx)))
               ((eq c (4vf))
                (if (or (eq b (4vt))
                        (eq b (4vf)))
                    b
                  (4vx)))
               (t
                (4vcases (4v-iff a b)
                  (t a)
                  (& (4vx)))))))

  (defun 4v-ite* (c a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases c
           (t (4v-unfloat a))
           (f (4v-unfloat b))
           (& (4vx)))
         :exec
         (cond ((eq c (4vt))
                (if (or (eq a (4vt))
                        (eq a (4vf)))
                    a
                  (4vx)))
               ((eq c (4vf))
                (if (or (eq b (4vt))
                        (eq b (4vf)))
                    b
                  (4vx)))
               (t
                (4vx))))))



(defsection 4v-tristate
  :parents (4v-operations)
  :short "Four-valued semantics for tri-state buffers."

  :long "<p>This is our model of a simple tri-state buffer:</p>

<code>
          A
          |
       ___|___
       \\     /
  C ----\\   /
         \\ /
          V
          |
         Out
</code>

<p>@(call 4v-tristate) returns:</p>

<ul>
 <li>A when its inputs are Boolean and C is T, or</li>
 <li>Z when C is known to be false, or</li>
 <li>X otherwise.</li>
</ul>

<p>This exactly matches the Verilog semantics for:</p>

<code>
  wire c = sel ? a : 1'bz;
</code>

<p>Such buffers are typically used to model muxes with multiple selectors.  See
also @(see 4v-res).</p>"

  (defun 4v-tristate (c a)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases c
           (t (4v-unfloat a))
           (f (4vz))
           (& (4vx)))
         :exec
         (cond ((eq c (4vf))
                (4vz))
               ((and (eq c (4vt))
                     (or (eq a (4vt))
                         (eq a (4vf))))
                a)
               (t
                (4vx))))))


(defsection 4v-pullup
  :parents (4v-operations)
  :short "Four-valued semantics for a pullup resistor."

  :long "<p>@(call 4v-pullup) acts just like a buffer except that, if its input
is floating, it instead produces true.  That is, it returns the value specified
by the following truth table:</p>

<code>
   a  |  out
 -----+-------
   F  |   F
   T  |   T
   X  |   X
   Z  |   T
</code>"

; BOZO what good are pullup resistors?  I don't think we're currently using
; them in VL/ESIM, can we get rid of them?

  (defun 4v-pullup (a)
    (declare (xargs :guard t))
    (4vcases a
      (t (4vt))
      (z (4vt))
      (f (4vf))
      (& (4vx)))))



(defsection 4v-res
  :parents (4v-operations)
  :short "Four-valued semantics for connecting multiple wires together."

  :long "<p>@(call 4v-res) is a funny kind of operation that resolves what
happens when multiple signals are wired together.</p>

<p>Suppose we have the following circuit:</p>

<code>
  .------------.   A           ...
  | some cloud |-----+          |
  |  of logic  |     |       ___|
  '------------'     |_____||
                     |     ||___
  .------------.     |          |
  | some cloud |-----+          |
  |  of logic  |   B           ...
  '------------'
</code>

<p>Because @(see esim) does support driving a single wire with multiple
sources, we model such a circuit by inserting a \"resolution\" module:</p>

<code>
  .------------.   A                  ...
  | some cloud |-----+                 |
  |  of logic  |     |              ___|
  '------------'   +-----+        ||
                   | res |---C ---||
                   +-----+        ||___
  .------------.     |                 |
  | some cloud |-----+                 |
  |  of logic  |   B                  ...
  '------------'
</code>

<p>@(call 4v-res) produces the value for C as follows:</p>

<ul>
 <li>The shared value of A and B when they agree, or</li>
 <li>The value on the other wire, when one of A or B is Z, or</li>
 <li>X otherwise.</li>
</ul>

<p>This is, of course, not a full model of transistor-level behavior.  It does
not account for the possibility that values could flow \"backwards\" from the
the circuitry connected to C, so it is only appropriate for cases where C is
really being used to gate a transistor.</p>

<p>It also does not account for the possibility that values could flow
\"between\" the clouds of logic producing A and B.  If, say, A and B are gate
outputs that are being driven to different values, then wiring them together
produces a short circuit!</p>"

  (defun 4v-res (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (z (4v-fix b))
           (& (4vcases b
                (z (4v-fix a))
                (& (let ((a (4v-fix a))
                         (b (4v-fix b)))
                     (if (eq a b)
                         a
                       (4vx)))))))
         :exec
         (cond ((eq a (4vz))
                (if (or (eq b (4vt))
                        (eq b (4vf))
                        (eq b (4vz)))
                    b
                  (4vx)))
               ((eq b (4vz))
                (if (or (eq a (4vt))
                        (eq a (4vf)))
                    a
                  (4vx)))
               (t
                (if (and (or (eq a (4vt))
                             (eq a (4vf)))
                         (eq a b))
                    a
                  (4vx)))))))


(defsection 4v-wand
  :parents (4v-operations)
  :short "Four-valued semantics for a wired and."

  :long "<p>@(call 4v-wand) returns:</p>
<ul>
 <li>F when either input is F, or</li>
 <li>Z when both inputs are Z, or</li>
 <li>T when one input is T and the other is T/Z, or</li>
 <li>X otherwise.</li>
</ul>

<p>We use this to model what happens when multiple signals are connected in a
wired and arrangement.</p>

<p>The full truth table is shown below.  It intentionally corresponds to the
Verilog semantics for wired ors (Section 4.6.2 of the Verilog 2005
specification).</p>

<code>
       |   F   T   X   Z  |
  -----+------------------+
    F  |   F   F   F   F  |
    T  |   F   T   X   T  |
    X  |   F   X   X   X  |
    Z  |   F   T   X   Z  |
  -----+------------------+
</code>"

  (defun 4v-wand (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4vcases b
                (z (4vt))
                (& (4v-fix b))))
           (f (4vf))
           (z (4v-fix b))
           (& (4vcases b
                (f (4vf))
                (& (4vx)))))
         :exec
         (cond ((eq a (4vf)) (4vf))
               ((eq b (4vf)) (4vf))
               ((eq a (4vt))
                (if (or (eq b (4vt))
                        (eq b (4vz)))
                    (4vt)
                  (4vx)))
               ((eq a (4vz))
                (if (or (eq b (4vt))
                        (eq b (4vz)))
                    b
                  (4vx)))
               (t
                (4vx)))))

  (defthm 4v-wand-truth-table
    ;; "Correctness" of 4v-wand, w.r.t. Table 4-3 of the Verilog spec.
    (and (equal (4v-wand (4vf) (4vf)) (4vf))
         (equal (4v-wand (4vf) (4vt)) (4vf))
         (equal (4v-wand (4vf) (4vx)) (4vf))
         (equal (4v-wand (4vf) (4vz)) (4vf))

         (equal (4v-wand (4vt) (4vf)) (4vf))
         (equal (4v-wand (4vt) (4vt)) (4vt))
         (equal (4v-wand (4vt) (4vx)) (4vx))
         (equal (4v-wand (4vt) (4vz)) (4vt))

         (equal (4v-wand (4vx) (4vf)) (4vf))
         (equal (4v-wand (4vx) (4vt)) (4vx))
         (equal (4v-wand (4vx) (4vx)) (4vx))
         (equal (4v-wand (4vx) (4vz)) (4vx))

         (equal (4v-wand (4vz) (4vf)) (4vf))
         (equal (4v-wand (4vz) (4vt)) (4vt))
         (equal (4v-wand (4vz) (4vx)) (4vx))
         (equal (4v-wand (4vz) (4vz)) (4vz)))
    :rule-classes nil))



(defsection 4v-wor
  :parents (4v-operations)
  :short "Four-valued semantics for a wired or."
  :long "<p>@(call 4v-wor) returns:</p>
<ul>
 <li>T when either input is T, or</li>
 <li>Z when both inputs are Z, or</li>
 <li>F when one input is F and the other is F/Z, or</li>
 <li>X otherwise.</li>
</ul>

<p>We use this to model what happens when multiple signals are connected in a
wired-or arrangement.</p>

<p>The full truth table is shown below.  It intentionally corresponds to the
Verilog semantics for wired ors (Section 4.6.2 of the Verilog
specification).</p>

<code>
       |   F   T   X   Z  |
  -----+------------------+
    F  |   F   T   X   F  |
    T  |   T   T   T   T  |
    X  |   X   T   X   X  |
    Z  |   F   T   X   Z  |
  -----+------------------+
</code>"

  (defun 4v-wor (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (4vcases a
           (t (4vt))
           (f (4vcases b
                (z (4vf))
                (& (4v-fix b))))
           (z (4v-fix b))
           (& (4vcases b
                (t (4vt))
                (& (4vx)))))
         :exec
         (cond ((eq a (4vt)) (4vt))
               ((eq b (4vt)) (4vt))
               ((eq a (4vf))
                (if (or (eq b (4vf))
                        (eq b (4vz)))
                    (4vf)
                  (4vx)))
               ((eq a (4vz))
                (if (or (eq b (4vf))
                        (eq b (4vz)))
                    b
                  (4vx)))
               (t
                (4vx)))))

  (defthm 4v-wor-truth-table
    ;; "Correctness" of 4v-wor, w.r.t. Table 4-4 of the Verilog spec.
    (and (equal (4v-wor (4vf) (4vf)) (4vf))
         (equal (4v-wor (4vf) (4vt)) (4vt))
         (equal (4v-wor (4vf) (4vx)) (4vx))
         (equal (4v-wor (4vf) (4vz)) (4vf))

         (equal (4v-wor (4vt) (4vf)) (4vt))
         (equal (4v-wor (4vt) (4vt)) (4vt))
         (equal (4v-wor (4vt) (4vx)) (4vt))
         (equal (4v-wor (4vt) (4vz)) (4vt))

         (equal (4v-wor (4vx) (4vf)) (4vx))
         (equal (4v-wor (4vx) (4vt)) (4vt))
         (equal (4v-wor (4vx) (4vx)) (4vx))
         (equal (4v-wor (4vx) (4vz)) (4vx))

         (equal (4v-wor (4vz) (4vf)) (4vf))
         (equal (4v-wor (4vz) (4vt)) (4vt))
         (equal (4v-wor (4vz) (4vx)) (4vx))
         (equal (4v-wor (4vz) (4vz)) (4vz)))
    :rule-classes nil))



(def-ruleset 4v-op-defs '(4v-fix 4v-unfloat 4v-not 4v-and 4v-or 4v-xor 4v-iff
                                 4v-res 4v-ite 4v-ite* 4v-tristate 4v-pullup
                                 4v-wand 4v-wor))

(def-ruleset 4v-op-execs '((4v-fix$inline)
                           (4v-unfloat$inline)
                           (4v-not$inline)
                           (4v-and$inline)
                           (4v-or$inline)
                           (4v-xor$inline)
                           (4v-iff$inline)
                           (4v-res)
                           (4v-ite)
                           (4v-ite*)
                           (4v-tristate)
                           (4v-pullup)
                           (4v-wand)
                           (4v-wor)))


(defsection 4v-<=
  :parents (4v)
  :short "Four-valued lattice-ordering comparison."

  :long "<p>@(call 4v-<=) is true when A is B or X.</p>

<p>This is a partial ordering on the <see topic='@(url 4vp)'>four-valued
constants</see>.  We generally just write <tt>a &lt;= b</tt> instead of
<tt>(4v-&lt;= a b)</tt>.</p>

<p>We say that X is smaller than any other value.  Furthermore, this is
reflexive, i.e., <tt>A &lt;= A</tt> for any value <tt>A</tt>.  Finally,
there is no order imposed between T, F, and Z.</p>

<p>Drawn as a lattice, the picture is:</p>

<code>
   T     F     Z
    \\    |    /
      \\  |  /
        \\|/
         X
</code>

<p>This ordering plays a key role in @(see 4v-monotonicity).</p>"

  (definline 4v-<= (a b)
    (declare (xargs :guard t))
    (mbe :logic
         (let ((a (4v-fix a)))
           (or (eq a (4vx))
               (eq a (4v-fix b))))
         :exec
         (if (or (eq a (4vt))
                 (eq a (4vf))
                 (eq a (4vz)))
             (eq a b)
           t)))

  (defthm 4v-<=-x
    (4v-<= (4vx) x))

  (defthm 4v-<=-refl
    (4v-<= a a))

  (defthmd 4v-<=-trans1
    (implies (and (4v-<= a b)
                  (4v-<= b c))
             (4v-<= a c)))

  (defthmd 4v-<=-trans2
    (implies (and (4v-<= b c)
                  (4v-<= a b))
             (4v-<= a c)))

  (defthm 4v-<=-of-4v-fix-1
    (equal (4v-<= (4v-fix a) b)
           (4v-<= a b)))

  (defthm 4v-<=-of-4v-fix-2
    (equal (4v-<= a (4v-fix b))
           (4v-<= a b))))




(defsection 4v-monotonicity
  :parents (4v)
  :short "The monotonicity property satisfied by all @(see 4v-operations)."

;; Taken almost directly from Sol's fixpoint paper.

  :long "<p>All of our primitive four-valued operations satisfy the following
monotonicity property, where &lt;= denotes @(see 4v-<=):</p>

<box>
<p>Whenever a &lt;= b, f(a) &lt;= f(b).</p>
</box>

<p>A higher-arity function is monotonic if it is monotonic with respect to each
of its arguments, e.g., a binary function is monotonic if:</p>

<box>
<p>Whenever a1 &lt;= a2, f(a1, b1) &lt;= f(a2, b2), and<br/>
   Whenever b1 &lt;= b2, f(a1, b1) &lt;= f(a2, b2).</p>
</box>

<p>This monotonicity requirement ensures that our operations respect the
special status of X as an unknown.  For instance, an operation <tt>h</tt>
would not be monotonic if <tt>h(X) = T</tt> but <tt>h(T) = F</tt>.</p>

<p>Another way of looking at this is, if <tt>h</tt> is monotonic and we know
that <tt>h(X) = T</tt>, then this means that <tt>h(v) = T</tt> for <b>any</b>
value <tt>v</tt>, regardless of whether it is T, F, X, or Z.</p>

<p>On the other hand, if we only know that <tt>h(X) = X</tt>, then we cannot
conclude anything about <tt>h(T)</tt>.  It only means that if we are unsure of
the value of the input, then we are unsure of the value of the output.</p>"

  (defun p4vm-suffix-args (args)
    (declare (xargs :mode :program))
    (if (atom args)
        nil
      (cons (intern-in-package-of-symbol
             (concatenate 'string (symbol-name (car args)) "1")
             (car args))
            (p4vm-suffix-args (cdr args)))))

  (defun p4vm-4v-<=-args (args suff-args)
    (declare (xargs :mode :program))
    (if (atom args)
        nil
      (cons (list '4v-<= (car args) (car suff-args))
            (p4vm-4v-<=-args (cdr args) (cdr suff-args)))))

  (defmacro prove-4v-monotonic (fn args)
    (let ((suff-args (p4vm-suffix-args args)))
      `(defthm ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name fn) "-IS-MONOTONIC")
                 fn)
         (implies (and . ,(p4vm-4v-<=-args args suff-args))
                  (4v-<= (,fn . ,args)
                         (,fn . ,suff-args))))))

  (prove-4v-monotonic 4v-fix (a))
  (prove-4v-monotonic 4v-unfloat (a))
  (prove-4v-monotonic 4v-not (a))
  (prove-4v-monotonic 4v-and (a b))
  (prove-4v-monotonic 4v-or (a b))
  (prove-4v-monotonic 4v-xor (a b))
  (prove-4v-monotonic 4v-iff (a b))
  (prove-4v-monotonic 4v-res (a b))
  (prove-4v-monotonic 4v-ite (c a b))
  (prove-4v-monotonic 4v-ite* (c a b))
  (prove-4v-monotonic 4v-tristate (c a))
  (prove-4v-monotonic 4v-pullup (a))
  (prove-4v-monotonic 4v-wand (a b))
  (prove-4v-monotonic 4v-wor (a b)))


; BOZO document this stuff

(defstub 4v-lookup-not-found (key) nil)

(defun 4v-lookup-not-found-quiet (key)
  (declare (xargs :guard t)
           (ignore key))
  nil)

(defun 4v-lookup-not-found-complain (key)
  (declare (xargs :guard t))
  (cw "4v-lookup: key not found: ~x0~%" key))

(defmacro 4v-lookup-complain-when-not-found (arg)
  `(defattach 4v-lookup-not-found
     ,(if arg
          '4v-lookup-not-found-complain
        '4v-lookup-not-found-quiet)))

(4v-lookup-complain-when-not-found nil)

(defsection 4v-lookup
  :parents (4v)
  :short "Alist lookup that automatically @(see 4v-fix)es its result."
  :long "<p>BOZO this is a convenient operation for ...</p>"

  (defun 4v-lookup (k env)
    (declare (xargs :guard t))
    (mbe :logic (let ((look (hons-get k env)))
                  (if look (4v-fix (cdr look)) (4vx)))
         :exec (let ((look (hons-get k env)))
                 (prog2$ (and (not look) (4v-lookup-not-found k))
                         (4v-fix (cdr look))))))

  (defthm 4vp-of-4v-lookup
    (4vp (4v-lookup k env)))

  (defthm 4v-fix-4v-lookup
    (equal (4v-fix (4v-lookup k env))
           (4v-lookup k env))))



(defsection 4v-list-<=
  :parents (4v-<=)
  :short "Extension of @(see 4v-<=) to four-valued lists."

  :long "<p>We say X &lt;= Y for four-valued lists when:</p>

<ul>
 <li>Y is at least as long as X, and</li>
 <li>Xi &lt;= Yi for all i up to |X|.</li>
</ul>"

  (defun 4v-list-<= (x y)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (consp y)
           (4v-<= (car x) (car y))
           (4v-list-<= (cdr x) (cdr y)))))

  (encapsulate
    nil
    (local
     (defthm 4v-list-<=-nil
       (implies (4v-list-<= a nil)
                (and (not (equal (nth n a) (4vt)))
                     (not (equal (nth n a) (4vf)))
                     (not (equal (nth n a) (4vz)))))))

    (defthm 4v-list-<=-nth
      (implies (4v-list-<= a b)
               (4v-<= (nth n a) (nth n b)))
      :hints(("Goal"
              :in-theory (disable 4v-list-<=)
              :expand ((4v-list-<= a b)))))))


(defsection 4v-alist-<=
  :parents (4v-<=)
  :short "Extension of @(see 4v-<=) to four-valued alists."

  :long "<p>We say X &lt;= Y for four-valued alists (i.e., alists whose every
value is a four-valued constant), when X[k] &lt;= Y[k] for every key k.</p>"

  (defquant 4v-alist-<= (x y)
    (forall (k)
            (4v-<= (4v-lookup k x)
                   (4v-lookup k y))))

  (verify-guards 4v-alist-<=)

  (defexample 4v-alist-<=-4v-lookup-example
    :pattern (4v-lookup a b)
    :templates (a)
    :instance-rulename 4v-alist-<=-instancing)

  (defexample 4v-alist-<=-hons-assoc-equal-example
    :pattern (hons-assoc-equal a b)
    :templates (a)
    :instance-rulename 4v-alist-<=-instancing)

  (defthm 4v-alist-<=-nil
    (4v-alist-<= nil x)
    :hints ((witness)))

  (defthm 4v-alist-<=-refl
    (4v-alist-<= x x)
    :hints ((witness :ruleset 4v-alist-<=-witnessing)))

  (defthmd 4v-alist-<=-trans1
    (implies (and (4v-alist-<= a b)
                  (4v-alist-<= b c))
             (4v-alist-<= a c))
    :hints (("goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-alist-<=-witnessing)
            (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)))

  (defthmd 4v-alist-<=-trans2
    (implies (and (4v-alist-<= b c)
                  (4v-alist-<= a b))
             (4v-alist-<= a c))
    :hints (("goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-alist-<=-witnessing)
            (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)))

  (defthm 4v-alist-<=-acons
    (implies (and (4v-<= a b)
                  (4v-alist-<= al1 al2))
             (4v-alist-<= (cons (cons k a) al1)
                          (cons (cons k b) al2)))
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness)))

  (defthm 4v-alist-<=-list-with-x
    (4v-alist-<= (list (cons k (4vx))) x)
    :hints ((witness)))

  (defthm 4v-alist-<=-cons-x
    (4v-alist-<= (cons (cons k (4vx)) x) x)
    :hints ((witness)))

  (defthm 4v-alist-<=-acons-1
    (implies (not (hons-assoc-equal k a))
             (iff (4v-alist-<= (cons (cons k v) a) b)
                  (and (4v-<= v (4v-lookup k b))
                       (4v-alist-<= a b))))
    :hints (("goal" :in-theory (disable 4v-<= 4v-fix))
            (witness :ruleset 4v-alist-<=-witnessing)
            (and stable-under-simplificationp
                 (if (member-equal '(not (4v-alist-<= a b)) clause)
                     '(:use ((:instance 4v-alist-<=-necc
                                        (x a)
                                        (y b)
                                        (k k))
                             (:instance 4v-alist-<=-necc
                                        (x a)
                                        (y b)
                                        (k k0))))
                   '(:use ((:instance 4v-alist-<=-necc
                                      (x (cons (cons k v) a))
                                      (y b)
                                      (k k))
                           (:instance 4v-alist-<=-necc
                                      (x (cons (cons k v) a))
                                      (y b)
                                      (k k0)))))))))


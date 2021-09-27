; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))

(defxdoc expressions
  :parents (sv)
  :short "The <b>S</b>ymbolic <b>V</b>ector <b>Ex</b>pression language (SVEX)
forms the core of SV.  It includes an S-expression language for certain
pre-defined hardware functions, an interpreter for evaluating these expressions
on four-valued integers, and related tools.")

(xdoc::order-subtopics expressions
                       (values
                        functions
                        svex
                        evaluation))

(defxdoc values
  :parents (expressions)
  :short "Our expressions operate on four-valued bit vectors called @(see
4vec)s.  There are also useful subsets of @(see 4vec)s, such as @(see
3vec)s (which have no Z bits) and @(see 2vec)s (which have no X or Z bits).")

(xdoc::order-subtopics values (4vec 3vec 2vec))

(defsection 4vec
  :parents (values)
  :short "The fundamental 4-valued vector representation used throughout SV
@(see expressions)."

  :long "<p>In hardware description languages like Verilog and SystemVerilog,
each bit can typically take one of four values, named 1, 0, X, or Z.  For some
background see for instance the @(see acl2::4v) library and in particular @(see
acl2::why-4v-logic).</p>

<p>A <b>4vec</b> represents a ``infinite width'' vector of 4-valued bits, i.e.,
each bit of a 4vec can be either 1, 0, X, or Z.  4vecs are fundamental to the
@(see sv) expression representation: the variables in each expression are
4vec-valued, and each expression produces a result that is a 4vec.</p>

<p>The concrete representation of a 4vec is either:</p>

<ul>
<li>an integer (for special cases where there are no X/Z bits), or</li>
<li>a pair of integers, say @('(upper . lower)').</li>
</ul>

<p>In the latter case, the value of each 4-valued bit is determined by the
corresponding bits in the two integers:</p>

<ul>

<li>If the corresponding bits are equal, the resulting bit is the shared
value (1 or 0).</li>

<li>Otherwise, if the <i>upper</i> bit is 1 and the <i>lower</i> 0, then the
resulting value is X.</li>

<li>Otherwise, the <i>upper</i> bit is 0 and the <i>lower</i> 1, then the
resulting value is Z.</li>

</ul>

<p>Examples:</p>

<table>
<tr><th>Representation</th><th>Meaning (LSB first)</th></tr>
<tr><td>6</td>        <td>0,1,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>-13</td>      <td>1,1,0,0,1,1,...infinitely many 1s...</td></tr>
<tr><td>(6 . -13)</td><td>Z,1,X,0,Z,Z,...infinitely many Zs...</td></tr>
</table>

<p>A 4vec should generally be @(see hons)ed if it is going to be used in an
expression, but it is better to avoid the expense of honsing ephemeral 4vecs,
e.g., those that arise during evaluation.  Accordingly we provide both @(see
make-4vec) and @(see make-honsed-4vec).</p>

<p>We provide a @('4vec') @(see b*) binder that allows you to access, e.g.,</p>

@({
      (b* (((4vec x)))          ==   (list :lower (4vec->lower x)
        (list :lower x.lower               :upper (4vec->upper x))
              :upper x.upper))
})")

(defxdoc 4vec-examples
  :parents (4vec)
  :short "@(see 4vec) examples"
  :long "
<p>@(see 4vec) Examples.  Note that some of them are redundant, but they are
  repeated so that the reader can more easily see the relationships between the
  bits.</p>

<table>
<tr><th>Representation</th><th>Meaning (LSB first)</th></tr>
<tr><td>1</td>      <td>1,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>0</td>      <td>0,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>(1 . 0)</td><td>X,0,0,0,0,0,...infinitely many 0s...</td></tr>

<tr><td>0</td>      <td>0,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>1</td>      <td>1,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>(0 . 1)</td><td>Z,0,0,0,0,0,...infinitely many 0s...</td></tr>

<tr><td>-1</td>      <td>1,1,1,1,1,1....infinitely many 1s...</td></tr>
<tr><td>0</td>       <td>0,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>(-1 . 0)</td><td>X,X,X,X,X,X,...infinitely many Xs...</td></tr>

<tr><td>0</td>       <td>0,0,0,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>-1</td>      <td>1,1,1,1,1,1,...infinitely many 1s...</td></tr>
<tr><td>(0 . -1)</td><td>Z,Z,Z,Z,Z,Z,...infinitely many Zs...</td></tr>


<tr><td>4</td>      <td>0,0,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>6</td>      <td>0,1,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>(4 . 6)</td><td>0,Z,1,0,0,0,...infinitely many 0s...</td></tr>

<tr><td>4</td>      <td>0,0,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>-6</td>     <td>0,1,0,1,1,1,...infinitely many 1s...</td></tr>
<tr><td>(4. -6)</td><td>0,Z,X,Z,Z,Z,...infinitely many Zs...</td></tr>

<tr><td>-4</td>      <td>0,0,1,1,1,1....infinitely many 1s...</td></tr>
<tr><td>6</td>       <td>0,1,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>(-4 . 6)</td><td>0,Z,1,X,X,X,...infinitely many Xs...</td></tr>

<tr><td>-4</td>       <td>0,0,1,1,1,1....infinitely many 1s...</td></tr>
<tr><td>-6</td>       <td>1,1,1,1,1,1,...infinitely many 1s...</td></tr>
<tr><td>(-4 . -6)</td><td>Z,Z,1,1,1,1,...infinitely many 1s...</td></tr>


<tr><td>6</td>       <td>0,1,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>13</td>      <td>1,0,1,1,0,0,...infinitely many 0s...</td></tr>
<tr><td>(6 . 13)</td><td>Z,X,1,Z,0,0,...infinitely many 0s...</td></tr>

<tr><td>6</td>       <td>0,1,1,0,0,0,...infinitely many 0s...</td></tr>
<tr><td>-13</td>     <td>1,1,0,0,1,1,...infinitely many 1s...</td></tr>
<tr><td>(6. -13)</td><td>Z,1,X,0,Z,Z,...infinitely many Zs...</td></tr>

<tr><td>-6</td>       <td>0,1,0,1,1,1....infinitely many 1s...</td></tr>
<tr><td>13</td>       <td>1,0,1,1,0,0,...infinitely many 0s...</td></tr>
<tr><td>(-6 . 13)</td><td>Z,X,Z,1,X,X,...infinitely many Xs...</td></tr>

<tr><td>-6</td>        <td>0,1,0,1,1,1....infinitely many 1s...</td></tr>
<tr><td>-13</td>       <td>1,1,0,0,1,1,...infinitely many 1s...</td></tr>
<tr><td>(-6 . -13)</td><td>Z,1,0,X,1,1,...infinitely many 1s...</td></tr>

</table>
")

(local (xdoc::set-default-parents 4vec))

(define 4vec-p (x)
  :short "Recognizer for @(see 4vec)s."
  (or (integerp x)
      (and (consp x)
           (integerp (car x))
           (integerp (cdr x))
           (not (equal (car x) (cdr x)))))
  ///
  (defthmd 4vec-p-when-integerp
    (implies (integerp x)
             (4vec-p x))))


(local (in-theory (enable 4vec-p)))

(defsection make-4vec
  :short "Raw constructor for @(see 4vec)s, using @(see cons)."
  :long "<p>@(call make-4vec) builds a 4vec with the given @('upper') and
@('lower').</p>

@(def make-4vec)"

  (defund 4vec (upper lower)
    (declare (xargs :guard (and (integerp upper)
                                (integerp lower))))
    (b* (((the integer upper) (lifix upper))
         ((the integer lower) (lifix lower)))
      (if (eql upper lower)
          upper
        (cons upper lower))))

  (defmacro make-4vec (&key upper lower)
    `(4vec ,upper ,lower))

  (add-macro-alias make-4vec 4vec)

  (local (in-theory (enable make-4vec)))

  (defthm 4vec-p-of-4vec
    (equal (4vec-p (make-4vec :upper upper :lower lower))
           t)))

(local (in-theory (enable make-4vec)))

(defsection make-honsed-4vec
  :short "Raw constructor for @(see 4vec)s, using @(see hons)."
  :long "<p>@(call make-honsed-4vec) is identical to @(see make-4vec) except
that it uses @(see hons) instead of @(see cons).  This is generally what you
want when building @(see expressions).</p>

@(def make-honsed-4vec)"

  (defun honsed-4vec (upper lower)
    (declare (xargs :guard (and (integerp upper)
                                (integerp lower))))
    (mbe :logic
         (make-4vec :upper upper
                    :lower lower)
         :exec
         (b* ((upper (lifix upper))
              (lower (lifix lower)))
           (if (eql upper lower)
               upper
             (hons upper lower)))))

  (defmacro make-honsed-4vec (&key upper lower)
    `(honsed-4vec ,upper ,lower)))

(defsection 4vec-x
  :parents (values)
  :short "Infinite width vector, all Xes."
  :long "@(def *4vec-x*) @(def 4vec-x)"
  (defconst *4vec-x* (make-honsed-4vec :upper -1 :lower 0))
  (defmacro 4vec-x () `',*4vec-x*))

(defsection 4vec-z
  :parents (values)
  :short "Infinite width vector, all Zs."
  :long "@(def *4vec-z*) @(def 4vec-z)"
  (defconst *4vec-z* (make-honsed-4vec :upper 0 :lower -1))
  (defmacro 4vec-z () `',*4vec-z*))

(defsection 4vec-1x
  :parents (values)
  :short "Vector with a single X bit (lsb), upper bits all 0."
  :long "@(def *4vec-1x*) @(def 4vec-1x)"
  (defconst *4vec-1x* (make-honsed-4vec :upper 1 :lower 0))
  (defmacro 4vec-1x () `',*4vec-1x*))

(defsection 4vec-1z
  :parents (values)
  :short "Vector with a single Z bit (lsb), upper bits all 0."
  :long "@(def *4vec-1z*) @(def 4vec-1z)"
  (defconst *4vec-1z* (make-honsed-4vec :upper 0 :lower 1))
  (defmacro 4vec-1z () `',*4vec-1z*))


(define 4vec-fix ((x 4vec-p))
  :short "Fix an arbitrary object to a @(see 4vec)."
  :inline t
  :prepwork ((local (in-theory (disable (force)))))
  :returns (newx 4vec-p)
  (mbe :logic (if (consp x)
                  (4vec (ifix (car x))
                        (ifix (cdr x)))
                (if (integerp x)
                    x
                  (4vec-x)))
       ;; (4vec (ifix (4vec->upper x))
       ;;       (ifix (4vec->lower x)))
       :exec x)
  ///
  (defthm 4vec-fix-of-4vec
    (implies (4vec-p x)
             (equal (4vec-fix x) x))))

(defsection 4vec-equiv
  :short "Equivalence relation for @(see 4vec)s."
  (deffixtype 4vec
    :pred 4vec-p
    :fix 4vec-fix
    :equiv 4vec-equiv
    :define t
    :forward t))

(fty::defoption maybe-4vec 4vec)

(local (in-theory (enable 4vec-fix 4vec-equiv)))

(define 4vec->upper ((x 4vec-p))
  :short "Raw accessor for the upper integer from a @(see 4vec)."
  :inline t
  :returns (upper integerp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (if (consp x)
                  (ifix (car x))
                (if (integerp x)
                    x
                  -1))
       :exec (if (consp x) ;; testing consp is likely faster than integerp
                 (car x)
               x))
  ///
  (defthm 4vec->upper-of-4vec
    (equal (4vec->upper (4vec upper lower))
           (ifix upper)))

  (defthm 4vec->upper-of-4vec-fix
    (equal (4vec->upper (4vec-fix x))
           (4vec->upper x)))

  (defcong 4vec-equiv equal (4vec->upper x) 1))


(define 4vec->lower ((x 4vec-p))
  :short "Raw accessor for the lower integer from a @(see 4vec)."
  :returns (lower integerp :rule-classes (:rewrite :type-prescription))
  :inline t
  (mbe :logic (if (consp x)
                  (ifix (cdr x))
                (if (integerp x)
                    x
                  0))
       :exec (if (consp x) ;; testing consp is likely faster than integerp
                 (cdr x)
               x))
  ///
  (defthm 4vec->lower-of-4vec
    (equal (4vec->lower (4vec upper lower))
           (ifix lower)))

  (defthm 4vec->lower-of-4vec-fix
    (equal (4vec->lower (4vec-fix x))
           (4vec->lower x)))

  (defcong 4vec-equiv equal (4vec->lower x) 1))

(local (in-theory (enable 4vec->upper 4vec->lower)))


(defsection 4vec-basics
  :extension (make-4vec)

  (defthm 4vec-of-fields
    (4vec-equiv (4vec (4vec->upper x) (4vec->lower x))
                x)
    :hints(("Goal" :in-theory (enable 4vec-fix 4vec-equiv))))

  (defthmd 4vec-fix-is-4vec-of-fields
    (equal (4vec-fix x)
           (4vec (4vec->upper x) (4vec->lower x)))
    :hints(("Goal" :in-theory (enable 4vec-fix))))

  (defthm 4vec-elim
    (implies (4vec-p x)
             (equal (4vec (4vec->upper x) (4vec->lower x))
                    x))
    :rule-classes :elim)

  (def-b*-binder 4vec
    :body
    (std::da-patbind-fn '4vec '((upper . 4vec->upper)
                                (lower . 4vec->lower))
                        args acl2::forms acl2::rest-expr))

  (defthm 4vec-equal
    (equal (equal (4vec upper lower) x)
           (and (4vec-p x)
                (equal (4vec->upper x) (ifix upper))
                (equal (4vec->lower x) (ifix lower))))
    :hints(("Goal" :in-theory (e/d (4vec-fix))))))


(define 2vec-p ((x 4vec-p))
  :parents (2vec)
  :short "Recognizer for @(see 2vec)s."
  :returns bool
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (e/d (4vec-p 4vec->upper 4vec->lower 4vec-fix))))
  (mbe :logic
       (equal (4vec->upper x)
              (4vec->lower x))
       :exec
       ;; Testing atom is likely faster than integerp
       (atom x))
  ///
  (defthm 4vec->lower-when-2vec-p
    (implies (2vec-p x)
             (equal (4vec->lower x)
                    (4vec->upper x))))

  (deffixequiv 2vec-p))

(define 2vec ((x integerp))
  :parents (values)
  :short "A <b>2vec</b> is a @(see 4vec) that has no X or Z bits."
  :long "<p>@('2vec') constructs a 2vec from an integer; @('2vec-p') recognizes
a 2vec; @('2vec->val') gets the integer value out of a 2vec.</p>"
  :inline t
  :guard-hints (("goal" :in-theory (enable 4vec)))
  (mbe :logic (4vec x x)
       :exec x)
  ///
  (defthm 4vec-p-of-2vec
    (4vec-p (2vec x)))

  (defthm 4vec->upper-of-2vec
    (equal (4vec->upper (2vec x))
           (ifix x)))

  (defthm 4vec->lower-of-2vec
    (equal (4vec->lower (2vec x))
           (ifix x)))

  (defthm equal-of-2vec
    (equal (equal (2vec x) y)
           (and (4vec-p y)
                (equal (4vec->upper y) (ifix x))
                (equal (4vec->lower y) (ifix x)))))

  (deffixequiv 2vec))

(define 2vec->val ((x (and (4vec-p x)
                           (2vec-p x))))
  :parents (2vec)
  :short "Extract the upper/lower value (both the same) from a 2vec."
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable 4vec->upper 4vec->lower 4vec-p)))
  (mbe :logic (4vec->upper x)
       :exec x))


(defsection if-2vec-p
  :parents (2vec)
  :short "Helper macro for writing optimized @(see 4vec-operations)."

  :long "<p>@(call if-2vec-p) is a macro for writing @(see 4vec) operations.
Most of these operations can be optimized in the case where their arguments are
two-valued.  In the logic, this simply expands to @('4vec-body').  In the
execution, it checks whether all of the arguments are @(see 2vec)s (which is
fast), if so executes @('2vec-body'), and otherwise executes
@('4vec-body').</p>"

  (defmacro if-2vec-p (vars 2vec-body 4vec-body)
    `(mbe :logic ,4vec-body
          :exec (if (and . ,(pairlis$ (replicate (len vars) '2vec-p)
                                      (pairlis$ vars nil)))
                    ,2vec-body
                  ,4vec-body))))


(deflist 4veclist
  :elt-type 4vec
  :true-listp t
  :parents (4vec))



;; BOZO maybe should become a type like 2vecnatp?
;; BOZO document me
(define 4vec-index-p ((x 4vec-p))
  (and (2vec-p x)
       (<= 0 (2vec->val x)))
  ///
  (defthm 4vec-index-p-implies
    (implies (4vec-index-p x)
             (and (equal (4vec->lower x) (4vec->upper x))
                  (<= 0 (4vec->lower x))))
    :rule-classes :forward-chaining)
  (deffixequiv 4vec-index-p))

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
(include-book "4vec-base")
(include-book "centaur/misc/universal-equiv" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(defsection 3vec
  :parents (values)
  :short "A <b>3vec</b> is a @(see 4vec) that has no Z bits."

  :long "<p>In hardware modeling, Z bits (floating/undriven wires) are:</p>

<ol>

<li>relatively rare&mdash;for instance, an AND gate will never produce a Z
value.</li>

<li>often indistinguishable from X&mdash;for instance, if we give an undriven
input to an OR gate, the hardware may interpret it as either a 0 or as a 1, so
we may as well supplied an X instead.</li>

</ol>

<p>In most of our @(see 4vec-operations), we account for the second property by
first ``unfloating'' our inputs, e.g., with @(see 3vec-fix).  But since Z
values are relatively rare in the first place, this unfloating is often
unnecessary.  That is, in a circuit like:</p>

@({
       (OR A (AND B C))
})

<p>we can tell, statically, that we don't need to unfloat the result of the
@('(AND B C)') when computing the OR, because the AND can never produce a Z
value anyway.  This turns out to be a useful optimization during
bit-blasting.</p>")

(define 3vec-p ((x 4vec-p))
  :parents (3vec)
  :short "Recognizer for @(see 3vec)s (with a @(see 4vec-p) guard)."
  :guard-hints(("Goal" :in-theory (enable 4vec)))
  :returns bool
  (mbe :logic
       (b* (((4vec x) x))
         (eql (logand x.lower (lognot x.upper)) 0))
       :exec
       (if (atom x)
           t
         (b* (((4vec x) x))
           (eql (logandc2 x.lower x.upper) 0))))
  ///
  (defthm 3vec-p-implies-bits
    (and (implies (and (3vec-p x)
                       (not (logbitp n (4vec->upper x))))
                  (not (logbitp n (4vec->lower x))))
         (implies (and (3vec-p x)
                       (logbitp n (4vec->lower x)))
                  (logbitp n (4vec->upper x))))
    :hints (("goal" :use
             ((:instance bitops::logbitp-of-logand
               (acl2::a n)
               (x       (4vec->lower x))
               (acl2::y (lognot (4vec->upper x)))))
             :in-theory (disable bitops::logbitp-of-logand))))

  (deffixequiv 4vec-p))

(defsection 3vec-p!
  :parents (3vec)
  :short "Recognizer for @(see 3vec) (without a @(see 4vec-p) guard)."
  :long "@(def 3vec-p!)"
  (defmacro 3vec-p! (x)
    `(and (4vec-p ,x)
          (3vec-p ,x))))

(define 3vec-fix ((x 4vec-p))
  :parents (3vec)
  :short "Coerces an arbitrary @(see 4vec) to a @(see 3vec) by ``unfloating''
it, i.e., by turning any Zs into Xes."

  :long "<p>In most logic gates, e.g., AND gates, inputs that are Z are treated
just the same as inputs that are X.  So, when we define @(see 4vec-operations)
like @(see 4vec-bitand), we typically just:</p>

<ul>
<li>Define a @(see 3vec) version of the operation, then</li>
<li>Invoke the 3vec version on the unfloats of the inputs.</li>
</ul>"

  :verify-guards nil
  :returns (x-fix 3vec-p! :hints (("Goal" :in-theory (enable 3vec-p))
                                  (acl2::equal-by-logbitp-hammer)))
  (if-2vec-p (x)
             (2vec (2vec->val x))
             (mbe :logic (b* (((4vec x) x))
                           (4vec (logior x.upper x.lower)
                                 (logand x.upper x.lower)))
                  :exec (if (3vec-p x)
                            x
                          (b* (((4vec x) x))
                            (4vec (logior x.upper x.lower)
                                  (logand x.upper x.lower))))))
  ///

  (local (defthm logand-lognot-implies
           (implies (equal (logand x (lognot y)) 0)
                    (and (equal (logand x y) (ifix x))
                         (equal (logior x y) (ifix y))))
           :hints ((acl2::equal-by-logbitp-hammer)
                   (and stable-under-simplificationp
                        '(:use ((:instance bitops::logbitp-of-logand
                                 (acl2::a bit)
                                 (acl2::x x)
                                 (acl2::y (lognot y)))))))))

  (defthm 3vec-fix-of-3vec-p
    (implies (3vec-p x)
             (equal (3vec-fix x)
                    (4vec-fix x)))
    :hints(("Goal" :in-theory (e/d (3vec-p)
                                   ((force))))))

  (verify-guards 3vec-fix
    :hints (("goal" :use 3vec-fix-of-3vec-p)))

  (deffixequiv 3vec-fix)

  (defthm 3vec-fix-idempotent
    (equal (3vec-fix (3vec-fix x)) (3vec-fix x))
    :hints ((acl2::logbitp-reasoning
             :add-hints (:in-theory (enable acl2::b-ior))))))

(defsection 3vec-equiv
  :parents (3vec)
  :short "Equivalence up to @(see 3vec-fix)."

  (local (in-theory (enable 3vec-fix)))

  (deffixtype 3vec
    :pred 3vec-p!
    :fix 3vec-fix
    :equiv 3vec-equiv
    :define t
    :forward t)

  ;; (acl2::def-universal-equiv 3vec-equiv
  ;;   :equiv-terms ((equal (3vec-fix x))))

  (local (in-theory (enable 3vec-equiv)))

  (defrefinement 4vec-equiv 3vec-equiv
    :hints(("Goal" :in-theory (enable 4vec-fix-is-4vec-of-fields)))))

(define 3vec-fix-fast ((x 3vec-p!))
  :parents (3vec)
  :short "Logically just @(see 3vec-fix), but guarded with @(see 3vec-p) so
that in the execution this is just the identity."
  :enabled t
  :inline t
  (mbe :logic (3vec-fix x)
       :exec x))



(defsection 2vecx
  :parents (values)
  :short "A <b>2vecx</b> is a @(see 4vec) that is either a @(see 2vec) or is
all Xes."

  :long "<p>In the Verilog semantics, many of the more interesting vector
operations (e.g., addition, multiplication, etc.) have a special X propagation
behavior where, if any bit of any input is X or Z, then the entire result is
X.</p>

<p>The <b>2vecx</b>'es are a subset of the @(see 4vec)s that capture this idea.
That is, the result of an operation like addition is surely a 2vecx.</p>")

(define 2vecx-p ((x 4vec-p))
  :parents (2vecx)
  :short "Recognizer for @(see 2vecx)es, with a @(see 4vec-p) guard."
  :guard-hints(("Goal" :in-theory (enable 4vec-p 4vec)))
  (mbe :logic (let ((x (4vec-fix x)))
                (or (2vec-p x)
                    (equal x (4vec-x))))
       :exec
       (or (atom x)
           (equal x (4vec-x)))))

(defsection 2vexc-p!
  :parents (2vecx)
  :short "Recognizer for @(see 2vecx)es, without even a @(see 4vec-p) guard."
  :long "@(def 2vecx-p!)"
  (defmacro 2vecx-p! (x)
    `(and (4vec-p ,x)
          (2vecx-p ,x))))

(define 2vecx-fix ((x 4vec-p))
  :parents (2vecx)
  :short "Coerces an arbitrary @(see 4vec) to a @(see 2vecx), by forcing any
non-@(see 2vec)s to an just be infinite Xes."
  :returns (x-fix 2vecx-p!
                  :hints(("Goal" :in-theory (enable 2vecx-p))))
  :inline t
  (if (2vec-p x)
      (4vec-fix x)
    (4vec-x))
  ///
  (local (in-theory (enable 2vecx-p)))

  (defthm 2vecx-fix-of-2vecx-p
    (implies (2vecx-p x)
             (equal (2vecx-fix x)
                    (4vec-fix x))))

  (deffixequiv 2vecx-fix
    :args ((x 3vec))
    :hints(("Goal" :in-theory (enable 3vec-fix))
           (acl2::logbitp-reasoning
            :add-hints
            (:in-theory (enable* acl2::logbitp-case-splits
                                 bitops::logbitp-of-const-split
                                 acl2::b-and
                                 acl2::b-ior))))))

(def-universal-equiv 2vecx-equiv
  :equiv-terms ((equal (2vecx-fix x)))
  :parents (2vecx)
  :short "Equivalence up to @(see 2vecx-fix).")

(defsection 2vecx-equiv-thms
  :extension (2vecx-equiv)
  ;; bozo would be nice for def-universal-equiv to support ///

  (local (in-theory (enable 2vecx-equiv)))

  (defrefinement 3vec-equiv 2vecx-equiv
    :hints(("Goal" :in-theory (disable 2vecx-fix))))

  (defcong 2vecx-equiv equal (2vecx-fix x) 1)

  (deffixtype 2vecx
    :pred 2vecx-p!
    :fix 2vecx-fix
    :equiv 2vecx-equiv))


(defsection 2vecnatx
  :parents (values)
  :short "A <b>2vecnatx</b> is a @(see 4vec) that is either a natural-valued
@(see 2vec) or is all Xes.")

(define 2vecnatx-p ((x 4vec-p))
  :parents (2vecnatx)
  :short "Recognizer for @(see 2vecnatx)es, with a @(see 4vec-p) guard."
  :inline t
  (mbe :logic
       (let ((x (4vec-fix x)))
         (or (and (2vec-p x)
                  (<= 0 (2vec->val x)))
             (equal x (4vec-x))))
       :exec
       (if (2vec-p x)
           (<= 0 (2vec->val x))
         (equal x (4vec-x)))))

(defsection 2vecnatx-p!
  :parents (2vecnatx)
  :short "Recognizer for @(see 2vecnatx)es, without even a @(see 4vec-p) guard."
  :long "@(def 2vecnatx-p!)"
  (defmacro 2vecnatx-p! (x)
    `(and (4vec-p ,x)
          (2vecnatx-p ,x))))

(define 2vecnatx-fix ((x 4vec-p))
  :parents (2vecnatx)
  :short "Coerces an arbitrary @(see 4vec) into a @(see 2vecnatx), by forcing
any non-naturals to all Xes."
  :returns (fix 2vecnatx-p! :hints(("Goal" :in-theory (enable 2vecnatx-p))))
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (4vec-fix x)
    (4vec-x))
  ///
  (local (in-theory (enable 2vecnatx-p)))

  (defthm 2vecnatx-fix-of-2vecnatx-p
    (implies (2vecnatx-p x)
             (equal (2vecnatx-fix x)
                    (4vec-fix x))))

  (deffixequiv 2vecnatx-fix :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix))
           (acl2::logbitp-reasoning))))

(def-universal-equiv 2vecnatx-equiv
  :equiv-terms ((equal (2vecnatx-fix x)))
  :parents (2vecnatx)
  :short "Equivalence up to @(see 2vecnatx-fix).")

(defsection 2vecnatx-equiv-thms
  :extension (2vecnatx-equiv)
  ;; bozo would be nice for def-universal-equiv to support ///

  (local (in-theory (enable 2vecnatx-equiv)))

  (defrefinement 2vecx-equiv 2vecnatx-equiv
    :hints(("Goal" :in-theory (disable 2vecnatx-fix))))

  (defcong 2vecnatx-equiv equal (2vecnatx-fix x) 1)

  (deffixtype 2vecnatx
    :pred 2vecnatx-p!
    :fix 2vecnatx-fix
    :equiv 2vecnatx-equiv))

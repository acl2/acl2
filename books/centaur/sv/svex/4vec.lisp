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
(include-book "4vec-subtypes")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "centaur/4v-sexpr/4v-logic" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)
(include-book "centaur/bitops/parity" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


;; Probably these are specialized enough that they shouldn't be integrated into
;; bitops?  Or maybe they should go into some heavier bitops book like
;; ihs-extensions?

(local (defthm equal-neg-1-when-logcdr
         (implies (and (logbitp 0 x)
                       (integerp x))
                  (equal (equal (logcdr x) -1)
                         (equal x -1)))
         :hints ((acl2::equal-by-logbitp-hammer))))

(local (defthm equal-0-when-logcdr
         (implies (and (not (logbitp 0 x))
                       (integerp x))
                  (equal (equal (logcdr x) 0)
                         (equal x 0)))
         :hints ((acl2::equal-by-logbitp-hammer))))

(local (defthm logior-of-three-negative-1
         (implies (equal (logior a b) -1)
                  (equal (logior a b c) -1))
         :hints (("goal" :use ((:instance bitops::associativity-of-logior
                                (acl2::a a) (acl2::b b) (acl2::c c)))
                  :in-theory (disable bitops::associativity-of-logior)))))

(local (defthm logior-neg-1-when-logand-neg-1
         (implies (equal (logand a b) -1)
                  (equal (logior a b) -1))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))



(defsection 4vec-operations
  :parents (functions 4vec)
  :short "Core operations on @(see 4vec)s."

  :long "<p>We now introduce many operations on @(see 4vec)s.  These operations
are generally intended to support the modeling of Verilog and SystemVerilog
expressions.  For instance, our @(see 4vec-plus) operation agrees with the
Verilog notion of plus: if there are any X or Z bits in either input, it
``conservatively'' returns all Xes.  Most of these operations have
corresponding @(see svex) @(see functions) and can hence be used in @(see
expressions).</p>

<p>Many of these operations have similarities with the @(see
acl2::4v-operations) which were used in @(see acl2::esim).  But SV expressions
are vectors instead of single bits, so there are many 4vec operations with no
4v equivalents (e.g., plus, times, etc.).  Historically these operations were
bit-blasted using the @(see vl2014::occform) transformation, but in svex they
are primitives with well-defined semantics.</p>

<p><u>Boolean Convention</u>.  Most 4vec operations take and return @(see 4vec)
objects&mdash;even comparisons, reductions, etc., which you might instead
expect to produce a Boolean result.  In these cases, we typically arrange so
that ``true'' is indicated by the all-1s vector (i.e., -1), ``false'' is
indicated by the all-0s vector (i.e., 0), and undetermined values are indicated
by the all-Xes vector.  This is sometimes convenient in that it avoids needing
to explicitly replicate/extend comparison results.</p>

<p>It is critical that these functions support efficient symbolic simulation
with @(see gl).  However, the logical definitions of these functions are
typically not relevant to this, because we use a custom translation from @(see
expressions) into @(see acl2::aig)s; see @(see bit-blasting) for details.</p>")

(xdoc::defpointer boolean-convention 4vec-operations)

(local (xdoc::set-default-parents 4vec-operations))

(define 4vec-idx->4v
  :short "Like @(see logbit) for @(see 4vec)s, for fixed indices, producing an
@(see acl2::4v)-style @(see acl2::4vp)."
  ((n natp   "The bit position to extract.")
   (x 4vec-p "The @(see 4vec) to extract it from."))
  :returns (bit acl2::4vp)
  :long "<p>This function is mainly used in correspondence theorems that show
the relationship between our @(see 4vec-operations) and the simple, four-valued
bit operations provided in the @(see acl2::4v) library.</p>"
  (b* (((4vec x))
       (n (lnfix n)))
    (if (logbitp n x.upper)
        (if (logbitp n x.lower)
            (acl2::4vt)
          (acl2::4vx))
      (if (logbitp n x.lower)
          (acl2::4vz)
        (acl2::4vf))))
  ///
  (deffixequiv 4vec-idx->4v)

  (defthm 4vec-idx->4v-when-3vec-p
    (implies (3vec-p x)
             (not (equal (4vec-idx->4v n x) 'z)))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-idx->4v)
            :use ((:instance bitops::logbitp-of-logand
                   (acl2::a n) (x (4vec->lower x)) (acl2::y (lognot (4vec->upper x))))))))

  (defthm 4vec-idx->4v-of-3vec-fix
    (equal (4vec-idx->4v n (3vec-fix x))
           (let ((x4v (4vec-idx->4v n x)))
             (if (eq x4v 'z)
                 'x
               x4v)))
    :hints(("Goal" :in-theory (enable 3vec-fix)))))


(define 4vec-bit-index
  :short "Like @(see logbit) for @(see 4vec)s; the bit position must be a @(see
natp)."
  ((n natp   "The bit position to extract.")
   (x 4vec-p "The @(see 4vec) to extract it from."))
  :returns (bit 4vec-p)
  :long "<p>We extract the @('n')th bit of @('x') as a new @(see 4vec).</p>

<p>We require that @('n') is a @(see natp) instead of a @(see 4vec), which
makes this function suitable for modeling simple Verilog indexing expressions
such as @('foo[3]'), but not for dynamic bit selects such as @('foo[i]').</p>

<p>For a more general (but less efficient) function that drops this restriction
and allows @('n') to be a @(see 4vec), see @(see 4vec-bit-extract).</p>"
  (if-2vec-p (x)
             (2vec (logbit (lnfix n) (2vec->val x)))
             (make-4vec :upper (logbit (lnfix n) (4vec->upper x))
                        :lower (logbit (lnfix n) (4vec->lower x))))
  ///
  (deffixequiv 4vec-bit-index))


(define 4vec-bit-extract
  :short "Like @(see logbit) for @(see 4vec)s; the bit position may be a @(see
4vec)."
  ((n 4vec-p "The bit position to extract.")
   (x 4vec-p "The @(see 4vec) to extract it from."))
  :returns (res 4vec-p)
  :long "<p>We extract the @('n')th bit of @('x') as a new @(see 4vec).</p>

<p>Here @('n') itself can also be a @(see 4vec).  This flexibility is often not
necessary.  When possible, it is generally better (more efficient) to use @(see
4vec-bit-index), which requires @('n') to be a @(see natp).  When @('n')
happens to be a natural, i.e., a @(see 2vec), both functions compute the same
result.</p>

<p>When @('n') is negative or isn't two-valued, i.e., it has some X or Z bit
somewhere, then we simply return a one-bit X value.  This agrees to the Verilog
semantics for @('foo[n]') in cases where @('n') is unknown.</p>"
  (if (and (2vec-p n)
           (<= 0 (2vec->val n)))
      (4vec-bit-index (2vec->val n) x)
    (4vec-1x))
  ///
  (deffixequiv 4vec-bit-extract))


(define bool->vec ((x booleanp))
  :short "Convert an ACL2 @(see booleanp) into a @(see 4vec) according to the
@(see boolean-convention)."
  :inline t
  (if x -1 0)
  ///
  (defthm bool->vec-cases
    (and (implies x
                  (equal (bool->vec x) -1))
         (implies (not x)
                  (equal (bool->vec x) 0)))))


(defsection 3vec-operations
  :parents (functions)
  :short "Core operations on @(see 3vec)s."

  :long "<p>You can mostly think of these as utility functions for defining
@(see 4vec-operations).  Many operations on 4vecs treat X and Z input bits the
same.  In these cases, for instance in @(see 4vec-bitand), we typically define
the 4vec operation to simply:</p>

<ul>
<li>``unfloating'' its inputs using @(see 3vec-fix), and then</li>
<li>invoke a simpler @(see 3vec) operation on the unfloated inputs.</li>
</ul>")


;; [Jared] this doesn't seem to be used?  trying to get rid of it
;; (acl2::def-b*-binder 3vecf
;;   :body
;;   #!acl2
;;   `(b* ((,(car args) (sv::3vec-fix-fast ,(car forms)))
;;         ((sv::4vec ,(car args)) ,(car args)))
;;      ,rest-expr))


(define 3vec-bitnot ((x 4vec-p))
  :parents (3vec-operations)
  :short "Bitwise logical NOT of a @(see 3vec)."
  :returns (~x 4vec-p)
  (if-2vec-p
   (x)
   (2vec (lognot (2vec->val x)))
   (b* (((4vec x)))
     (4vec (lognot x.lower)
           (lognot x.upper))))
  ///
  (defret 3vec-p-of-3vec-bitnot
    (implies (3vec-p x)
             (3vec-p ~x))
    :hints(("Goal" :in-theory (enable 3vec-p 3vec-fix))
           (acl2::equal-by-logbitp-hammer)))

  (defthm 3vec-bitnot-bits
    (implies (3vec-p x)
             (equal (4vec-idx->4v n (3vec-bitnot x))
                    (acl2::4v-not (4vec-idx->4v n x))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 3vec-bitnot
    :hints(("Goal" :in-theory (enable 3vec-fix)))))


(define 4vec-bitnot ((x 4vec-p))
  :short "Bitwise logical NOT of a @(see 4vec)."
  :returns (~x 3vec-p!)
  (3vec-bitnot (3vec-fix x))
  ///

  "<p>Main correctness theorem: each result bit is just the @(see acl2::4v-not)
   of the corresponding input bit.</p>"

  (defthm 4vec-bitnot-bits
    (equal (4vec-idx->4v n (4vec-bitnot x))
           (acl2::4v-not (4vec-idx->4v n x))))

  (deffixequiv 4vec-bitnot :args ((x 3vec))))


(define 3vec-bitand ((x 4vec-p) (y 4vec-p))
  :parents (3vec-operations)
  :short "Bitwise logical AND of @(see 3vec)s."
  :returns (x&y 4vec-p)
  (if-2vec-p (x y)
             (2vec (logand (2vec->val x) (2vec->val y)))
             (b* (((4vec x))
                  ((4vec y)))
               (4vec (logand x.upper y.upper)
                     (logand x.lower y.lower))))
  ///
  (defret 3vec-p-of-3vec-bitand
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p x&y))
    :hints(("Goal" :in-theory (enable 3vec-p))
           (acl2::logbitp-reasoning)))

  (defthm 3vec-bitand-bits
    (implies (and (3vec-p! x)
                  (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitand x y))
                    (acl2::4v-and (4vec-idx->4v n (3vec-fix x))
                                  (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 3vec-bitand))


(define 4vec-bitand ((x 4vec-p) (y 4vec-p))
  :short "Bitwise logical AND of @(see 4vec)s."
  :returns (x&y 3vec-p!)
  (3vec-bitand (3vec-fix x) (3vec-fix y))
  ///

  "<p>Main correctness theorem: each result bit is just the @(see acl2::4v-and)
  of the corresponding input bits.</p>"

  (defthm 4vec-bitand-bits
    (equal (4vec-idx->4v n (4vec-bitand x y))
           (acl2::4v-and (4vec-idx->4v n x)
                         (4vec-idx->4v n y))))

  (deffixequiv 4vec-bitand :args ((x 3vec) (y 3vec))))


(define 3vec-bitor ((x 4vec-p) (y 4vec-p))
  :parents (3vec-operations)
  :short "Bitwise logical OR of @(see 3vec)s."
  :returns (x-or-y 4vec-p)
  (if-2vec-p (x y)
             (2vec (logior (2vec->val x) (2vec->val y)))
             (b* (((4vec x))
                  ((4vec y)))
               (4vec (logior x.upper y.upper)
                     (logior x.lower y.lower))))
  ///
  (defret 3vec-p-of-3vec-bitor
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p x-or-y))
    :hints(("Goal" :in-theory (enable 3vec-p))
           (acl2::logbitp-reasoning)))

  (defthm 3vec-bitor-bits
    (implies (and (3vec-p! x)
                  (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitor x y))
                    (acl2::4v-or (4vec-idx->4v n (3vec-fix x))
                                 (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 3vec-bitor))


(define 4vec-bitor ((x 4vec-p) (y 4vec-p))
  :short "Bitwise logical OR of @(see 4vec)s."
  :returns (x-or-y 3vec-p!)
  (3vec-bitor (3vec-fix x) (3vec-fix y))
  ///

  "<p>Main correctness theorem: each result bit is just the @(see acl2::4v-or)
  of the corresponding input bits.</p>"

  (defthm 4vec-bitor-bits
    (equal (4vec-idx->4v n (4vec-bitor x y))
           (acl2::4v-or (4vec-idx->4v n x)
                        (4vec-idx->4v n y))))

  (deffixequiv 4vec-bitor :args ((x 3vec) (y 3vec))))


(define 3vec-bitxor ((x 4vec-p) (y 4vec-p))
  :parents (3vec-operations)
  :short "Bitwise logical XOR of @(see 3vec)s."
  :returns (x^y 4vec-p)
  (if-2vec-p (x y)
             (2vec (logxor (2vec->val x) (2vec->val y)))
             (b* (((4vec x))
                  ((4vec y))
                  (xmask (logior (logand x.upper (lognot x.lower))
                                 (logand y.upper (lognot y.lower)))))
               (4vec (logior xmask (logxor x.upper y.upper))
                     (logand (lognot xmask) (logxor x.lower y.lower)))))
  ///
  (defret 3vec-p-of-3vec-bitxor
    (implies (and (3vec-p x)
                  (3vec-p y))
             (3vec-p x^y))
    :hints(("Goal" :in-theory (enable 3vec-p))
           (acl2::logbitp-reasoning)))

  (defthm 3vec-bitxor-bits
    (implies (and (3vec-p! x)
                  (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitxor x y))
                    (acl2::4v-xor (4vec-idx->4v n (3vec-fix x))
                                  (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 3vec-bitxor))


(define 4vec-bitxor ((x 4vec-p) (y 4vec-p))
  :short "Bitwise logical XOR of @(see 4vec)s."
  :guard-hints ((acl2::equal-by-logbitp-hammer))
  :returns (x^y 3vec-p! :hints (("goal" :in-theory (enable 3vec-p))
                                (acl2::equal-by-logbitp-hammer)))
  (if-2vec-p (x y)
             (2vec (logxor (2vec->val x) (2vec->val y)))
             (b* (((4vec x))
                  ((4vec y))
                  (xmask (logior (logxor x.upper x.lower)
                                 (logxor y.upper y.lower))))
               (4vec (logior xmask (logxor x.upper y.upper))
                     (logand (lognot xmask) (logxor x.lower y.lower)))))
  ///
  (defthmd 4vec-bitxor-redef
    (equal (4vec-bitxor x y)
           (3vec-bitxor (3vec-fix x) (3vec-fix y)))
    :hints(("Goal" :in-theory (enable 3vec-bitxor 3vec-fix))
           (acl2::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:in-theory (enable bool->bit)))))

  (local (in-theory (enable 4vec-bitxor-redef)))

  "<p>Main correctness theorem: each result bit is just the @(see acl2::4v-xor)
  of the corresponding input bits.</p>"

  (defthm 4vec-bitxor-bits
    (equal (4vec-idx->4v n (4vec-bitxor x y))
           (acl2::4v-xor (4vec-idx->4v n x)
                         (4vec-idx->4v n y))))

  (deffixequiv 4vec-bitxor :args ((x 3vec) (y 3vec))
    :hints (("goal" :in-theory (enable 3vec-fix))
            (acl2::equal-by-logbitp-hammer))))


(define 4vec-res ((a 4vec-p) (b 4vec-p))
  :short "Bitwise wire resolution of two @(see 4vec)s."

  :long "<p>Resolves together two 4vecs as if they were both shorted together.
Each bit of the result is determined by the corresponding bits of the two
inputs as follows:</p>

<ul>
 <li>If both input bits have the same value, then the resulting bit is that value.</li>
 <li>If one input bit is Z, the result is the other input bit.</li>
 <li>Otherwise, the result is X.</li>
</ul>"
  :returns (ans 4vec-p)
  (b* (((4vec a))
       ((4vec b)))
    ;; truth table:
    ;;   u 0011
    ;;   l 0101
    ;;     0zx1
    ;; ul
    ;; 000 00xx
    ;; 01z 0zx1
    ;; 10x xxxx
    ;; 111 x1x1

    ;; (a.upper == 1) iff a is 1 or x.  (result is 1 or x) iff (one or both of the inputs is 1 or x).
    ;; (a.lower == 0) iff a is 0 or x.  (result is 0 or x) iff (one or both of the inputs is 0 or x).
    (4vec (logior a.upper b.upper)
          (logand a.lower b.lower)))
  ///

  "<p>Main correctness theorem: each result bit is just the @(see acl2::4v-res)
  of the corresponding input bits.</p>"

  (defthm 4vec-res-bits
    (equal (4vec-idx->4v n (4vec-res x y))
           (acl2::4v-res (4vec-idx->4v n x)
                         (4vec-idx->4v n y)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 4vec-res))


(define 4vec-resand ((a 4vec-p) (b 4vec-p))
  :short "Bitwise wired AND resolution of two @(see 4vec)s."

  :long "<p>Resolves together two 4vecs as if they were both assigned to a
@('wand') net in Verilog.  Each bit of the result is determined by the
corresponding bits of the two inputs as follows:</p>

<ul>
 <li>If either input is 0, the result is 0.</li>
 <li>If either input is Z, the result is the other input bit.</li>
 <li>If both inputs are 1, the result is 1.</li>
 <li>If one input is X and the other is not 0, the result is X.</li>
</ul>"
  :returns (ans 4vec-p)
  (b* (((4vec a))
       ((4vec b)))
    ;; truth table:
    ;;   u 0011
    ;;   l 0101
    ;;     0zx1
    ;; ul
    ;; 000 0000
    ;; 01z 0zx1
    ;; 10x 0xxx
    ;; 111 01x1

    (4vec (logand (logior a.upper a.lower)  ;; a not 0
                  (logior b.upper b.lower)  ;; b not 0
                  (logior a.upper b.upper)) ;; not both z
          (logand a.lower b.lower)))
  ///

  "<p>Main correctness theorem: each result bit just the @(see acl2::4v-wand)
  of the corresponding input bits.</p>"

  (defthm 4vec-resand-bits
    (equal (4vec-idx->4v n (4vec-resand x y))
           (acl2::4v-wand (4vec-idx->4v n x)
                          (4vec-idx->4v n y)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 4vec-resand))


(define 4vec-resor ((a 4vec-p) (b 4vec-p))
  :short "Bitwise wired OR resolution of two @(see 4vec)s."

  :long "<p>Resolves together two 4vecs as if they were both assigned to a
@('wor') net in Verilog.  Each bit of the result is determined by the
corresponding bits of the two inputs as follows:</p>

<ul>
<li>If either input is 1, the result is 1.</li>
<li>If either input is Z, the result is the other input bit.</li>
<li>If both inputs are 0, the result is 0.</li>
<li>If one input is X and the other is not 1, the result is X.</li>
</ul>"
  :returns (ans 4vec-p)
  (b* (((4vec a))
       ((4vec b)))
    ;; truth table:
    ;;   u 0011
    ;;   l 0101
    ;;     0zx1
    ;; ul
    ;; 000 00x1
    ;; 01z 0zx1
    ;; 10x xxx1
    ;; 111 1111

    (4vec (logior a.upper b.upper)
          (logior (logand a.upper a.lower)
                  (logand b.upper b.lower)
                  (logand a.lower b.lower))))
  ///

  "<p>Main correctness theorem: each result bit just the @(see acl2::4v-wor)
  of the corresponding input bits.</p>"

  (defthm 4vec-resor-bits
    (equal (4vec-idx->4v n (4vec-resor x y))
           (acl2::4v-wor (4vec-idx->4v n x)
                         (4vec-idx->4v n y)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (deffixequiv 4vec-resor))


; Special hack for bit explosions.
;
; Operations like `(4vec-zero-ext ,(expt 2 30) -1) could result in the creation
; of huge bignums.  Normally we should try to detect this kind of problem and
; cause a clean (break) so that the problem can be debugged.  However, in some
; cases, such as Verilog linting, it is better to fudge the result and
; continue.

(defmacro 4vec-bit-limit () (expt 2 24))

(defconst *4vec-unsoundly-suppress-large-integers* nil)

(defmacro 4vec-very-large-integer-warning (n)
  ;; Logically always returns NIL.
  `(if *4vec-unsoundly-suppress-large-integers*
       t
     (prog2$ (cw "!!!!!!!! Danger -- if you continue, ~x0 will create a ~x1-bit ~
                  value -- examine the backtrace to diagnose.~%"
                 std::__function__ ,n)
             (break$))))

(local (in-theory (disable (break$))))

(define 4vec-zero-ext ((n 4vec-p "Position to truncate/zero-extend at.")
                       (x 4vec-p "The @(see 4vec) to truncate/zero-extend."))
  :returns (x-ext 4vec-p)
  :short "Like @(see loghead) for @(see 4vec)s; the width is also a @(see
4vec)."

  :long "<p>When @('n') is a natural number, we keep the least significant
@('n') bits of @('x') and clear any bits above this to zero.</p>

<p>When @('n') has any X or Z bits or is negative, the result is all X
bits.</p>"

  (if (and (2vec-p n)
           (<= 0 (2vec->val n)))
      (if (mbe :logic nil
               :exec
               (and (>= (2vec->val n) (4vec-bit-limit))
                    (b* (((4vec x)))
                      ;; can only create a very large integer from a
                      ;; not-very-large integer by zero extension if x is
                      ;; negative or x/z-extended
                      (or (< x.upper 0)
                          (< x.lower 0)))
                    (4vec-very-large-integer-warning (2vec->val n))))
          ;; Logically unreachable case -- but we can do this if
          ;; *4vec-unsoundly-suppress-large-integers* is redefined
          (4vec-x)
        (if-2vec-p (x)
                   (2vec (loghead (2vec->val n) (2vec->val x)))
                   (b* (((4vec x))
                        (nval (2vec->val n)))
                     (4vec (loghead nval x.upper)
                           (loghead nval x.lower)))))
    (4vec-x))
  ///
  (deffixequiv 4vec-zero-ext))


(define 4vec-sign-ext ((n 4vec-p)
                       (x 4vec-p))
  :returns (x-ext 4vec-p)
  :short "Like @(see logext) for @(see 4vec)s; the width is also a @(see
4vec)."

  :long "<p>When @('n') is a positive natural, we keep the least significant
@('n') bits of @('x') and then sign-extend them to infinity, i.e., bit @('n-1')
gets replicated out to infinity.</p>

<p>When @('n') has any X or Z bits, or is not positive, the result is all X
bits.</p>"

  (if (and (2vec-p n)
           (< 0 (2vec->val n)))
      (if-2vec-p (x)
                 (2vec (fast-logext (2vec->val n) (2vec->val x)))
                 (b* (((4vec x))
                      (nval (2vec->val n)))
                   (4vec (fast-logext nval x.upper)
                         (fast-logext nval x.lower))))
    (4vec-x))
  ///
  (deffixequiv 4vec-sign-ext))



(define 4v->4vec-bit ((x acl2::4vp))
  :returns (vec 4vec-p)
  :short "Convert a @(see acl2::4v)-style @(see acl2::4vp) into an infinite
width @(see 4vec) of that bit."
  (case x
    ((t)       (2vec -1))
    ((f)       (2vec 0))
    (z         (4vec-z))
    (otherwise (4vec-x)))
  ///
  ;; (defthm 4vec-idx->4v-of-4v->4vec-bit
  ;;   (equal (4vec-idx->4v 0 (4v->4vec-bit x))
  ;;          (acl2::4v-fix x)))
  ;; (defthm 4v->4vec-bit-of-4vec-idx->4v
  ;;   (equal (4v->4vec-bit (4vec-idx->4v n x))
  ;;          (4vec-bit-index n x))
  ;;   :hints(("Goal" :in-theory (enable 4vec-bit-index
  ;;                                     4vec-idx->4v))))
  )




(define 3vec-reduction-and ((x 4vec-p))
  :parents (3vec-operations)
  :returns (and-x 4vec-p)
  :short "Reduction logical AND of a @(see 3vec)."
  :long "<p>See @(see 4vec-reduction-and) for some additional discussion.  We
assume there are no Z bits and in that case, following the @(see
boolean-convention), we return:</p>

<ul>
<li>True (all 1s) if all of the (infinite) bits are 1, i.e., if X is -1,</li>
<li>False (all 0s) if there is any bit that is 0, or</li>
<li>All Xes otherwise.</li>
</ul>"

  (if-2vec-p (x)
             (2vec (bool->vec (int= (2vec->val x) -1)))
             (b* (((4vec x)))
               (4vec (bool->vec (int= x.upper -1))
                     (bool->vec (int= x.lower -1)))))
  ///
  (defret 3vec-p-of-3vec-reduction-and
    (implies (3vec-p x)
             (3vec-p and-x))
    :hints(("Goal" :in-theory (enable 3vec-p bool->vec))))

  (local (defthm lower-of-3vec-not-neg-1
           (implies (and (3vec-p x)
                         (not (equal (4vec->upper x) -1)))
                    (not (equal (4vec->lower x) -1)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm lower-of-3vec-not-neg-1-logcdr
           (implies (and (3vec-p x)
                         (not (equal (logcdr (4vec->upper x)) -1)))
                    (not (equal (logcdr (4vec->lower x)) -1)))
           :hints(("Goal" :in-theory (enable 3vec-p
                                             acl2::logand**
                                             acl2::lognot**)))))

  (local (defthm 3vec-implies-logbitp
           (implies (and (3vec-p x)
                         (not (logbitp n (4vec->upper x))))
                    (not (logbitp n (4vec->lower x))))
           :hints(("Goal" :in-theory (enable 3vec-p))
                  (acl2::logbitp-reasoning))))

  (defthmd 3vec-reduction-and-recursive
    (implies (3vec-p! x)
             (equal (3vec-reduction-and x)
                    (b* (((4vec x)))
                      (if (and (or (zip x.upper) (eql x.upper -1))
                               (or (zip x.lower) (eql x.lower -1)))
                          (4vec-fix x)
                        (4v->4vec-bit
                         (acl2::4v-and (4vec-idx->4v 0 x)
                                       (4vec-idx->4v 0 (3vec-reduction-and
                                                        (4vec (logcdr x.upper)
                                                              (logcdr x.lower))))))))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v 3vec-fix
                                      acl2::b-and acl2::b-ior
                                      bool->vec)
            :expand ((logand (4vec->lower x) (4vec->upper x))
                     (logior (4vec->lower x) (4vec->upper x)))))
    :rule-classes ((:definition :install-body nil
                    :clique (3vec-reduction-and)
                    :controller-alist ((3vec-reduction-and t)))))

  (deffixequiv 3vec-reduction-and))


(define 4vec-reduction-and ((x 4vec-p))
  :short "Reduction logical AND of a @(see 4vec)."
  :long "<p>ANDs together all of the bits in a 4vec.  Following the @(see
boolean-convention), we return:</p>

<ul>
<li>True (all 1s) if all of the (infinite) bits are 1, i.e., if X is -1,</li>
<li>False (all 0s) if there is any bit that is 0, or</li>
<li>All Xes otherwise.</li>
</ul>

<p><b>Subtle</b>.  Since @(see 4vec)s are ``infinite width,'' reduction
operations are a bit unusual.  For reduction AND in particular, when
translating from Verilog or other languages where your vectors are only some
fixed width, you will typically need to <i>always sign-extend the input
vector</i>, regardless of whether it is signed or unsigned.</p>

<p>That is, say you start with a unsigned 5-bit vector whose value is
@('11111').  If you create your (infinite width) 4vec for this by zero
extension, you'll end up with infinitely many leading 0s, which will cause the
reduction AND of your vector to be 0!</p>"
  :returns (and-x 3vec-p!)
  (3vec-reduction-and (3vec-fix x))
  ///
  (defthmd 4vec-reduction-and-recursive
    (equal (4vec-reduction-and x)
           (b* (((4vec x))
                ((when (and (or (zip x.upper) (eql x.upper -1))
                            (or (zip x.lower) (eql x.lower -1))))
                 (3vec-fix x))
                (first    (4vec-idx->4v 0 x))
                (and-rest (4vec-idx->4v 0 (4vec-reduction-and (4vec (logcdr x.upper)
                                                                    (logcdr x.lower))))))
             (4v->4vec-bit (acl2::4v-and first and-rest))))
    :hints(("Goal":in-theory (e/d (4vec-idx->4v 4vec-bit-index
                                                bool->vec
                                                3vec-fix 3vec-reduction-and
                                                acl2::b-and acl2::b-ior)
                                  (bitops::logand-with-negated-bitmask))
            :expand ((logand (4vec->lower x) (4vec->upper x))
                     (logior (4vec->lower x) (4vec->upper x))
                     (:free (x) (logbitp 0 x)))))
    :rule-classes ((:definition :install-body nil
                    :clique (4vec-reduction-and)
                    :controller-alist ((4vec-reduction-and t)))))

  (deffixequiv 4vec-reduction-and :args ((x 3vec))))


(define 3vec-reduction-or ((x 4vec-p))
  :parents (3vec-operations)
  :short "Reduction logical OR of a @(see 3vec)."
  :long "<p>See @(see 4vec-reduction-or) for some additional discussion.  We
assume that there are no Z bits.  In that case, following the @(see
boolean-convention), we return:</p>

<ul>
<li>False (all 0s) if all of the (infinite) bits are 0, i.e., if X is 0,</li>
<li>True (all 1s) if there is any bit that is 1, or</li>
<li>All Xes otherwise.</li>
</ul>"

  :returns (or-x 4vec-p)
  (if-2vec-p (x)
             (2vec (bool->vec (not (int= (2vec->val x) 0))))
             (b* (((4vec x)))
               (4vec (bool->vec (not (int= x.upper 0)))
                     (bool->vec (not (int= x.lower 0))))))
  ///
  (defret 3vec-p-of-3vec-reduction-or
    (implies (3vec-p x)
             (3vec-p or-x))
    :hints(("Goal" :in-theory (enable 3vec-p bool->vec))))

  (local (defthm upper-of-3vec-not-zero
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm upper-of-3vec-not-0-logcdr
           (implies (and (3vec-p x)
                         (not (equal (logcdr (4vec->lower x)) 0)))
                    (not (equal (logcdr (4vec->upper x)) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p
                                             acl2::logand**
                                             acl2::lognot**)))))

  (local (defthm 3vec-implies-logbitp
           (implies (and (3vec-p x)
                         (logbitp n (4vec->lower x)))
                    (logbitp n (4vec->upper x)))
           :hints(("Goal" :in-theory (enable 3vec-p))
                  (acl2::logbitp-reasoning))))

  (defthmd 3vec-reduction-or-recursive
    (implies (3vec-p! x)
             (equal (3vec-reduction-or x)
                    (b* (((4vec x)))
                      (if (and (or (zip x.upper) (eql x.upper -1))
                               (or (zip x.lower) (eql x.lower -1)))
                          (3vec-fix x)
                        (4v->4vec-bit
                         (acl2::4v-or (4vec-idx->4v 0 x)
                                      (4vec-idx->4v 0 (3vec-reduction-or
                                                       (4vec (logcdr x.upper)
                                                             (logcdr x.lower))))))))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v 3vec-fix
                                      bool->vec
                                      acl2::b-and acl2::b-ior)
            :expand ((logand (4vec->lower x) (4vec->upper x))
                     (logior (4vec->lower x) (4vec->upper x)))))
    :rule-classes ((:definition :install-body nil
                    :clique (3vec-reduction-or)
                    :controller-alist ((3vec-reduction-or t)))))

  (deffixequiv 3vec-reduction-or))


(define 4vec-reduction-or ((x 4vec-p))
  :short "Reduction logical OR of a @(see 4vec)."

  :long "<p>ORs together all of the bits in a 4vec.  Following the @(see
boolean-convention), we return:</p>

<ul>
<li>False (all 0s) if all of the (infinite) bits are 0, i.e., if X is 0,</li>
<li>True (all 1s) if there is any bit that is 1, or</li>
<li>All Xes otherwise.</li>
</ul>

<p>When translating Verilog, the input vector may be either sign- or 0-extended
without affecting the result.</p>"
    :returns (or-x 3vec-p!)
    (3vec-reduction-or (3vec-fix x))
    ///
    (defthmd 4vec-reduction-or-recursive
      (equal (4vec-reduction-or x)
             (b* (((4vec x))
                  ((when (and (or (zip x.upper) (eql x.upper -1))
                              (or (zip x.lower) (eql x.lower -1))))
                   (3vec-fix x))
                  (first   (4vec-idx->4v 0 x))
                  (or-rest (4vec-idx->4v 0 (4vec-reduction-or (4vec (logcdr x.upper)
                                                                    (logcdr x.lower))))))
               (4v->4vec-bit
                (acl2::4v-or first or-rest))))
      :hints(("Goal":in-theory (e/d (4vec-idx->4v 4vec-bit-index
                                                  bool->vec
                                                  3vec-fix 3vec-reduction-or
                                                  acl2::b-and acl2::b-ior)
                                    (bitops::logand-with-negated-bitmask))
              :expand ((logand (4vec->lower x) (4vec->upper x))
                       (logior (4vec->lower x) (4vec->upper x))
                       (:free (x) (logbitp 0 x)))))
      :rule-classes ((:definition :install-body nil
                      :clique (4vec-reduction-or)
                      :controller-alist ((4vec-reduction-or t)))))

    (deffixequiv 4vec-reduction-or :args ((x 3vec))))


(define 4vec-concat ((width 4vec-p "Width of less-significant 4vec.")
                     (low   4vec-p "Source of the W less-significant bits.")
                     (high  4vec-p "Source of the rest of the bits."))
  :returns (concat 4vec-p)
  :short "Like @(see logapp) for @(see 4vec)s; the width is also a @(see 4vec)."

  :long "<p>In the usual case, @('width') is some natural number: we
concatenate the @('width') least significant bits of @('low') with all of
@('high').  That is, we produce a new @(see 4vec) which might be written in
Verilog as @('{high, low[width-1:0]}').</p>

<p>Since @('width') is a @(see 4vec) it may have X or Z bits or may be
negative.  In this case, the result is infinite Xes.</p>"

  (if (and (2vec-p width)
           (<= 0 (2vec->val width)))
      (if (mbe :logic nil
               :exec
               (and (>= (2vec->val width) (4vec-bit-limit))
                    (b* (((4vec low))
                         ((4vec high)))
                      ;; can only create a very large integer from a
                      ;; not-very-large integer by zero extension if x is
                      ;; negative or x/z-extended
                      (or (if (< low.upper 0)
                              (not (eql high.upper -1))
                            (not (eql high.upper 0)))
                          (if (< low.lower 0)
                              (not (eql high.lower -1))
                            (not (eql high.lower 0)))))
                    (4vec-very-large-integer-warning (2vec->val width))))
          ;; Logically unreachable case -- but we can do this if
          ;; *4vec-unsoundly-suppress-large-integers* is redefined
          (4vec-x)
        ;; Normal case
        (b* ((wval (2vec->val width)))
          (if-2vec-p (low high)
                     (2vec (logapp wval (2vec->val low) (2vec->val high)))
                     (b* (((4vec low))
                          ((4vec high)))
                       (4vec (logapp wval low.upper high.upper)
                             (logapp wval low.lower high.lower))))))
    (4vec-x))
  ///
  (deffixequiv 4vec-concat
    :args ((width 2vecnatx :hints(("Goal" :in-theory (enable 2vecnatx-fix))))
           (low   4vec)
           (high  4vec))))


(define 4vec-shift-core ((amt integerp "Shift amount.")
                         (src 4vec-p "Source operand."))
  :returns (shift 4vec-p)
  (b* ((amt (lifix amt)))
    (if (mbe :logic nil
             :exec (and (>= amt (4vec-bit-limit))
                        (b* (((4vec src)))
                          (not (and (eql src.upper 0)
                                    (eql src.lower 0))))
                        (4vec-very-large-integer-warning amt)))
        ;; Logically unreachable case -- but we can do this if
        ;; *4vec-unsoundly-suppress-large-integers* is redefined
        (4vec-x)
      ;; Normal case
      (if-2vec-p (src)
                 (2vec (ash (2vec->val src) amt))
                 (b* (((4vec src)))
                   (4vec (ash src.upper amt)
                         (ash src.lower amt))))))
  ///
  (deffixequiv 4vec-shift-core))

(define 4vec-rsh ((amt 4vec-p "Shift amount.")
                  (src 4vec-p "Source operand."))
  :returns (shifted 4vec-p)
  :short "Right ``arithmetic'' shift of @(see 4vec)s."

  :long "<p>In the usual case, @('amt') is a @(see 2vec), i.e., its bits are
all good Boolean values.  In this case:</p>

<ul>

<li>If @('amt') is non-negative then we ``arithmetically'' shift @('src') to
the right by @('amt')-many places.  This doesn't affect the infinitely-repeated
most significant bit of @('src').  That is, if @('src') is negative to begin
with, i.e., its upper bits are all 1s, then the resulting, shifted value will
also be a negative number whose upper bits are all 1s.  If @('src') has upper
bits Z, then the shifted result will also have upper bits that are all Zs,
etc.</li>

<li>If @('amt') is negative, then we shift @('src') to the <b>left</b> instead
of to the right, shifting in 0s from below.  Note that this behavior
<b>differs</b> from the (very strange) semantics of Verilog/SystemVerilog,
where shift amounts are always treated as unsigned.</li>

</ul>

<p>In cases where @('amt') has any X or Z bits, the result is just all
Xes.</p>"

  (if (2vec-p amt)
      (4vec-shift-core (- (2vec->val amt)) src)
    (4vec-x))
  ///
  (deffixequiv 4vec-rsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (src 4vec))))


(define 4vec-lsh ((amt 4vec-p "Shift amount.")
                  (src 4vec-p "Source operand."))
  :returns (shifted 4vec-p)
  :short "Left ``arithmetic'' shift of @(see 4vec)s."

  :long "<p>In the usual case, @('amt') is a @(see 2vec), i.e., its bits are
all good Boolean values.  In this case:</p>

<ul>

<li>If @('amt') is non-negative, then we shift @('src') to the left by
@('amt')-many places.  The least significant bits become 0s.</li>

<li>If @('amt') is negative, then we shift @('src') to the <b>right</b> instead
of to the left.  This is an ``arithmetic'' shift, as described in @(see
4vec-rsh).  Note that this behavior <b>differs</b> from the (very strange)
semantics of Verilog/SystemVerilog, where shift amounts are always treated as
unsigned.</li>

</ul>

<p>In cases where @('amt') has any X or Z bits, the result is just all
Xes.</p>"

  (if (2vec-p amt)
      (4vec-shift-core (2vec->val amt) src)
    (4vec-x))
  ///
  (deffixequiv 4vec-lsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (src 4vec))))


(define 4vec-parity ((x 4vec-p))
  :returns (parity 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  :short "Reduction logical XOR (i.e., parity) of a @(see 4vec)."

  :long "<p>We compute the parity of @('x') if possible, following the @(see
boolean-convention).  If @('x') has any X or Z bits, or is a negative number,
we just return all Xes.  Otherwise, @('x') is a natural number and we just
return the parity of its 1 bits.  For instance,</p>

@({
     (4vec-parity #b0) == 0   (all 0s, false)
     (4vec-parity #b1) == -1  (all 1s, true)
     (4vec-parity #b11) == 0  (all 0s, false)
     (4vec-parity #b10) == -1 (all 1s, true)
})

<p><b>Subtle.</b> Since @(see 4vec)s are ``infinite width,'' reduction
operators are a bit unusual.  For parity computations this is especially true
for negative number: if @('x') is negative, i.e., it has infinitely many
leading 1 bits, it doesn't make much sense to ask about its parity.
Accordingly, if you are translating from Verilog or other languages that have
fixed width vectors, you will typically want to take the parity of, e.g., the
@(see 4vec-zero-ext) of your vector.</p>"
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (b* ((x (2vec->val x)))
        (2vec (- (fast-parity (+ 1 (integer-length x)) x))))
    ;; Negative ("infinite ones") or X/Z bits
    (4vec-x))
  ///
  (deffixequiv 4vec-parity
    :args ((x 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix)))))))

(define 4vec-countones ((x 4vec-p))
  :returns (count 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  :short "Count of 1 bits in a @(see 4vec) (X-monotonic)."
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (b* ((x (2vec->val x)))
        (2vec (logcount x)))
    ;; Negative ("infinite ones") or X/Z bits
    (4vec-x))
  ///
  (deffixequiv 4vec-countones
    :args ((x 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix)))))))


(define 4vec-onehot ((x 4vec-p))
  :returns (count 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  :short "Count of 1 bits in a @(see 4vec) (X-monotonic)."
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (b* ((x (2vec->val x)))
        (2vec (bool->bit (eql (logcount x) 1))))
    ;; X/Z bits
    (4vec-x))
  ///
  (deffixequiv 4vec-onehot
    :args ((x 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix)))))))

(define 4vec-onehot0 ((x 4vec-p))
  :returns (count 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  :short "Count of 1 bits in a @(see 4vec) (X-monotonic)."
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (b* ((x (2vec->val x)))
        (2vec (bool->bit (<= (logcount x) 1))))
    ;; X/Z bits
    (4vec-x))
  ///
  (deffixequiv 4vec-onehot
    :args ((x 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix)))))))


(define 4vec-plus ((x 4vec-p) (y 4vec-p))
  :short "Integer addition of two @(see 4vec)s."

  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: if either input has any X or Z bits anywhere, the entire
result is all Xes.  We return all Xes even in cases where you might think that
some bits are ``obviously'' going to be driven in a certain way.  For instance,
when we add @('4'b XX00') to @('4'b ZZ01'), we return all Xes even though a
less conservative semantics might produce @('4'b XX01').</p>

<p>When there are no X or Z bits anywhere, we just compute the (signed) sum of
the two (signed) inputs.</p>"

  :returns (sum 4vec-p)
  (if (and (2vec-p x) (2vec-p y))
      (2vec (+ (the integer (2vec->val x))
               (the integer (2vec->val y))))
    (4vec-x))
  ///
  (deffixequiv 4vec-plus
    :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-xdet ((x 4vec-p))
  :short "Identity function for @(see 2vec)s, or all Xes when there are any X
or Z bits."
  :long "<p>This (arguably) matches the Verilog specification for unary +.</p>

<p>BOZO this is identical to @(see 2vecx-fix).</p>"
  :returns (res 4vec-p)
  (if (2vec-p x)
      (4vec-fix x)
    (4vec-x))
  ///
  (deffixequiv 4vec-xdet :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-minus ((x 4vec-p) (y 4vec-p))
  :returns (diff 4vec-p)
  :short "Integer subtraction of two @(see 4vec)s."

  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: if either input has any X or Z bits, the result is all X
bits.  We return all Xes even in cases where you might think that some bits are
``obviously'' going to be driven in a certain way.  For instance, when we
subtract @('4'b XX11') - @('4'b ZZ00'), we return all Xes even though a less
conservative semantics might produce @('4'b XX11').</p>

<p>When there are no X or Z bits anywhere, we just compute the (signed)
difference of the two (signed) inputs.</p>"

  (if (and (2vec-p x)
           (2vec-p y))
      (2vec (binary-- (the integer (2vec->val x))
                      (the integer (2vec->val y))))
    (4vec-x))
  ///
  (deffixequiv 4vec-minus
    :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-uminus ((x 4vec-p))
  :returns (-x 4vec-p)
  :short "Integer negation of a @(see 4vec)."
  :long "<p>If the input has X or Z bits, the result is all X bits.  Otherwise,
we return the signed negation of the input.</p>"
  (if (2vec-p x)
      (2vec (- (the integer (2vec->val x))))
    (4vec-x))
  ///
  (deffixequiv 4vec-uminus :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-times ((x 4vec-p) (y 4vec-p))
  :returns (product 4vec-p)
  :short "Integer multiplication of @(see 4vec)s."
  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: if either input has any X or Z bits, the result is all X
bits.  Otherwise, we return the (signed) product of the two (signed)
inputs.</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (* (the integer (2vec->val x))
               (the integer (2vec->val y))))
    (4vec-x))
  ///
  (deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-quotient ((x 4vec-p) (y 4vec-p))
  :returns (quotient 4vec-p)
  :short "Integer division as in @(see truncate) for @(see 4vec)s."
  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: if either input has X or Z bits, or if you try to divide by
zero, then the result is all X bits.  Otherwise, we produce the integer
division of @($\\frac{x}{y}$), rounding toward zero as in @(see truncate).</p>"
  (if (and (2vec-p x)
           (2vec-p y)
           (not (eql (2vec->val y) 0)))
      (2vec (truncate (the integer (2vec->val x))
                      (the integer (2vec->val y))))
    (4vec-x))
  ///
  (deffixequiv 4vec-quotient :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-remainder ((x 4vec-p) (y 4vec-p))
  :returns (remainder 4vec-p)
  :short "Integer remainder as in @(see rem) for @(see 4vec)s."
  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: if either input has X or Z bits, or if you try to divide by
zero, then the result is all X bits.  Otherwise, we produce the integer
remainder of @($\\frac{x}{y}$), with rounding toward zero as in @(see
rem).</p>"
  (if (and (2vec-p x)
           (2vec-p y)
           (not (eql (2vec->val y) 0)))
      (2vec (rem (the integer (2vec->val x))
                 (the integer (2vec->val y))))
    (4vec-x))
  ///
  (deffixequiv 4vec-remainder :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))


(define 4vec-< ((x 4vec-p) (y 4vec-p))
  :returns (less 4vec-p)
  :short "Integer less-than for @(see 4vec)s."

  :long "<p>We return, following the @(see boolean-convention),</p>

<ul>
<li>All Xes when if either input has any X or Z bits, or else</li>
<li>True (all 1s) when @($x < y$), or else</li>
<li>False (all 0s) otherwise.</li>
</ul>

<p>This is a fairly conservative definition in the style of the Verilog
semantics: if either input has X or Z bits, the result is all X bits.  We
return all Xes even in cases where the comparison would ``obviously'' go a
certain way.  For instance, if you compare @('4'b 0100 < 4'b 011X'), we return
all Xes even though a less conservative semantics might say that the comparison
will be true.</p>"
  (if (and (2vec-p x)
           (2vec-p y))
      (2vec (bool->vec (< (the integer (2vec->val x))
                          (the integer (2vec->val y)))))
    (4vec-x))
  ///
  (deffixequiv 4vec-< :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))



(define 3vec-== ((x 4vec-p)
                 (y 4vec-p))
  :parents (3vec-operations)
  :returns (equal 4vec-p)
  :short "Bitwise equality of @(see 3vec)s."
  :long "<p>Assuming that the inputs have no Z bits, we return, following the
@(see boolean-convention):</p>

<ul>
<li>True (all 1s) when the inputs are purely Boolean and are equal, or</li>
<li>False (all 0s) if any bit is 0 in one input and is 1 in another, or</li>
<li>All Xes otherwise</li>
</ul>

<p>This properly treats X as an unknown, i.e., whether or not an X bit is equal
to anything else, including another X bit, is always unknown.</p>"

  (3vec-reduction-and
   (3vec-bitnot
    (3vec-bitxor x y)))
  ///
  (deffixequiv 3vec-==))


(define 4vec-== ((x 4vec-p) (y 4vec-p))
  :returns (equal 4vec-p)
  :short "Bitwise equality of @(see 4vec)s."
  :long "<p>We return, following the @(see boolean-convention),</p>

<ul>
<li>True (all 1s) when the inputs are purely Boolean and are equal, or</li>
<li>False (all 0s) if any bit is 0 in one input and is 1 in another, or</li>
<li>All Xes otherwise</li>
</ul>

<p>This properly treats X and Z values as unknowns, i.e., whether or not an X/Z
bit is equal to anything else, including another X/Z bit, is always
unknown.</p>"

  (3vec-== (3vec-fix x) (3vec-fix y))
  ///
  (deffixequiv 4vec-==
    :args ((x 3vec) (y 3vec))))


(define 4vec-=== ((x 4vec-p) (y 4vec-p))
  :returns (equal 4vec-p)
  :short "Unsafe, Verilog-style ``case equality'' of @(see 4vec)s."

  :long "<p>Warning: this is a bad operator that breaks the @(see 4vec-[=)
lattice monotonicity property.  It is similar to @(see 4vec-==) but, instead of
treating X or Z bits as unknown, allows them to be directly compared with one
another.</p>

<p>We return, following the @(see boolean-convention),</p>

<ul>
<li>True (all 1s) when the inputs are identical, or</li>
<li>False (all 0s) otherwise.</li>
</ul>"

  (2vec (bool->vec (4vec-equiv x y)))
  ///
  (deffixequiv 4vec-===))


(define 3vec-? ((test 4vec-p)
                (then 4vec-p)
                (else 4vec-p))
  :parents (3vec-operations)
  :returns (choice 4vec-p)
  :short "Atomic if-then-else of @(see 4vec)s, with a @(see 3vec) test; doesn't
unfloat then/else values."

  :long "<p>See @(see 4vec-?).  This is identical except that we assume
@('test') has no Z bits.</p>"

  (b* (((4vec test))
       ((when (eql test.upper 0)) ;; test is false
        (4vec-fix else))
       ((when (not (eql test.lower 0))) ;; test is true
        (4vec-fix then))
       ;; otherwise, test is X
       ((4vec then))
       ((4vec else)))
    ;; Truth table for case where test is X:
    ;; e\t   1  0  X  Z --> upper:     lower:
    ;; 1     1  X  X  X     1 1 1 1    1 0 0 0
    ;; 0     X  0  X  X     1 0 1 1    0 0 0 0
    ;; X     X  X  X  X     1 1 1 1    0 0 0 0
    ;; Z     X  X  X  X     1 1 1 1    0 0 0 0
    (4vec ;; upper is set if then and else are true, or if either is Z or X -- meaning,
     ;; if they're not both false.
     (logior then.upper else.upper then.lower else.lower)
     ;; lower is set if then and else are true, otherwise not --
     (logand then.upper else.upper then.lower else.lower)))

  ///
  (deffixequiv 3vec-?))

;; (defconst *zx10* (make-4vec :upper #b0110 :lower #b1010))
;; (3vec-? (4vec-x) *zx10* *zx10*)


(define 4vec-? ((test 4vec-p) (then 4vec-p) (else 4vec-p))
  :returns (choice 4vec-p)
  :short "Atomic if-then-else of @(see 4vec)s; doesn't unfloat then/else
values."

  :long "<p>Easy cases: when @('test') has any 1-bits we return @('then'); when
@('test') is 0 we return @('else').</p>

<p>Note that the behavior in these cases is <b>not very conservative</b>.  In
particular, the @('then') and @('else') branches are passed through without
``unfloating'' Z values.  This agrees with the Verilog and SystemVerilog
semantics for the @('?:') operators, but it does not agree with how some mux
implementations behave in hardware, e.g., and/or style muxes.</p>

<p>Hard case: when @('test') has some X or Z bits, we merge the bits of
@('then') and @('else'), setting each bit of the result to:</p>

<ul>
  <li>Xes in bit positions where @('then') and @('else') are unequal or both Z, or</li>
  <li>The agreed upon Boolean value, otherwise.</li>
</ul>"

  (3vec-? (3vec-fix test) then else)
  ///
  (deffixequiv 4vec-?
    :args ((test 3vec)
           (then 4vec)
           (else 4vec))))

(define 3vec-bit? ((tests 4vec-p)
                   (thens 4vec-p)
                   (elses 4vec-p))
  :parents (3vec-operations)
  :returns (choices 4vec-p)
  :short "Bitwise multiple if-then-elses of @(see 4vec)s, with a @(see 3vec)
test vector; doesn't unfloat then/else values."

  :prepwork ;; just a speed hint
  ((local (in-theory (disable BITOPS::LOGAND->=-0-LINEAR-2
                              BITOPS::LOGIOR-<-0-LINEAR-2
                              BITOPS::UPPER-BOUND-OF-LOGAND
                              LOGIOR-NEG-1-WHEN-LOGAND-NEG-1
                              ))))

  :long "<p>See @(see 4vec-bit?).  This is identical except that we assume
@('tests') has no Z bits.</p>"
  ;; ~test.upper --> false
  ;; test.lower --> true
  ;; otherwise x.
  ;;
  ;; ans upper:
  ;; (~tests.upper & elses.upper)       ;; test is false --> else
  ;;   | (tests.lower & thens.upper)    ;; test is true --> then
  ;;   | ( (tests.upper & ~tests.lower)   ;; test is X --> merge
  ;;        & (elses.upper | thens.upper | elses.lower | thens.lower)
  ;;        )
  ;;
  ;; ans lower:
  ;; (~tests.upper & elses.lower)       ;; test is false --> else
  ;;   | (tests.lower & thens.lower)    ;; test is true --> then
  ;;   | ( (tests.upper & ~tests.lower)   ;; test is X --> merge
  ;;        & elses.upper & thens.upper & elses.lower & thens.lower )
  (b* (((4vec tests))
       ((4vec thens))
       ((4vec elses))
       (test-x (logand tests.upper (lognot tests.lower))))
    (4vec (logior (logand (lognot tests.upper) elses.upper)
                  (logand tests.lower thens.upper)
                  (logand test-x
                          (logior (logior thens.upper thens.lower)
                                  (logior elses.upper elses.lower))))
          (logior (logand (lognot tests.upper) elses.lower)
                  (logand tests.lower thens.lower)
                  (logand test-x
                          (logand thens.upper thens.lower)
                          (logand elses.upper elses.lower)))))
  ///
  (defthm 3vec-?-in-terms-of-3vec-bit?
    (implies (3vec-p tests)
             (equal (3vec-bit? (4vec-sign-ext 1 (3vec-reduction-or tests)) thens elses)
                    (3vec-? tests thens elses)))
    :hints(("Goal" :in-theory (enable 3vec-?
                                      4vec-sign-ext
                                      3vec-p
                                      3vec-reduction-or))))
  (deffixequiv 3vec-bit?))

;;(defconst *zx10* (make-4vec :upper #b0110 :lower #b1010))
;;(3vec-bit? (4vec-x) *zx10* *zx10*)

(define 4vec-bit? ((tests 4vec-p)
                   (thens 4vec-p)
                   (elses 4vec-p))
  :returns (choices 4vec-p)
  :short "Bitwise multiple if-then-elses of @(see 4vec)s; doesn't unfloat
then/else values."

  :long "<p>We carry out an independent if-then-else for each bit of
@('tests'), @('thens'), and @('elses'), producing a new vector with all of the
answers.  This result is computed bit by bit, with @('result[i]') being set
to:</p>

<ul>
<li>@('thens[i]') if @('tests[i]') is 1,</li>
<li>@('elses[i]') if @('tests[i]') is 0, or</li>
<li>the merger of @('thens[i]') and @('elses[i]'), otherwise.</li>
</ul>

<p>This merging is just @('x') if the bits are different, or the agreed upon
value otherwise.</p>

<p>BOZO.  This operation is not very conservative.  In particular, Z values are
passed through without unfloating them, and can even be merged without
unfloating.  BOZO Consider how and whether Issue 384 (see @(see 4vec-?)) should
affect this operation and update the docs accordingly once it's fixed.</p>"

  (3vec-bit? (3vec-fix tests) thens elses)
  ///
  (local (defthm 3vec-fix-of-4vec-sign-ext
           (equal (3vec-fix (4vec-sign-ext n x))
                  (4vec-sign-ext n (3vec-fix x)))
           :hints(("Goal" :in-theory (enable 3vec-fix 4vec-sign-ext))
                  (acl2::logbitp-reasoning))))

  (defthm 4vec-?-in-terms-of-4vec-bit?
    (equal (4vec-bit? (4vec-sign-ext 1 (4vec-reduction-or tests)) thens elses)
           (4vec-? tests thens elses))
    :hints(("Goal" :in-theory (enable 4vec-?
                                      4vec-p 4vec-reduction-or))))
  (deffixequiv 4vec-bit?
    :args ((tests 3vec)
           (thens 4vec)
           (elses 4vec))))

(define 4vec-bit?! ((tests 4vec-p)
                    (thens 4vec-p)
                    (elses 4vec-p))
  :returns (choices 4vec-p)
  :short "Bitwise multiple if-then-elses of @(see 4vec)s; doesn't unfloat
then/else values; uses else branch bits for any test bits not equal to
1 (non-monotonic semantics in this respect)."

  :long "<p>We carry out an independent if-then-else for each bit of
@('tests'), @('thens'), and @('elses'), producing a new vector with all of the
answers.  This result is computed bit by bit, with @('result[i]') being set
to:</p>

<ul>
<li>@('thens[i]') if @('tests[i]') is 1,</li>
<li>@('elses[i]') if @('tests[i]') is not 1.</li>
</ul>

<p>This is used for conditionally overriding signals, as in:</p>
@({
 (bit?! override-test override-val regular-val)
 })

<p>This way, if the override-test is left out of the environment (therefore its
value is X), the regular value will go through.</p>"

  (b* (((4vec tests))
       ((4vec thens))
       ((4vec elses))
       (pick-then (logand tests.upper tests.lower)))
    (mbe :logic (b* ((pick-else (lognot pick-then))
                     (upper (logior (logand pick-then thens.upper)
                                    (logand pick-else elses.upper)))
                     (lower (logior (logand pick-then thens.lower)
                                    (logand pick-else elses.lower))))
                  (4vec upper lower))
         :exec (b* (((when (eql pick-then -1)) thens)
                    ((when (eql pick-then 0)) elses)
                    (pick-else (lognot pick-then))
                    (upper (logior (logand pick-then thens.upper)
                                   (logand pick-else elses.upper)))
                    (lower (logior (logand pick-then thens.lower)
                                   (logand pick-else elses.lower))))
                 (4vec upper lower))))
                 
  ///
  (deffixequiv 4vec-bit?!
    :args ((tests 4vec)
           (thens 4vec)
           (elses 4vec))))



(define 4vec-?! ((test 4vec-p)
                 (then 4vec-p)
                 (else 4vec-p))
  :returns (choices 4vec-p)
  :short "If-then-elses of @(see 4vec)s following the SystemVerilog semantics for
          procedural conditional branches, i.e. if the test has any bit that is
          exactly 1 (not 0, Z, or X), we choose the then branch, else the else
          branch. (Non-monotonic semantics)."

  (b* (((4vec test))
       ;; We choose the THEN branch if any bit has upper and lower both set.
       (pick-else (equal 0 (logand test.upper test.lower))))
    (if pick-else (4vec-fix else) (4vec-fix then)))
                 
  ///
  (deffixequiv 4vec-?!
    :args ((test 4vec)
           (then 4vec)
           (else 4vec))))




(define 3vec-?* ((test 4vec-p)
                (then 4vec-p)
                (else 4vec-p))
  :parents (3vec-operations)
  :returns (choice 4vec-p)
  :short "Atomic if-then-else of @(see 4vec)s, with a @(see 3vec) test.  Has
the property that when branches are equal, the result is equal to the branch,
regardless of the test."

  :long "<p>The difference between this and @(see 3vec-?) is that when the test is X and the branches are both Z, here we return Z whereas @(see 3vec-?) returns X.</p>"

  (b* (((4vec test))
       ((when (eql test.upper 0)) ;; test is false
        (4vec-fix else))
       ((when (not (eql test.lower 0))) ;; test is true
        (4vec-fix then))
       ;; otherwise, test is X
       ((4vec then))
       ((4vec else)))
    ;; Truth table for case where test is X:
    ;; e\t   1  0  X  Z --> upper:     lower:
    ;; 1     1  X  X  X     1 1 1 1    1 0 0 0
    ;; 0     X  0  X  X     1 0 1 1    0 0 0 0
    ;; X     X  X  X  X     1 1 1 1    0 0 0 0
    ;; Z     X  X  X  Z     1 1 1 0    0 0 0 1
    (4vec ;; upper is set unless both are 0 or both are Z - meaning, unless
          ;; both have upper == 0 and lower equal.
     (logior then.upper else.upper (logxor then.lower else.lower))
     ;; lower is set if both are 1 or both are Z -- meaning, both lowers are 1
     ;; and uppers are equal.
     (logand (logeqv then.upper else.upper) then.lower else.lower)))

  ///
  (deffixequiv 3vec-?*))

;; (defconst *zx10* (make-4vec :upper #b0110 :lower #b1010))
;; (3vec-?* (4vec-x) *zx10* *zx10*)


(define 4vec-?* ((test 4vec-p) (then 4vec-p) (else 4vec-p))
  :returns (choice 4vec-p)
  :short "Atomic if-then-else of @(see 4vec)s.   Has the property that when branches
          are equal, the result is equal to the branch, regardless of the
          test."

  (3vec-?* (3vec-fix test) then else)
  ///
  (deffixequiv 4vec-?*
    :args ((test 3vec)
           (then 4vec)
           (else 4vec))))




;; ---------- BOZO could generally use better documentation below here ---------



(define 4vec-override ((stronger 4vec-p)
                       (weaker   4vec-p))
  :returns (res 4vec-p)
  :short "Resolution for when one signal is stronger than the other."
  :long "<p>(4vec-override stronger weaker) takes the value of @('stronger')
for each of its non-Z bits, and the value of @('weaker') for bits where
stronger is Z.</p>"
  :guard-hints ((acl2::logbitp-reasoning))
  (b* (((4vec stronger))
       ((4vec weaker)))
    (mbe :logic
         (b* ((stronger-z (logand stronger.lower (lognot stronger.upper))))
           (4vec (logior (logand stronger-z weaker.upper)
                         (logand (lognot stronger-z) stronger.upper))
                 (logior (logand stronger-z weaker.lower)
                         (logand (lognot stronger-z) stronger.lower))))
         :exec (4vec (logior (logand stronger.lower weaker.upper) stronger.upper)
                     (logand (logior stronger.upper weaker.lower) stronger.lower))))
  ///
  (local (in-theory (e/d* ()
                          ((:rules-of-class :type-prescription :here)
                           (:rules-of-class :linear :here)
                           4vec->lower-when-2vec-p 2vec-p
                           bitops::logior-equal-0
                           acl2::zip-open
                           not)
                          ((:t logior) (:t logand) (:t lognot) (:t logbitp)))))
  (defthm 4vec-override-associative
    (equal (4vec-override (4vec-override x y) z)
           (4vec-override x (4vec-override y z)))
    :hints ((acl2::logbitp-reasoning)
            (and stable-under-simplificationp
                 '(:bdd (:vars nil)))))
  (deffixequiv 4vec-override))


(define 4vec-onset ((x 4vec-p))
  :returns (res 4vec-p)
  :short "Identity, except Z bits become 0."
  :long "<p>The closest monotonic approximation of the onset of each of the
bits of the input.  It differs from the actual onset in that the 4vec-onset of
an X bit is X.</p>"
  (b* (((4vec x)))
    (4vec x.upper (logand x.upper x.lower)))
  ///
  (defthm 4vec-onset-bits
    (equal (4vec-idx->4v n (4vec-onset x))
           (let ((in (4vec-idx->4v n x)))
             (if (eq 'z in)
                 'f
               in)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))
  (deffixequiv 4vec-onset))

(define 4vec-offset ((x 4vec-p))
  :returns (res 4vec-p)
  :short "Negation, except Z bits become 0."
  :long "<p>The closest monotonic approximation of the offset of each of the
bits of the input.  It differs from the actual offset in that the 4vec-offset
of an X bit is X.</p>"
  (b* (((4vec x)))
    (4vec (lognot x.lower) (lognot (logior x.upper x.lower))))
  ///
  (defthm 4vec-offset-bits
    (equal (4vec-idx->4v n (4vec-offset x))
           (let ((in (4vec-idx->4v n x)))
             (if (eq 'z in)
                 'f
               (acl2::4v-not in))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))
  (deffixequiv 4vec-offset))


(define rev-blocks ((nbits natp)
                    (blocksz posp)
                    (x integerp))
  :parents (4vec-rev-blocks)
  ;; :returns (res natp :rule-classes :type-prescription)
  :short "Reverses blocks, like the streaming concatenation operator in SystemVerilog."
  :long "<p>Example:</p>

@({
    (equal (rev-blocks 28 8 #xaabbccdd) #xddccbba)
})

<p>This essentially truncates x to nbits bits, then divides this into blocks of
size blocksz, starting from least significant bits, where the last
block (corresponding to the most significant bits of x) may be smaller.  Then
it reverses the order of these blocks.  So in the example above, the most
significant @('#xa') is dropped, and the rest is divided into the blocks @('a
bb cc dd'), which are then reversed.</p>"
  :measure (nfix nbits)
  :returns (res natp :rule-classes :type-prescription)
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       ((when (< nbits blocksz))
        (loghead nbits x))
       (next-nbits (- nbits blocksz))
       (rest (rev-blocks next-nbits blocksz (ash x (- blocksz)))))
    (logapp next-nbits rest (loghead blocksz x)))
  ///
  (deffixequiv rev-blocks))

(define rev-block-index ((i natp)
                         (nbits natp)
                         (blocksz posp))
  :parents (4vec-rev-blocks)
  :short "For reasoning about rev-blocks, computes the offset into x corresponding
to an offset into @('(rev-blocks nbits blocksz x)')."

  :long "
@({
 (equal (logbitp i (rev-blocks nbits blocksz x))
        (logbitp (rev-block-index i nbits blogksz) x))
})
<p>if i is in bounds.</p>"
  :measure (nfix nbits)
  :returns (idx natp :rule-classes :type-prescription)
  (b* ((nbits (lnfix nbits))
       (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
       (i (lnfix i))
       ((when (< nbits blocksz)) i)
       (next-nbits (- nbits blocksz))
       ((when (<= next-nbits i)) (- i next-nbits)))
    (+ blocksz (rev-block-index i next-nbits blocksz)))
  ///
  (local (defun ind (i nbits blocksz x)
           (declare (xargs :measure (nfix nbits)))
           (b* ((nbits (lnfix nbits))
                (blocksz (mbe :logic (acl2::pos-fix blocksz) :exec blocksz))
                (i (lnfix i)))
             (if (< nbits blocksz)
                 (list x i)
               (ind i (- nbits blocksz) blocksz (ash x (- blocksz)))))))

  (defthm logbitp-of-rev-blocks
    (equal (logbitp i (rev-blocks nbits blocksz x))
           (and (< (nfix i) (nfix nbits))
                (logbitp (rev-block-index i nbits blocksz) x)))
    :hints (("goal" :induct (ind i nbits blocksz x)
             :expand ((rev-block-index i nbits blocksz)
                      (rev-blocks nbits blocksz x))))))


(define 4vec-rev-blocks ((nbits   4vec-p)
                         (blocksz 4vec-p)
                         (x       4vec-p))
  :returns (res 4vec-p)
  :short "Similar to a streaming concatenation operation in SystemVerilog."
  :long "<p>BOZO document me.</p>"
  (if (and (2vec-p nbits)
           (<= 0 (2vec->val nbits))
           (2vec-p blocksz)
           (< 0 (2vec->val blocksz)))
      (b* (((4vec x)))
        (4vec (rev-blocks (2vec->val nbits)
                          (2vec->val blocksz)
                          x.upper)
              (rev-blocks (2vec->val nbits)
                          (2vec->val blocksz)
                          x.lower)))
    (4vec-x))
  ///
  ;; BOZO can probably strengthen the equivalences
  (deffixequiv 4vec-rev-blocks))

(define 4vec-wildeq-safe ((a 4vec-p) (b 4vec-p))
  :short "True if for every pair of corresponding bits of a and b, either they
          are equal or the bit from b is Z."
  :returns (res 4vec-p)
  (b* ((eq (3vec-bitnot (4vec-bitxor a b))) ;; 4vec-bitxor-redef
       ((4vec b))
       (zmask (logand (lognot b.upper) b.lower))) ;; b is z
    (3vec-reduction-and (3vec-bitor eq (2vec zmask))))
  ///
  (deffixequiv 4vec-wildeq-safe
    :args ((a 3vec)
           (b 4vec))))

(define 4vec-wildeq ((a 4vec-p) (b 4vec-p))
  :short "True if for every pair of corresponding bits of a and b, either they
          are equal or the bit from b is X or Z."
  :long "<p>This is the Verilog semantics for the @('==?') operator. Like ===,
this violates monotonicity, i.e. it doesn't respect the idea that X represents
an unknown.</p>"
  :returns (res 4vec-p)
  (b* ((eq (3vec-bitnot (4vec-bitxor a b))) ;; 4vec-bitxor-redef
       ((4vec b))
       (zxmask (logxor b.upper b.lower))) ;; b is z or x
    (3vec-reduction-and (3vec-bitor eq (2vec zxmask))))
  ///
  (local (defthm logxor-of-3vec-fix
           (equal (logxor (logand l u)
                          (logior l u))
                  (logxor l u))
           :hints ((logbitp-reasoning)
                   (and stable-under-simplificationp
                        '(:in-theory (enable bool->bit))))))

  (deffixequiv 4vec-wildeq
    :args ((a 3vec)
           (b 3vec))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable 3vec-fix))))))

(define 4vec-symwildeq ((a 4vec-p) (b 4vec-p))
  :short "Symmetric wildcard equality: true if for every pair of corresponding
          bits of a and b, either they are equal or the bit from either a or b
          is Z."
  :returns (res 4vec-p)
  (b* ((eq (3vec-bitnot (4vec-bitxor a b))) ;; 4vec-bitxor-redef
       ((4vec a))
       ((4vec b))
       (zmask (logior (logand (lognot b.upper) b.lower)
                      (logand (lognot a.upper) a.lower))))
    (3vec-reduction-and (3vec-bitor eq (2vec zmask))))
  ///
  (deffixequiv 4vec-symwildeq))

(define 4vec-clog2 ((a 4vec-p))
  :short "Ceiling of the log2 of a, or X if any non-2-valued bits.  Must be truncated
          to its width (nonnegative)."
  :returns (res 4vec-p)
  (if (and (2vec-p a)
           (<= 0 (2vec->val a)))
      (2vec (integer-length (- (2vec->val a) 1)))
    (4vec-x))
  ///
  (deffixequiv 4vec-clog2
    :args ((a 2vecnatx))
    :hints(("Goal" :in-theory (enable 2vecnatx-fix)))))


(local (defthm expt-neg1-integerp
         (integerp (expt -1 n))
         :hints (("goal" :in-theory (enable expt)))))

(define 4vec-pow ((base 4vec-p) (exp 4vec-p))
  :short "Power operator (** in SystemVerilog)."
  :long "<p>See Table 11-4 in IEEE System Verilog Spec.</p>"
  :returns (res 4vec-p)
  (if (and (2vec-p base)
           (2vec-p exp))
      (b* ((base (2vec->val base))
           (exp (2vec->val exp))
           ((when (or (natp exp)
                      (eql base 1)
                      (eql base -1)))
            (2vec (expt base exp)))
           ((when (eql base 0)) (4vec-x))) ;; 0 to negative power
        (2vec 0)) ;; a <= -2 or a >= 2, b negative.
    (4vec-x))
  ///
  (deffixequiv 4vec-pow
    :args ((base 2vecx) (exp 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))



(define 4vec-part-select ((lsb 4vec-p)
                          (width 4vec-p)
                          (in 4vec-p))
  :short "Part select operation: select @('width') bits of @('in') starting at @('lsb')."
  :returns (res 4vec-p)
  (if (and (2vec-p lsb)
           (2vec-p width)
           (<= 0 (2vec->val width)))
      (b* ((lsbval (2vec->val lsb))
           ((when (<= 0 lsbval))
            (4vec-zero-ext width (4vec-rsh lsb in))))
        (4vec-zero-ext width (4vec-concat (2vec (- lsbval)) (4vec-x) in)))
    (4vec-x)))

(define 4vec-part-install ((lsb 4vec-p)
                           (width 4vec-p)
                           (in 4vec-p)
                           (val 4vec-p))
  :short "Part install operation: replace @('width') bits of @('in') starting at
          @('lsb') with the least-significant bits of @('val')."
  :returns (res 4vec-p)
  (if (and (2vec-p lsb)
           (2vec-p width)
           (<= 0 (2vec->val width)))
      (b* ((lsbval (2vec->val lsb))
           (widthval (2vec->val width))
           ((when (<= 0 lsbval))
            ;; normal case: result is LSB bits of in, followed by val, followed by more in
            (4vec-concat lsb in (4vec-concat width val (4vec-rsh (2vec (+ lsbval widthval)) in))))
           ((when (<= widthval (- lsbval)))
            ;; if we're writing width bits starting more than width bits below 0, in is unchanged
            (4vec-fix in)))
        ;; otherwise, we're writing, for example,
        ;; 5 bits starting at -3 -- which means 2 bits of val starting at 3, followed by in starting at bit 2.
        (4vec-concat (2vec (+ widthval lsbval))
                     (4vec-rsh (2vec (- lsbval)) val)
                     (4vec-rsh (2vec (+ widthval lsbval)) in)))
    (4vec-x))
  ///
  (local (in-theory (disable unsigned-byte-p)))

  ;; some sanity checks
  (defthm 4vec-part-install-of-part-select
    (implies (and (2vec-p lsb) (2vec-p width) (<= 0 (2vec->val width)))
             (equal (4vec-part-install lsb width in (4vec-part-select lsb width in))
                    (4vec-fix in)))
    :hints(("Goal" :in-theory (enable 4vec-part-select
                                      4vec-zero-ext
                                      4vec-concat
                                      4vec-rsh
                                      4vec-shift-core))
           (logbitp-reasoning :prune-examples nil)))


  (defthm 4vec-part-select-of-install
    (implies (and (2vec-p lsb) (2vec-p width)
                  (<= 0 (2vec->val width)))
             (equal (4vec-part-select lsb width (4vec-part-install lsb width in val))
                    (if (< (2vec->val lsb) 0)
                        (if (< (- (2vec->val lsb)) (2vec->val width))
                            (4vec-concat (2vec (- (2vec->val lsb)))
                                         (4vec-x)
                                         (4vec-zero-ext
                                          (2vec (+ (2vec->val width) (2vec->val lsb)))
                                          (4vec-rsh (2vec (- (2vec->val lsb))) val)))
                          (4vec-zero-ext width (4vec-x)))
                      (4vec-zero-ext width val))))
    :hints(("Goal" :in-theory (enable 4vec-part-select
                                      4vec-zero-ext
                                      4vec-concat
                                      4vec-rsh
                                      4vec-shift-core))
           (logbitp-reasoning :prune-examples nil))))







;;ANNA: Converting 4vec-p / 4veclist-p to string(s) of 0s, 1s, Xs, and Zs
;;MSB first

(define 4v-to-characterp
  ((upper booleanp)
   (lower booleanp))
  :returns (c characterp)
  (if (equal upper lower)
      (if upper #\1 #\0)
    (if (and upper (not lower))
        #\x
      #\z))
  )

(define 4vec-p-to-stringp-aux
  ((x.upper integerp)
   (x.lower integerp)
   (i natp)
   (ac character-listp)
   )
  (if (zp i)
      (coerce (reverse ac) 'string)
    (4vec-p-to-stringp-aux
      x.upper
      x.lower
      (1- i)
      (cons
       (4v-to-characterp
        (logbitp (1- i) x.upper)
        (logbitp (1- i) x.lower))
       ac)))
  )

(define 4vec-p-to-stringp
  ((x 4vec-p))
  :short "Converts 4vec-p into string of 0,1,x,z's msb-first"
  :returns (x-string stringp)
  :prepwork ((local
              (defthm character-listp-of-explode-nonnegative-integer
                (implies
                 (and
                  (integerp x)
                  (<= 0 x)
                  (character-listp ans))
                 (character-listp (explode-nonnegative-integer x base ans)))
                :hints (("goal"
                         :in-theory (enable explode-nonnegative-integer) ))
                )))
  :guard-hints (("goal" :in-theory (e/d (4vec-p)(floor) )))
  (if (integerp x)
      (coerce (explode-atom x 2) 'string)
    (4vec-p-to-stringp-aux
     (car x) (cdr x)
     (max (integer-length (car x))
          (integer-length (cdr x)))
     nil))
  )

(define 4veclist-p-to-stringp
  ((x 4veclist-p))
  :short  "Converts 4veclist-p into list of strings of 0,1,x,z's msb-first"
  :returns (x-string-list string-listp)
  (if (atom x)
      nil
    (cons
     (4vec-p-to-stringp (car x))
     (4veclist-p-to-stringp (cdr x))))
  )


(define 4vec-xfree-p ((x 4vec-p))
  :parents (4vec-[= svex-xeval)
  :short "Recognizer for @(see 4vec)s with no X bits.  These have a special
relationship with @(see svex-xeval)."
  (b* (((4vec x) x))
    (eql -1 (logior (lognot x.upper) x.lower))))



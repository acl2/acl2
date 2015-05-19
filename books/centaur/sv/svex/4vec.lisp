; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(include-book "centaur/4v-sexpr/4v-logic" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)
(include-book "centaur/bitops/parity" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection bozo
  ;; BOZO 1 -- These are non-local and enabled
  ;; BOZO 2 -- These look obviously great, move to bitops/ihsext-basics if possible

  (defthm logand-self-identity
    (equal (logand x x)
           (ifix x))
    :hints ((acl2::equal-by-logbitp-hammer)))

  (defthm logior-self-identity
    (equal (logior x x)
           (ifix x))
    :hints ((acl2::equal-by-logbitp-hammer))))


;; BOZO consider whether any of these can be integrated into bitops

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

(local (defthm logior-logand-id-1
         (equal (logior b (logand a b))
                (ifix b))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logand-logior-id-1
         (equal (logand b (logior a b))
                (ifix b))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logior-neg-1-when-logand-neg-1
         (implies (equal (logand a b) -1)
                  (equal (logior a b) -1))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))



(defsection 4vec-operations
  :parents (expressions)
  :short "Core operations on @(see 4vec)s."

  :long "<p>We now introduce many operations on @(see 4vec)s.  These operations
are generally intended to support the modeling of Verilog and SystemVerilog
expressions.  For instance, our @(see 4vec-plus) operation agrees with the
Verilog notion of plus: if there are any X or Z bits in either input, it
``conservatively'' returns all Xes.</p>

<p>Most of these operations have corresponding @(see svex) functions and can
hence be used in @(see expressions).  See in particular @(see svex-functions).
Because of this, for each of the operations below, we are especially interested
in the performance of symbolic simulation with @(see gl).  Concrete execution
efficiency is of less importance, but in most cases we can do well in both
contexts.</p>

<p>These operations have many similarities to the @(see acl2::4v-operations)
which were used in by @(see acl2::esim).  However, since SV expressions are
vectors instead of single bits, there are many 4vec operations with no 4v
equivalents (e.g., plus, times, etc.).  Historically these operations were
bit-blasted using the @(see vl2014::occform) transformation, but in svex they
are primitives with well-defined semantics.</p>")


(define 4vec-idx->4v
  :short "Like @(see logbit) for @(see 4vec)s, for fixed indices, producing an
@(see acl2::4v)-style @(see acl2::4vp)."
  ((n natp   "The bit position to extract.")
   (x 4vec-p "The @(see 4vec) to extract it from."))
  :returns (bit acl2::4vp)
  :long "<p>This function is mainly used in correspondence theorems that show
the relationship between our @(see 4vec-operations) and the simple, four-valued
bit operations provided in the @(see acl2::4v) library.</p>"
  (b* (((4vec x) x)
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
  :short "Convert a boolean into an infinite-width @(see 2vec)."
  :inline t
  (if x -1 0)
  ///
  (defthm bool->vec-cases
    (and (implies x
                  (equal (bool->vec x) -1))
         (implies (not x)
                  (equal (bool->vec x) 0)))))


(defsection 3vec-operations
  :parents (expressions)
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
   (b* (((4vec x) x))
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
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitnot ((x 4vec-p))
  :parents (4vec-operations)
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
             (b* (((4vec x) x)
                  ((4vec y) y))
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
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitand ((x 4vec-p) (y 4vec-p))
  :parents (4vec-operations)
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
             (b* (((4vec x) x)
                  ((4vec y) y))
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
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitor ((x 4vec-p) (y 4vec-p))
  :parents (4vec-operations)
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
             (b* (((4vec x) x)
                  ((4vec y) y)
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
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitxor ((x 4vec-p) (y 4vec-p))
  :parents (4vec-operations)
  :short "Bitwise logical XOR of @(see 4vec)s."
  :guard-hints ((acl2::equal-by-logbitp-hammer))
  :returns (x^y 3vec-p! :hints (("goal" :in-theory (enable 3vec-p))
                                (acl2::equal-by-logbitp-hammer)))
  (if-2vec-p (x y)
             (2vec (logxor (2vec->val x) (2vec->val y)))
             (b* (((4vec x) x)
                  ((4vec y) y)
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
  :parents (4vec-operations)
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
  (b* (((4vec a) a)
       ((4vec b) b))
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
  :parents (4vec-operations)
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
  (b* (((4vec a) a)
       ((4vec b) b))
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
  :parents (4vec-operations)
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
  (b* (((4vec a) a)
       ((4vec b) b))
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


(define 4vec-zero-ext ((n 4vec-p "Position to truncate/zero-extend at.")
                       (x 4vec-p "The @(see 4vec) to truncate/zero-extend."))
  :returns (x-ext 4vec-p)
  :parents (4vec-operations)
  :short "Like @(see loghead) for @(see 4vec)s; the width is also a @(see
4vec)."

  :long "<p>When @('n') is a natural number, we keep the least significant
@('n') bits of @('x') and clear any bits above this to zero.</p>

<p>When @('n') has any X or Z bits or is negative, the result is all X
bits.</p>"

  (if (and (2vec-p n)
           (<= 0 (2vec->val n)))
      (if-2vec-p (x)
                 (2vec (loghead (2vec->val n) (2vec->val x)))
                 (b* (((4vec x) x)
                      (nval (2vec->val n)))
                   (4vec (loghead nval x.upper)
                         (loghead nval x.lower))))
    (4vec-x))
  ///
  (deffixequiv 4vec-zero-ext))


(define 4vec-sign-ext ((n 4vec-p)
                       (x 4vec-p))
  :returns (x-ext 4vec-p)
  :parents (4vec-operations)
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
                 (b* (((4vec x) x)
                      (nval (2vec->val n)))
                   (4vec (fast-logext nval x.upper)
                         (fast-logext nval x.lower))))
    (4vec-x))
  ///
  (deffixequiv 4vec-sign-ext))




(define 4v->4vec-bit ((x acl2::4vp))
  :returns (vec 4vec-p)
  :parents (4v-operations)
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
  (if-2vec-p (x)
             (2vec (bool->vec (int= (2vec->val x) -1)))
             (b* (((4vec x) x))
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
                    (b* (((4vec x) x))
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
                    :controller-alist ((3vec-reduction-and t))))))


(define 4vec-reduction-and ((x 4vec-p))
  :parents (4vec-operations)
  :short "Reduction logical AND of a @(see 4vec)."
  :long "<p>ANDs together all of the bits in a 4vec.  If any bit is 0, the
result will be 0; otherwise if any bit is X or Z, the result is X (extended to
infinity), otherwise the result is -1.</p>

<p><b>Subtle</b>.  Since @(see 4vec)s are ``infinite width,'' reduction
operations are a bit unusual.  For reduction AND, when translating from Verilog
or other languages where your vectors are only some particular width, you will
typically need to <i>always sign-extend the input vector</i>, regardless of
whether it is signed or unsigned.  That is, say you start with a unsigned 5-bit
vector whose value is @('11111').  If you create your (infinite width) 4vec for
this by zero extension, you'll end up with infinitely many leading 0s, which
will cause the reduction AND of your vector to be 0!</p>"
  :returns (and-x 3vec-p!)
  (3vec-reduction-and (3vec-fix x))
  ///
  (defthmd 4vec-reduction-and-recursive
    (equal (4vec-reduction-and x)
           (b* (((4vec x) x)
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
  :returns (or-x 4vec-p)
  (if-2vec-p (x)
             (2vec (bool->vec (not (int= (2vec->val x) 0))))
             (b* (((4vec x) x))
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
                    (b* (((4vec x) x))
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
                    :controller-alist ((3vec-reduction-or t))))))


(define 4vec-reduction-or ((x 4vec-p))
  :parents (4vec-operations)
  :short "Reduction logical OR of a @(see 4vec)."

  :long "<p>ORs together all of the bits in a 4vec.  If any bit is 1, the
result will be -1 (infinite true bits); otherwise if any bit is X or Z, the
result is X (extended to infinity), otherwise the result is 0.</p>

<p>When translating Verilog, the input vector may be either sign- or 0-extended
without affecting the result.</p>"
    :returns (or-x 3vec-p!)
    (3vec-reduction-or (3vec-fix x))
    ///
    (defthmd 4vec-reduction-or-recursive
      (equal (4vec-reduction-or x)
             (b* (((4vec x) x)
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
  :parents (4vec-operations)
  :short "Like @(see logapp) for @(see 4vec)s; the width is also a @(see 4vec)."

  :long "<p>In the usual case, @('width') is some natural number: we
concatenate the @('width') least significant bits of @('low') with all of
@('high').  That is, we produce a new @(see 4vec) which might be written in
Verilog as @('{high, low[width-1:0]}').</p>

<p>Since @('width') is a @(see 4vec) it may have X or Z bits or may be
negative.  In this case, the result is infinite Xes.</p>"

  (if (and (2vec-p width)
           (<= 0 (2vec->val width)))
      (b* ((wval (2vec->val width)))
        (if-2vec-p (low high)
                   (2vec (logapp wval (2vec->val low) (2vec->val high)))
                   (b* (((4vec low) low)
                        ((4vec high) high))
                     (4vec (logapp wval low.upper high.upper)
                           (logapp wval low.lower high.lower)))))
    (4vec-x))
  ///
  (deffixequiv 4vec-concat
    :args ((width 2vecnatx :hints(("Goal" :in-theory (enable 2vecnatx-fix))))
           (low   4vec)
           (high  4vec))))

(define 4vec-rsh ((amt 4vec-p "Shift amount.")
                  (x   4vec-p "Source operand."))
  :returns (shifted 4vec-p)
  :parents (4vec-operations)
  :short "Right shift of @(see 4vec)s."
  :long "<p>If @('amt') has any X or Z bits, the result is all Xes.  If it
is negative, then @('x') is left-shifted.</p>"
  (if (2vec-p amt)
      (if-2vec-p (x)
                 (2vec (ash (2vec->val x) (- (2vec->val amt))))
                 (b* (((4vec x) x)
                      (shamt (- (2vec->val amt))))
                   (4vec (ash x.upper shamt)
                         (ash x.lower shamt))))
    (4vec-x))
  ///
  (deffixequiv 4vec-rsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (x   4vec))))

(define 4vec-lsh ((amt 4vec-p "Shift amount.")
                  (x   4vec-p "Source operand."))
  :returns (shifted 4vec-p)
  :parents (4vec-operations)
  :short "Left-shift 4vec @('x') by @('amt') bits."
  :long "<p>If @('amt') has any X or Z bits, the result is all Xes.  If it is
negative, then @('x') is right-shifted.</p>"
  (if (2vec-p amt)
      (if-2vec-p (x)
                 (2vec (ash (2vec->val x) (2vec->val amt)))
                 (b* (((4vec x) x)
                      (shamt (2vec->val amt)))
                   (4vec (ash x.upper shamt)
                         (ash x.lower shamt))))
    (4vec-x))
  ///
  (deffixequiv 4vec-lsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (x   4vec))))


(define 4vec-parity ((x 4vec-p))
  :returns (par 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  :parents (4vec-operations)
  :short "Reduction logical XOR (i.e., parity) of a @(see 4vec)."

  :long "<p>If @('x') has any X or Z bits, or is a negative number, we just
return all Xes.  Otherwise, @('x') is a natural number and we just return the
parity of its 1 bits.</p>

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


(define 4vec-plus ((x 4vec-p) (y 4vec-p))
  :parents (4vec-operations)
  :short "Addition of @(see 4vec)s."
  :long "<p>This is a fairly conservative definition in the style of the
Verilog semantics: If either input has any X or Z bits, the result is all Xes.
Otherwise, we produce the (signed) sum of the two (signed) inputs.</p>"
  :returns (res 4vec-p)
  (if (and (2vec-p x) (2vec-p y))
      (2vec (+ (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (deffixequiv 4vec-plus
    :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-xdet ((x 4vec-p))
  :parents (4vec-operations)
  :short "Identity function for @(see 2vec)s, but returns all Xes if there is
any X bit."
  :long "<p>This (arguably) matches the Verilog specification for unary +.</p>"
  :returns (res 4vec-p)
  (if (2vec-p x)
      (4vec-fix x)
    (4vec-x))
  ///
  (deffixequiv 4vec-xdet :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-minus ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Subtract two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed difference of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (- (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (deffixequiv 4vec-minus :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-uminus ((x 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "(Arithmetically) negate a 4vec"
  :long "<p>If the input has X or Z bits, the result is all X bits.  Otherwise,
produces the signed negation of the input.</p>"
  (if (2vec-p x)
      (2vec (- (2vec->val x)))
    (4vec-x))
  ///
  (deffixequiv 4vec-uminus :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-times ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Multiply two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (* (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-quotient ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Divide two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y) (not (eql (2vec->val y) 0)))
      (2vec (truncate (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-remainder ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Remainder from division of two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y) (not (eql (2vec->val y) 0)))
      (2vec (rem (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-< ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Arithmetic inequality of two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, does the signed comparison of the two inputs and produces -1 (true)
or 0 (false).</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (bool->vec (< (2vec->val x) (2vec->val y))))
    (4vec-x)))

(define 3vec-== ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Arithmetic equality of two 4vecs"
  :long "<p>Shorthand for (uand (bitnot (bitxor x y))).</p>"
  (3vec-reduction-and (3vec-bitnot (3vec-bitxor x y))))

(define 4vec-== ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Arithmetic equality of two 4vecs"
  :long "<p>Shorthand for (uand (bitnot (bitxor x y))).</p>"
  (3vec-== (3vec-fix x) (3vec-fix y)))

(define 4vec-=== ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Case equality of two 4vecs, Verilog-style"
  :long "<p>Note: this is a bad operation that breaks the lattice discipline.</p>"
  (2vec (bool->vec (equal (4vec-fix x) (4vec-fix y)))))


(define 3vec-? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "If-then-else of 4vecs, with 3vec test"
  :long "<p>If @('x') has any 1-bits, returns @('y'); if @('x') is 0, returns
@('z'); otherwise returns a result consisting of Xes in bit positions where
@('y') and @('z') are unequal and their bits in the positions where they are
equal.</p>"
  (b* (((4vec x) x)
       ((when (eql x.upper 0))
        ;; false
        (4vec-fix z))
       ((when (not (eql x.lower 0)))
        ;; true
        (4vec-fix y))
       ;; otherwise, x
       ((4vec y) y)
       ((4vec z) z)
       (same-bits (logand (logeqv y.upper z.upper)
                          (logeqv y.lower z.lower))))
    (4vec (logior (lognot same-bits) y.upper)
          (logand same-bits y.lower))))

(define 4vec-? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "If-then-else of 4vecs"
  :long "<p>If @('x') has any 1-bits, returns @('y'); if @('x') is 0, returns
@('z'); otherwise returns a result consisting of Xes in bit positions where
@('y') and @('z') are unequal and their bits in the positions where they are
equal.</p>"
  (3vec-? (3vec-fix x) y z))

(define 3vec-bit? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Bitwise if-then-else of 4vecs, with 3vec test"
  :long "<p>For each bit position, if that bit of x is 1, returns that bit of
y; if 0, then that bit of z; otherwise if those bits of y and z are equivalent,
then that bit, else X.  Assumes x has no z values.</p>"
  ;; (~x.upper & z.upper) | (x.lower & y.upper) | (z!=y | y.upper)
  ;; (~x.upper & z.lower) | (x.lower & y.lower) | (z==y & y.lower)
  (b* (((4vec x))
       ((4vec y))
       ((4vec z))
       (same (logand (logeqv y.upper z.upper)
                     (logeqv y.lower z.lower))))
    (4vec (logior (logand (lognot x.upper) z.upper)
                  (logand x.lower y.upper)
                  (logand x.upper (lognot x.lower)
                          (logior (lognot same) y.upper)))
          (logior (logand (lognot x.upper) z.lower)
                  (logand x.lower y.lower)
                  (logand x.upper (lognot x.lower)
                          (logand same y.lower)))))
  ///
  (defthm 3vec-?-in-terms-of-3vec-bit?
    (implies (3vec-p x)
             (equal (3vec-bit? (4vec-sign-ext 1 (3vec-reduction-or x)) y z)
                    (3vec-? x y z)))
    :hints(("Goal" :in-theory (enable 3vec-? 4vec-sign-ext
                                      3vec-p 3vec-reduction-or)))))

(define 4vec-bit? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Bitwise if-then-else of 4vecs"
  :long "<p>For each bit position, if that bit of x is 1, returns that bit of
y; if 0, then that bit of z; otherwise if those bits of y and z are equivalent,
then that bit, else X.  Assumes x has no z values.</p>"
  (3vec-bit? (3vec-fix x) y z)
  ///
  (local (defthm 3vec-fix-of-4vec-sign-ext
           (equal (3vec-fix (4vec-sign-ext n x))
                  (4vec-sign-ext n (3vec-fix x)))
           :hints(("Goal" :in-theory (enable 3vec-fix 4vec-sign-ext))
                  (acl2::logbitp-reasoning))))

  (defthm 4vec-?-in-terms-of-4vec-bit?
    (equal (4vec-bit? (4vec-sign-ext 1 (4vec-reduction-or x)) y z)
           (4vec-? x y z))
    :hints(("Goal" :in-theory (enable 4vec-?
                                      4vec-p 4vec-reduction-or)))))

(define 4vec-index-p ((x 4vec-p))
  (and (2vec-p x)
       (<= 0 (2vec->val x)))
  ///
  (defthm 4vec-index-p-implies
    (implies (4vec-index-p x)
             (and (equal (4vec->lower x) (4vec->upper x))
                  (<= 0 (4vec->lower x))))
    :rule-classes :forward-chaining))


(define 4vec-override ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-operations)
  :short "Resolution for when one signal is stronger than the other"
  :long "<p>(4vec-override x y) takes the value of @('x') for each of its non-Z
bits, and the value of @('y') for bits where x is Z.</p>"
  :guard-hints ((acl2::logbitp-reasoning))

  (b* (((4vec x) x)
       ((4vec y) y))
    (mbe :logic
         (b* ((xz (logand x.lower (lognot x.upper))))
           (4vec (logior (logand xz y.upper) (logand (lognot xz) x.upper))
                 (logior (logand xz y.lower) (logand (lognot xz) x.lower))))
         :exec (4vec (logior (logand x.lower y.upper) x.upper)
                     (logand (logior x.upper y.lower) x.lower))))
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
                 '(:bdd (:vars nil))))))

(define 4vec-onset ((x 4vec-p))
  :returns (res 4vec-p)
  :short "Identity, except Z bits become 0."
  :long "<p>The closest monotonic approximation of the onset of each of the
bits of the input.  It differs from the actual onset in that the 4vec-onset of
an X bit is X.</p>"
  (b* (((4vec x) x))
    (4vec x.upper (logand x.upper x.lower)))
  ///
  (defthm 4vec-onset-bits
    (equal (4vec-idx->4v n (4vec-onset x))
           (let ((in (4vec-idx->4v n x)))
             (if (eq 'z in)
                 'f
               in)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))

(define 4vec-offset ((x 4vec-p))
  :returns (res 4vec-p)
  :short "Negation, except Z bits become 0."
  :long "<p>The closest monotonic approximation of the offset of each of the
bits of the input.  It differs from the actual offset in that the 4vec-offset
of an X bit is X.</p>"
  (b* (((4vec x) x))
    (4vec (lognot x.lower) (lognot (logior x.upper x.lower))))
  ///
  (defthm 4vec-offset-bits
    (equal (4vec-idx->4v n (4vec-offset x))
           (let ((in (4vec-idx->4v n x)))
             (if (eq 'z in)
                 'f
               (acl2::4v-not in))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define rev-blocks ((nbits natp)
                    (blocksz posp)
                    (x integerp))
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
    (logapp next-nbits rest (loghead blocksz x))))

(define rev-block-index ((i natp)
                         (nbits natp)
                         (blocksz posp))
  :short "For reasoning about rev-blocks, computes the offset into x corresponding
          to an offset into @('(rev-blocks nbits blocksz x)')."
  :long "
@({
 (equal (logbitp i (rev-blocks nbits blocksz x))
        (logbitp (rev-block-index i nbits blogksz) x)) })
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


(define 4vec-rev-blocks ((nbits 4vec-p)
                         (blocksz 4vec-p)
                         (x 4vec-p))
  :returns (res 4vec-p)
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
    (4vec-x)))

(define 4vec-wildeq ((a 4vec-p) (b 4vec-p))
  :short "True if for every pair of corresponding bits of a and b, either they
          are equal or the bit from b is Z."
  :returns (res 4vec-p)
  (b* ((eq (3vec-bitnot (4vec-bitxor a b))) ;; 4vec-bitxor-redef
       ((4vec a))
       ((4vec b))
       (zmask (logand (lognot b.upper) b.lower))) ;; b is z
    (3vec-reduction-and (3vec-bitor eq (2vec zmask)))))

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
    (3vec-reduction-and (3vec-bitor eq (2vec zmask)))))

(define 4vec-clog2 ((a 4vec-p))
  :short "Ceiling of the log2 of a, or X if any non-2-valued bits.  Must be truncated
          to its width (nonnegative)."
  :returns (res 4vec-p)
  (if (and (2vec-p a)
           (<= 0 (2vec->val a)))
      (2vec (integer-length (- (2vec->val a) 1)))
    (4vec-x)))

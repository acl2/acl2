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

(in-package "SVEX")
(include-book "svex")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(include-book "centaur/4v-sexpr/4v-logic" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defxdoc 4vec.lisp :parents (4vec))
(local (xdoc::set-default-parents 4vec.lisp))

(fty::deffixtype int :pred integerp :fix ifix :equiv int-equiv)
(fty::deffixtype nat :pred natp :fix nfix :equiv nat-equiv)


(defmacro if-2vec-p (vars 2vec-body 4vec-body)
  `(mbe :logic ,4vec-body
        :exec (if (and . ,(pairlis$ (replicate (len vars) '2vec-p)
                                    (pairlis$ vars nil)))
                  ,2vec-body
                ,4vec-body)))


(define 4vec-bit-index ((n natp) (x 4vec-p))
  :returns (bit 4vec-p)
  (if-2vec-p (x)
             (2vec (logbit (lnfix n) (2vec->val x)))
             (4vec (logbit (lnfix n) (4vec->upper x))
                   (logbit (lnfix n) (4vec->lower x))))
  ///
  (fty::deffixequiv 4vec-bit-index))

(define 4vec-bit-extract ((n 4vec-p) (x 4vec-p))
  :returns (res 4vec-p)
  (if (and (2vec-p n)
           (<= 0 (2vec->val n)))
      (4vec-bit-index (2vec->val n) x)
    (4vec-1x))
  ///
  (fty::deffixequiv 4vec-bit-extract))


(define 4vec-idx->4v ((n natp)
                      (x 4vec-p))
  :returns (bit acl2::4vp)
  (b* (((4vec x) x)
       (n (lnfix n)))
    (if (logbitp n x.upper)
        (if (logbitp n x.lower)
            t
          'x)
      (if (logbitp n x.lower)
          'z
        'f)))
  ///
  (fty::deffixequiv 4vec-idx->4v))

(define 4v->4vec-bit ((x acl2::4vp))
  :returns (bit 4vec-p)
  (case x
    ((t) (2vec -1))
    ((f) (2vec 0))
    (z   (4vec 0 -1))
    (acl2::otherwise (4vec -1 0)))
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


(define 3vec-p ((x 4vec-p))
  :parents (4vec)
  :short "A 4vec is also a 3vec if no bit of it is Z-valued."
  (b* (((4vec x) x))
    (eql (logand x.lower (lognot x.upper)) 0))
  ///

  (defthm 3vec-p-implies-bits
    (and (implies (and (3vec-p x)
                       (not (logbitp n (4vec->upper x))))
                  (not (logbitp n (4vec->lower x))))
         (implies (and (3vec-p x)
                       (logbitp n (4vec->lower x)))
                  (logbitp n (4vec->upper x))))
    :hints (("goal" :use
             ((:instance acl2::logbitp-of-logand
               (acl2::a n) (x (4vec->lower x)) (acl2::y (lognot (4vec->upper x)))))
             :in-theory (disable acl2::logbitp-of-logand))))

  (defthm 4vec-idx->4v-when-3vec-p
    (implies (3vec-p x)
             (not (equal (4vec-idx->4v n x) 'z)))
    :hints(("Goal" :in-theory (enable 3vec-p 4vec-idx->4v)
            :use ((:instance acl2::logbitp-of-logand
                   (acl2::a n) (x (4vec->lower x)) (acl2::y (lognot (4vec->upper x))))))))

  (fty::deffixequiv 4vec-p))

(defthm logand-self-identity
  (equal (logand x x)
         (ifix x))
  :hints ((acl2::equal-by-logbitp-hammer)))

(defthm logior-self-identity
  (equal (logior x x)
         (ifix x))
  :hints ((acl2::equal-by-logbitp-hammer)))

(defmacro 3vec-p! (x)
  `(and (4vec-p ,x) (3vec-p ,x)))


(defxdoc 4vec-functions
  :parents (4vec)
  :short "Functions on 4vec objects")

(define 3vec-fix ((x 4vec-p))
  :parents (4vec-functions)
  :short "Fixes an arbitrary object to a 3vec by turning Zs into Xes."
  :verify-guards nil
  :returns (newx 3vec-p! :hints (("Goal" :in-theory (enable 3vec-p))
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
                        '(:use ((:instance acl2::logbitp-of-logand
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

  (defthm 4vec-idx->4v-of-3vec-fix
    (equal (4vec-idx->4v n (3vec-fix x))
           (let ((x4v  (4vec-idx->4v n x)))
             (if (eq x4v 'z) 'x x4v)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (fty::deffixequiv 3vec-fix)

  (defthm 3vec-fix-idempotent
    (equal (3vec-fix (3vec-fix x)) (3vec-fix x))
    :hints ((acl2::logbitp-reasoning
             :add-hints (:in-theory (enable acl2::b-ior)))))

  (fty::deffixtype 3vec :pred 3vec-p! :fix 3vec-fix :equiv 3vec-equiv :define t :forward t)

  ;; (acl2::def-universal-equiv 3vec-equiv
  ;;   :equiv-terms ((equal (3vec-fix x))))

  (local (in-theory (enable 3vec-equiv)))

  (defrefinement 4vec-equiv 3vec-equiv
    :hints(("Goal" :in-theory (enable 4vec-fix-is-4vec-of-fields)))))


(define 3vec-fix-fast ((x 3vec-p!))
  :enabled t
  (mbe :logic (3vec-fix x)
       :exec x))

(acl2::def-b*-binder 3vecf
  :body
  #!acl2
  `(b* ((,(car args) (svex::3vec-fix-fast ,(car forms)))
        ((svex::4vec ,(car args)) ,(car args)))
     ,rest-expr))



(define 3vec-bitnot ((x 4vec-p))
  :returns (newx (and (4vec-p newx)
                      (implies (3vec-p x) (3vec-p newx)))
                 :hints(("Goal" :in-theory (enable 3vec-p 3vec-fix))
                        (acl2::equal-by-logbitp-hammer)))
  (if-2vec-p
   (x)
   (2vec (lognot (2vec->val x)))
   (b* (((4vec x) x))
     (4vec (lognot x.lower)
           (lognot x.upper))))
  ///
  (defthm 3vec-bitnot-bits
    (implies (3vec-p! x)
             (equal (4vec-idx->4v n (3vec-bitnot x))
                    (acl2::4v-not (4vec-idx->4v n x))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))

(define 4vec-bitnot ((x 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise NOT of a 4vec"
  :returns (newx 3vec-p!)
  (3vec-bitnot (3vec-fix x))
  ///
  (defthm 4vec-bitnot-bits
    (equal (4vec-idx->4v n (4vec-bitnot x))
           (acl2::4v-not (4vec-idx->4v n x))))
  (fty::deffixequiv 4vec-bitnot :args ((x 3vec))))




(define 3vec-bitand ((x 4vec-p) (y 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise and of two 3vecs"
  :returns (newx (and (4vec-p newx)
                      (implies (and (3vec-p x) (3vec-p y)) (3vec-p newx)))
                 :hints(("Goal" :in-theory (enable 3vec-p))
                        (acl2::logbitp-reasoning)))
  (if-2vec-p (x y)
             (2vec (logand (2vec->val x) (2vec->val y)))
             (b* (((4vec x) x)
                  ((4vec y) y))
               (4vec (logand x.upper y.upper)
                     (logand x.lower y.lower))))
  ///
  (defthm 3vec-bitand-bits
    (implies (and (3vec-p! x) (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitand x y))
                    (acl2::4v-and (4vec-idx->4v n (3vec-fix x))
                                  (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitand ((x 4vec-p)
                     (y 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise AND of two 4vecs"
  :returns (newx 3vec-p!)
  (3vec-bitand (3vec-fix x) (3vec-fix y))
  ///
  (defthm 4vec-bitand-bits
    (equal (4vec-idx->4v n (4vec-bitand x y))
           (acl2::4v-and (4vec-idx->4v n x)
                         (4vec-idx->4v n y))))

  (fty::deffixequiv 4vec-bitand :args ((x 3vec) (y 3vec))))




(define 3vec-bitor ((x 4vec-p) (y 4vec-p))
  :returns (newx (and (4vec-p newx)
                      (implies (and (3vec-p x) (3vec-p y)) (3vec-p newx)))
                 :hints(("Goal" :in-theory (enable 3vec-p))
                        (acl2::logbitp-reasoning)))
  (if-2vec-p (x y)
             (2vec (logior (2vec->val x) (2vec->val y)))
             (b* (((4vec x) x)
                  ((4vec y) y))
               (4vec (logior x.upper y.upper)
                     (logior x.lower y.lower))))
  ///
  (defthm 3vec-bitor-bits
    (implies (and (3vec-p! x) (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitor x y))
                    (acl2::4v-or (4vec-idx->4v n (3vec-fix x))
                                 (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitor ((x 4vec-p)
                    (y 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise OR of two 4vecs"
  :returns (newx 3vec-p!)
  (3vec-bitor (3vec-fix x) (3vec-fix y))
  ///
  (defthm 4vec-bitor-bits
    (equal (4vec-idx->4v n (4vec-bitor x y))
           (acl2::4v-or (4vec-idx->4v n x)
                         (4vec-idx->4v n y))))

  (fty::deffixequiv 4vec-bitor :args ((x 3vec) (y 3vec))))


(define 3vec-bitxor ((x 4vec-p) (y 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise xor of two 3vecs"
  :returns (newx (and (4vec-p newx)
                      (implies (and (3vec-p x) (3vec-p y)) (3vec-p newx)))
                 :hints(("Goal" :in-theory (enable 3vec-p))
                        (acl2::logbitp-reasoning)))
  (if-2vec-p (x y)
             (2vec (logxor (2vec->val x) (2vec->val y)))
             (b* (((4vec x) x)
                  ((4vec y) y)
                  (xmask (logior (logand x.upper (lognot x.lower))
                                 (logand y.upper (lognot y.lower)))))
               (4vec (logior xmask (logxor x.upper y.upper))
                     (logand (lognot xmask) (logxor x.lower y.lower)))))
  ///
  (defthm 3vec-bitxor-bits
    (implies (and (3vec-p! x) (3vec-p! y))
             (equal (4vec-idx->4v n (3vec-bitxor x y))
                    (acl2::4v-xor (4vec-idx->4v n (3vec-fix x))
                                  (4vec-idx->4v n (3vec-fix y)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v)))))


(define 4vec-bitxor ((x 4vec-p)
                     (y 4vec-p))
  :parents (4vec-functions)
  :short "Bitwise XOR of two 4vecs"
  :guard-hints ((acl2::equal-by-logbitp-hammer))
  :returns (newx 3vec-p! :hints (("goal" :in-theory (enable 3vec-p))
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

  (defthm 4vec-bitxor-bits
    (equal (4vec-idx->4v n (4vec-bitxor x y))
           (acl2::4v-xor (4vec-idx->4v n x)
                         (4vec-idx->4v n y))))

  (fty::deffixequiv 4vec-bitxor :args ((x 3vec) (y 3vec))
    :hints (("goal" :in-theory (enable 3vec-fix))
            (acl2::equal-by-logbitp-hammer))))

(define 4vec-res ((a 4vec-p) (b 4vec-p))
  :parents (4vec-functions)
  :short "Resolution of two 4vecs"
  :long "<p>Resolves together two 4vecs as if they were both shorted together.
Each bit of the result is determined by the corresponding bits of the two
inputs as follows:</p>

<ul>
<li>If both input bits have the same value, then the resulting bit is that value.</li>
<li>If one input bit is Z, the result is the other input bit.</li>
<li>Otherwise, the result is X.</li>
</ul>"
  :returns (newx 4vec-p)
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
  (defthm 4vec-res-bits
    (equal (4vec-idx->4v n (4vec-res x y))
           (acl2::4v-res (4vec-idx->4v n x)
                         (4vec-idx->4v n y)))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (fty::deffixequiv 4vec-res))


(define 4vec-resand ((a 4vec-p) (b 4vec-p))
  :parents (4vec-functions)
  :short "Resolution of two 4vecs as in a wired AND"
  :long "<p>Resolves together two 4vecs as if they were both assigned to a
\"wand\" net in Verilog.  Each bit of the result is determined by the
corresponding bits of the two inputs as follows:</p>

<ul>
<li>If either input is 0, the result is 0.</li>
<li>If either input is Z, the result is the other input bit.</li>
<li>If both inputs are 1, the result is 1.</li>
<li>If one input is X and the other is not 0, the result is X.</li>
</ul>"
  :returns (newx 4vec-p)
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
  (defthm 4vec-resand-bits
    (equal (4vec-idx->4v n (4vec-resand x y))
           (let ((x (4vec-idx->4v n x))
                 (y (4vec-idx->4v n y)))
             (cond ((or (eq x (acl2::4vf))
                        (eq y (acl2::4vf)))
                    (acl2::4vf))
                   ((eq x (acl2::4vz)) y)
                   ((eq y (acl2::4vz)) x)
                   ((eq x y) x)
                   (t (acl2::4vx)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (fty::deffixequiv 4vec-resand))

(define 4vec-resor ((a 4vec-p) (b 4vec-p))
  :parents (4vec-functions)
  :short "Resolution of two 4vecs as in a wired OR"
  :long "<p>Resolves together two 4vecs as if they were both assigned to a
\"wor\" net in Verilog.  Each bit of the result is determined by the
corresponding bits of the two inputs as follows:</p>

<ul>
<li>If either input is 1, the result is 1.</li>
<li>If either input is Z, the result is the other input bit.</li>
<li>If both inputs are 0, the result is 0.</li>
<li>If one input is X and the other is not 1, the result is X.</li>
</ul>"
  :returns (newx 4vec-p)
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
  (defthm 4vec-resor-bits
    (equal (4vec-idx->4v n (4vec-resor x y))
           (let ((x (4vec-idx->4v n x))
                 (y (4vec-idx->4v n y)))
             (cond ((or (eq x (acl2::4vt))
                        (eq y (acl2::4vt)))
                    (acl2::4vt))
                   ((eq x (acl2::4vz)) y)
                   ((eq y (acl2::4vz)) x)
                   ((eq x y) x)
                   (t (acl2::4vx)))))
    :hints(("Goal" :in-theory (enable 4vec-idx->4v))))

  (fty::deffixequiv 4vec-resor))


(defsection 4vec-reduction-ops

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

  ;; (local (defun ind3 (x y z)
  ;;          (declare (xargs :measure (+ (integer-length x)
  ;;                                      (integer-length y)
  ;;                                      (integer-length z))
  ;;                          :hints(("Goal" :in-theory (enable acl2::integer-length**)))))
  ;;          (if (and (or (zip x) (eql x -1))
  ;;                   (or (zip y) (eql y -1))
  ;;                   (or (zip z) (eql z -1)))
  ;;              x
  ;;            (ind3 (logcdr x) (logcdr y) (logcdr z)))))

  (local (defthm logior-of-three-negative-1
           (implies (equal (logior a b) -1)
                    (equal (logior a b c) -1))
           :hints (("goal" :use ((:instance acl2::associativity-of-logior
                                  (acl2::a a) (acl2::b b) (acl2::c c)))
                    :in-theory (disable acl2::associativity-of-logior)))))

  (local (defthm logior-logand-id-1
           (equal (logior b (logand a b))
                  (ifix b))
           :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                              acl2::ihsext-recursive-redefs)))))

  (local (defthm logand-logior-id-1
           (equal (logand b (logior a b))
                  (ifix b))
           :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                              acl2::ihsext-recursive-redefs)))))

  (local (defthm logior-neg-1-when-logand-neg-1
           (implies (equal (logand a b) -1)
                    (equal (logior a b) -1))
           :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                              acl2::ihsext-recursive-redefs)))))

  (define bool->vec (x)
    (if x -1 0)
    ///
    (defthm bool->vec-cases
      (and (implies x
                    (equal (bool->vec x) -1))
           (implies (not x)
                    (equal (bool->vec x) 0)))))

  (define 3vec-reduction-and ((x 4vec-p))
    :parents (4vec-functions)
    :returns (newx (and (4vec-p newx)
                        (implies (3vec-p x) (3vec-p newx)))
                   :hints(("Goal" :in-theory (enable 3vec-p bool->vec))))
    :prepwork ((local (defthm lower-of-3vec-not-neg-1
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
                               (acl2::logbitp-reasoning)))))
    (if-2vec-p (x)
               (2vec (bool->vec (int= (2vec->val x) -1)))
               (b* (((4vec x) x))
                 (4vec (bool->vec (int= x.upper -1))
                       (bool->vec (int= x.lower -1)))))
    ///
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
    :parents (4vec-functions)
    :short "Redunction AND of a 4vec."
    :long "<p>ANDs together all of the bits in a 4vec.  If any bit is 0, the
result will be 0; otherwise if any bit is X or Z, the result is X (extended to
infinity), otherwise the result is -1.  When translating Verilog, this means
the input vector needs to be sign extended regardless of its type -- if it is
0-extended, the result will always be 0!</p>"
    :returns (newx 3vec-p!)
    (3vec-reduction-and (3vec-fix x))
    ///

    (defthmd 4vec-reduction-and-recursive
      (equal (4vec-reduction-and x)
             (b* (((4vec x) x))
               (if (and (or (zip x.upper) (eql x.upper -1))
                        (or (zip x.lower) (eql x.lower -1)))
                   (3vec-fix x)
                 (4v->4vec-bit
                  (acl2::4v-and (4vec-idx->4v 0 x)
                                (4vec-idx->4v 0 (4vec-reduction-and
                                                 (4vec (logcdr x.upper)
                                                       (logcdr x.lower)))))))))
      :hints(("Goal":in-theory (e/d (4vec-idx->4v 4vec-bit-index
                                                  bool->vec
                                                  3vec-fix 3vec-reduction-and
                                                  acl2::b-and acl2::b-ior)
                                    (acl2::logand-with-negated-bitmask))
              :expand ((logand (4vec->lower x) (4vec->upper x))
                       (logior (4vec->lower x) (4vec->upper x))
                       (:free (x) (logbitp 0 x)))))
      :rule-classes ((:definition :install-body nil
                      :clique (4vec-reduction-and)
                      :controller-alist ((4vec-reduction-and t)))))

    (fty::deffixequiv 4vec-reduction-and :args ((x 3vec))))

  (define 3vec-reduction-or ((x 4vec-p))
    :parents (4vec-functions)
    :returns (newx (and (4vec-p newx)
                        (implies (3vec-p x) (3vec-p newx)))
                   :hints(("Goal" :in-theory (enable 3vec-p bool->vec))))
    :prepwork ((local (defthm upper-of-3vec-not-zero
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
                               (acl2::logbitp-reasoning)))))
    (if-2vec-p (x)
               (2vec (bool->vec (not (int= (2vec->val x) 0))))
               (b* (((4vec x) x))
                 (4vec (bool->vec (not (int= x.upper 0)))
                       (bool->vec (not (int= x.lower 0))))))
    ///
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
    :parents (4vec-functions)
    :short "Redunction OR of a 4vec."
    :long "<p>ORs together all of the bits in a 4vec.  If any bit is 1, the
result will be -1; otherwise if any bit is X or Z, the result is X (extended to
infinity), otherwise the result is 0.  When translating Verilog, the input
vector may be either sign- or 0-extended without affecting the result.</p>"
    :returns (newx 3vec-p!)
    (3vec-reduction-or (3vec-fix x))
    ///

    (defthmd 4vec-reduction-or-recursive
      (equal (4vec-reduction-or x)
             (b* (((4vec x) x))
               (if (and (or (zip x.upper) (eql x.upper -1))
                        (or (zip x.lower) (eql x.lower -1)))
                   (3vec-fix x)
                 (4v->4vec-bit
                  (acl2::4v-or (4vec-idx->4v 0 x)
                                (4vec-idx->4v 0 (4vec-reduction-or
                                                 (4vec (logcdr x.upper)
                                                       (logcdr x.lower)))))))))
      :hints(("Goal":in-theory (e/d (4vec-idx->4v 4vec-bit-index
                                                  bool->vec
                                                  3vec-fix 3vec-reduction-or
                                                  acl2::b-and acl2::b-ior)
                                    (acl2::logand-with-negated-bitmask))
              :expand ((logand (4vec->lower x) (4vec->upper x))
                       (logior (4vec->lower x) (4vec->upper x))
                       (:free (x) (logbitp 0 x)))))
      :rule-classes ((:definition :install-body nil
                      :clique (4vec-reduction-or)
                      :controller-alist ((4vec-reduction-or t)))))
    (fty::deffixequiv 4vec-reduction-or :args ((x 3vec)))))

(define 4vec-zero-ext ((n 4vec-p)
                       (x 4vec-p))
  :parents (4vec-functions)
  :short "Zero-extend a 4vec at a given width (also a 4vec)."
  :long "<p>Extends 4vec @('x') with zeros at bit width @('n').  If @('n') has
any X or Z bits or is negative, the result is all X bits.</p>"
  :returns (newx 4vec-p)
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
  (fty::deffixequiv 4vec-zero-ext))

(define 4vec-sign-ext ((n 4vec-p)
                       (x 4vec-p))
  :parents (4vec-functions)
  :short "Sign-extend a 4vec at a given width (also a 4vec)."
  :long "<p>Extends 4vec @('x') with its sign bit at bit width @('n').  If @('n') has
any X or Z bits or is not positive, the result is all X bits.</p>"
  :returns (newx 4vec-p)
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
  (fty::deffixequiv 4vec-sign-ext))

(define 2vecx-p ((x 4vec-p))
  (let ((x (4vec-fix x)))
    (or (2vec-p x)
        (equal x (4vec-x))))
  ///
  (defmacro 2vecx-p! (x)
    `(and (4vec-p ,x) (2vecx-p ,x))))

(define 2vecx-fix ((x 4vec-p))
  :returns (fix 2vecx-p! :hints(("Goal" :in-theory (enable 2vecx-p))))
  (if (2vec-p x)
      (4vec-fix x)
    (4vec-x))
  ///
  (local (in-theory (enable 2vecx-p)))

  (defthm 2vecx-fix-of-2vecx-p
    (implies (2vecx-p x)
             (equal (2vecx-fix x)
                    (4vec-fix x))))

  (fty::deffixequiv 2vecx-fix :args ((x 3vec))
    :hints(("Goal" :in-theory (enable 3vec-fix))
           (acl2::logbitp-reasoning
            :add-hints
            (:in-theory (enable* acl2::logbitp-case-splits
                                 acl2::logbitp-of-const-split
                                 acl2::b-and
                                 acl2::b-ior)))))

  (acl2::def-universal-equiv 2vecx-equiv
    :equiv-terms ((equal (2vecx-fix x))))

  (local (in-theory (enable 2vecx-equiv)))

  (defrefinement 3vec-equiv 2vecx-equiv
    :hints(("Goal" :in-theory (disable 2vecx-fix))))

  (defcong 2vecx-equiv equal (2vecx-fix x) 1)

  (fty::deffixtype 2vecx :pred 2vecx-p! :fix 2vecx-fix :equiv 2vecx-equiv))


(define 2vecnatx-p ((x 4vec-p))
  (let ((x (4vec-fix x)))
    (or (and (2vec-p x)
             (<= 0 (2vec->val x)))
        (equal x (4vec-x))))
  ///
  (defmacro 2vecnatx-p! (x)
    `(and (4vec-p ,x) (2vecnatx-p ,x))))

(define 2vecnatx-fix ((x 4vec-p))
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

  (fty::deffixequiv 2vecnatx-fix :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix))
           (acl2::logbitp-reasoning)))

  (acl2::def-universal-equiv 2vecnatx-equiv
    :equiv-terms ((equal (2vecnatx-fix x))))

  (local (in-theory (enable 2vecnatx-equiv)))

  (defrefinement 2vecx-equiv 2vecnatx-equiv
    :hints(("Goal" :in-theory (disable 2vecnatx-fix))))

  (defcong 2vecnatx-equiv equal (2vecnatx-fix x) 1)

  (fty::deffixtype 2vecnatx :pred 2vecnatx-p! :fix 2vecnatx-fix :equiv 2vecnatx-equiv))





(define 4vec-concat ((w 4vec-p "width of less-significant vec")
                     (x 4vec-p "source of the W less-significant bits")
                     (y 4vec-p "source of the rest of the bits"))
  :parents (4vec-functions)
  :short "Concatenate two 4vecs, using the @('w') least-significant bits of @('x')."
  :long "<p>Concatenates the @('w') lowest bits of 4vec @('x') with all of
@('y').  If @('w') has any X or Z bits or is negative, the result is all X
bits.</p>"
  :returns (concat 4vec-p)
  (if (and (2vec-p w)
           (<= 0 (2vec->val w)))
      (b* ((wval (2vec->val w)))
        (if-2vec-p (x y)
                   (2vec (logapp wval (2vec->val x) (2vec->val y)))
                   (b* (((4vec x) x)
                        ((4vec y) y))
                     (4vec (logapp wval x.upper y.upper)
                           (logapp wval x.lower y.lower)))))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-concat
    :args ((w 2vecnatx :hints(("Goal" :in-theory (enable 2vecnatx-fix))))
           (x 4vec) (y 4vec))))

(define 4vec-rsh ((amt 4vec-p "shift amount")
                  (x 4vec-p))
  :parents (4vec-functions)
  :short "Right-shift 4vec @('x') by @('amt') bits."
  :long "<p>If @('amt') has any X or Z bits, the result is all X bits.  If it
is negative, then @('x') is left-shifted.</p>"
  :returns (res 4vec-p)
  (if (2vec-p amt)
      (if-2vec-p (x)
                 (2vec (ash (2vec->val x) (- (2vec->val amt))))
                 (b* (((4vec x) x)
                      (shamt (- (2vec->val amt))))
                   (4vec (ash x.upper shamt)
                         (ash x.lower shamt))))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-rsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (x 4vec))))

(define 4vec-lsh ((amt 4vec-p "shift amount")
                  (x 4vec-p))
  :parents (4vec-functions)
  :short "Left-shift 4vec @('x') by @('amt') bits."
  :long "<p>If @('amt') has any X or Z bits, the result is all X bits.  If it
is negative, then @('x') is right-shifted.</p>"
  :returns (res 4vec-p)
  (if (2vec-p amt)
      (if-2vec-p (x)
                 (2vec (ash (2vec->val x) (2vec->val amt)))
                 (b* (((4vec x) x)
                      (shamt (2vec->val amt)))
                   (4vec (ash x.upper shamt)
                         (ash x.lower shamt))))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-lsh
    :args ((amt 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix))))
           (x 4vec))))

(define parity-rec ((n natp) (x integerp))
  :measure (nfix n)
  :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
          :expand ((integer-length x))))
  :prepwork ((local (defthm bitp-logxor
                      (implies (and (bitp x) (bitp y))
                               (bitp (logxor x y)))
                      :hints(("Goal" :in-theory (enable bitp))))))
  :returns (p bitp)
  (cond ((zp n) 0)
        (t (logxor (logand x 1) (parity-rec (1- n) (ash x -1)))))
  ///
  (fty::deffixequiv parity-rec)

  (defthm parity-rec-decomp
    (equal (logxor (parity-rec m (logtail n x))
                   (parity-rec n (loghead n x)))
           (parity-rec (+ (nfix m) (nfix n)) x))
    :hints (("goal" :in-theory (enable* acl2::ihsext-inductions)
             :induct (loghead n x)
             :expand ((loghead n x)
                      (:free (x) (loghead 1 x))
                      (logtail n x)
                      (:free (x) (logtail 1 x))
                      (:free (n) (parity-rec n x))
                      (:free (x) (parity-rec n x))
                      (parity-rec m (ifix x))))))
  (defthm parity-rec-of-logxor
    (equal (parity-rec n (logxor x y))
           (logxor (parity-rec n x)
                   (parity-rec n y))))

  (defthm parity-rec-of-0
    (equal (parity-rec n 0) 0))

  (defthm parity-rec-of-loghead-split
    (equal (parity-rec m (loghead n x))
           (parity-rec (min (nfix m) (nfix n)) x))
    :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions)
            :induct (list (loghead m x)
                          (loghead n x))
             :expand ((loghead n x)
                      (:free (x) (loghead 1 x))
                      (logtail n x)
                      (:free (x) (logtail 1 x))
                      (:free (n) (parity-rec n x))
                      (:free (x) (parity-rec m x))
                      (parity-rec m (ifix x)))))))


;; Note: we currently don't use parity4 to implement parity32 below, but we could (and maybe should, if we can figure out how to make it faster than the last five lines of parity32.
(define parity4 ((x :type (unsigned-byte 4)))
  :inline t
  :enabled t
  :verify-guards nil
  :returns (p bitp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (parity-rec 4 x)
       :exec ;; (the bit (logand 1
             ;;                  (the (unsigned-byte 32)
             ;;                    (ash (the (unsigned-byte 32) #x6996)
             ;;                         (the (integer -16 0) (- (the (unsigned-byte 4) x)))))))
       (the bit (logbit (the (unsigned-byte 5) x)
                        (the (unsigned-byte 16) #x6996)))
       )
  ///
  (local (fty::deffixequiv parity4 :args ((x int))))
  (local (defun check-parity4 (x)
           (if (zp x)
               t
             (let ((x (1- x)))
               (and (equal (parity4 x) (logbit x #x6996))
                    (check-parity4 x))))))
  (local (defthm check-parity4-correct
           (implies (and (< (ifix x) (nfix n))
                         (<= 0 (ifix x))
                         (check-parity4 n))
                    (equal (logbit x #x6996)
                           (parity4 x)))
           :hints(("Goal" :in-theory (disable parity4)))))
  (verify-guards parity4$inline
    :hints (("goal" :use ((:instance check-parity4-correct
                           (n 16)))))))


(define parity32 ((x :type (unsigned-byte 32)))
  :inline t
  :enabled t
  :guard-hints (("goal" :expand ((:free (n x) (parity-rec n x)))))
  (mbe :logic (parity-rec 32 x)
       :exec
       (b* ((x (the (unsigned-byte 32)
                 (logxor x (the (unsigned-byte 32) (ash x -16)))))
            (x (the (unsigned-byte 32)
                 (logxor x (the (unsigned-byte 32) (ash x -8)))))
            (x (the (unsigned-byte 32)
                 (logxor x (the (unsigned-byte 32) (ash x -4)))))
            (x (the (unsigned-byte 32)
                 (logxor x (the (unsigned-byte 32) (ash x -2)))))
            (x (the (unsigned-byte 32)
                 (logxor x (the (unsigned-byte 32) (ash x -1))))))
         (the (unsigned-byte 1) (logand 1 x)))))

(define parity-fast ((n natp) (x integerp))
  :enabled t
  :returns (p bitp :rule-classes (:rewrite :type-prescription))
  :guard-hints (("goal" :in-theory (e/d (nfix)
                                        (logmask parity-rec-decomp))
                 :expand ((:free (n x) (parity-fast n x)))
                 :use ((:instance parity-rec-decomp
                        (n 32) (m (- n 32))))))
  (mbe :logic (parity-rec n x)
       :exec (if (<= n 32)
                 (parity32 (logand (logmask n) x))
               (logxor (parity32 (logand #xffffffff x))
                       (parity-fast (- n 32) (ash x -32))))))


(define 4vec-parity ((x 4vec-p))
  :parents (4vec-functions)
  :short "Compute the parity of a 4vec."
  :long "<p>If @('x') has any X or Z bits or is negative, the result is all X
bits.  Otherwise, the result is the parity of the (finite) number of 1-bits in
@('x').</p>"
  :returns (x 3vec-p! :hints(("Goal" :in-theory (enable 3vec-p))))
  (if (and (2vec-p x)
           (<= 0 (2vec->val x)))
      (b* ((x (2vec->val x)))
        (2vec (- (parity-fast (+ 1 (integer-length x)) x))))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-parity
    :args ((x 2vecx :hints(("Goal" :in-theory (enable 2vecx-fix)))))))





(define 4vec-plus ((x 4vec-p) (y 4vec-p))
  :parents (4vec-functions)
  :short "Sum two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed sum of the two inputs.</p>"
  :returns (res 4vec-p)
  (if (and (2vec-p x) (2vec-p y))
      (2vec (+ (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-plus :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-minus ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Subtract two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed difference of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (- (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-minus :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-uminus ((x 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "(Arithmetically) negate a 4vec"
  :long "<p>If the input has X or Z bits, the result is all X bits.  Otherwise,
produces the signed negation of the input.</p>"
  (if (2vec-p x)
      (2vec (- (2vec->val x)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-uminus :args ((x 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-times ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Multiply two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (* (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-quotient ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Divide two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y) (not (eql (2vec->val y) 0)))
      (2vec (truncate (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-remainder ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Remainder from division of two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, produces the signed product of the two inputs.</p>"
  (if (and (2vec-p x) (2vec-p y) (not (eql (2vec->val y) 0)))
      (2vec (rem (2vec->val x) (2vec->val y)))
    (4vec-x))
  ///
  (fty::deffixequiv 4vec-times :args ((x 2vecx) (y 2vecx))
    :hints(("Goal" :in-theory (enable 2vecx-fix)))))

(define 4vec-< ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Arithmetic inequality of two 4vecs"
  :long "<p>If either input has X or Z bits, the result is all X bits.
Otherwise, does the signed comparison of the two inputs and produces -1 (true)
or 0 (false).</p>"
  (if (and (2vec-p x) (2vec-p y))
      (2vec (bool->vec (< (2vec->val x) (2vec->val y))))
    (4vec-x)))

(define 3vec-== ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Arithmetic equality of two 4vecs"
  :long "<p>Shorthand for (uand (bitnot (bitxor x y))).</p>"
  (3vec-reduction-and (3vec-bitnot (3vec-bitxor x y))))

(define 4vec-== ((x 4vec-p) (y 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
  :short "Arithmetic equality of two 4vecs"
  :long "<p>Shorthand for (uand (bitnot (bitxor x y))).</p>"
  (3vec-== (3vec-fix x) (3vec-fix y)))

(define 3vec-? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
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
  :parents (4vec-functions)
  :short "If-then-else of 4vecs"
  :long "<p>If @('x') has any 1-bits, returns @('y'); if @('x') is 0, returns
@('z'); otherwise returns a result consisting of Xes in bit positions where
@('y') and @('z') are unequal and their bits in the positions where they are
equal.</p>"
  (3vec-? (3vec-fix x) y z))

(define 3vec-bit? ((x 4vec-p) (y 4vec-p) (z 4vec-p))
  :returns (res 4vec-p)
  :parents (4vec-functions)
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
  :parents (4vec-functions)
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
  :parents (4vec-functions)
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
                           acl2::logior-equal-0
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

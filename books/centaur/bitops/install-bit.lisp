; Centaur Bitops Library
; Copyright (C) 2010-2015 Centaur Technology
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


; install-bit.lisp
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "centaur/misc/introduce-var" :dir :system)
(include-book "logbitp-mismatch")
(local (include-book "equal-by-logbitp"))
(local (include-book "ihsext-basics"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

; BOZO this is very similar to copybit/notbit/etc... also need to figure
; out a better way to deal with these rulesets.

(def-ruleset! ihsext-basic-thms nil)
(def-ruleset! ihsext-advanced-thms nil)
(def-ruleset! ihsext-bad-type-thms nil)
(def-ruleset! ihsext-redefs nil)
(def-ruleset! ihsext-recursive-redefs nil)
(def-ruleset! ihsext-inductions nil)
(def-ruleset! ihsext-bounds-thms nil)
(def-ruleset! ihsext-arithmetic nil)

(defsection install-bit
  :parents (bitops)
  :short "@(call install-bit) sets @('x[n] = val'), where @('x') is an integer,
@('n') is a bit position, and @('val') is a bit."

  (defund install-bit (n val x)
    (declare (xargs :guard (and (natp n)
                                (bitp val)
                                (integerp x))))
    (mbe :logic
         (b* ((x     (ifix x))
              (n     (nfix n))
              (val   (bfix val))
              (place (ash 1 n))
              (mask  (lognot place)))
           (logior (logand x mask)
                   (ash val n)))
         :exec
         (logior (logand x (lognot (ash 1 n)))
                 (ash val n))))

  (local (in-theory (enable install-bit)))

  (defthmd install-bit**
    (equal (install-bit n val x)
           (if (zp n)
               (logcons val (logcdr x))
             (logcons (logcar x)
                      (install-bit (1- n) val (logcdr x)))))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs)))
    :rule-classes
    ((:definition
      :clique (install-bit)
      :controller-alist ((install-bit t nil nil)))))

  (add-to-ruleset ihsext-redefs install-bit**)
  (add-to-ruleset ihsext-recursive-redefs install-bit**)

  (defthm natp-install-bit
    (implies (not (and (integerp x)
                       (< x 0)))
             (natp (install-bit n val x)))
    :rule-classes :type-prescription)

  (defcong nat-equiv equal (install-bit n val x) 1)
  (defcong bit-equiv equal (install-bit n val x) 2)
  (defcong int-equiv equal (install-bit n val x) 3)

  (defthmd logbitp-of-install-bit-split
    ;; Disabled by default since it can cause case splits.
    (equal (logbitp m (install-bit n val x))
           (if (= (nfix m) (nfix n))
               (equal val 1)
             (logbitp m x)))
    :hints(("Goal" :in-theory (enable logbitp-of-ash-split))))

  (add-to-ruleset ihsext-advanced-thms logbitp-of-install-bit-split)
  (add-to-ruleset logbitp-case-splits logbitp-of-install-bit-split)

  (local (in-theory (e/d (logbitp-of-install-bit-split)
                         (install-bit))))

  (defthm logbitp-of-install-bit-same
    (equal (logbitp m (install-bit m val x))
           (equal val 1)))

  (defthm logbitp-of-install-bit-diff
    (implies (not (equal (nfix m) (nfix n)))
             (equal (logbitp m (install-bit n val x))
                    (logbitp m x))))

  (defthm install-bit-of-install-bit-same
    (equal (install-bit a v (install-bit a v2 x))
           (install-bit a v x))
    :hints((equal-by-logbitp-hint)))

  (defthm install-bit-of-install-bit-diff
    (implies (not (equal (nfix a) (nfix b)))
             (equal (install-bit a v (install-bit b v2 x))
                    (install-bit b v2 (install-bit a v x))))
    :rule-classes ((:rewrite :loop-stopper ((a b install-bit))))
    :hints((equal-by-logbitp-hint)))

  (add-to-ruleset ihsext-basic-thms
                  '(logbitp-of-install-bit-same
                    logbitp-of-install-bit-diff
                    install-bit-of-install-bit-same
                    install-bit-of-install-bit-diff))

  (defthm install-bit-when-redundant
    (implies (equal (logbit n x) b)
             (equal (install-bit n b x)
                    (ifix x)))
    :hints((equal-by-logbitp-hint)))

  (encapsulate
    ()
    (local (defthm unsigned-byte-p-of-bit
             (implies (and (bitp i)
                           (posp n))
                      (unsigned-byte-p n i))
             :hints(("Goal" :in-theory (enable bitp)))))

    (local (defthm help1
             (implies (unsigned-byte-p n x)
                      (natp n))))

    (local (in-theory (e/d (install-bit)
                           (unsigned-byte-p))))

    (defthm unsigned-byte-p-of-install-bit
      (implies (and (unsigned-byte-p n x)
                    (< (nfix i) n))
               (unsigned-byte-p n (install-bit i v x)))))

  (defthmd equal-of-install-bit
    (implies (syntaxp (or (acl2::rewriting-positive-literal-fn `(equal (install-bit ,n ,val ,x) ,y) mfc state)
                          (acl2::rewriting-positive-literal-fn `(equal ,y (install-bit ,n ,val ,x)) mfc state)))
             (equal (equal (install-bit n val x) y)
                    (and (integerp y)
                         (let ((arb (nfix (introduce-var 'arbitrary-bit (hide (acl2::logbitp-mismatch (install-bit n val x) y))))))
                           (equal (logbitp arb (install-bit n val x))
                                  (logbitp arb y))))))
    :hints(("Goal"
            :in-theory (e/d (introduce-var
                             logbitp-of-install-bit-split)
                            (acl2::logbitp-mismatch-correct))
            :expand ((:free (x) (hide x)))
            :use ((:instance acl2::logbitp-mismatch-correct
                             (acl2::a (install-bit n val x))
                             (acl2::b y))))))

  (add-to-ruleset ihsext-advanced-thms equal-of-install-bit))


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
(include-book "extra-defs")
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

(add-to-ruleset ihsext-advanced-thms equal-of-install-bit)


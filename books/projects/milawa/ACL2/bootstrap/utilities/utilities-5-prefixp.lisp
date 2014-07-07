; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "utilities-4")
(%interactive)



(%autoadmit prefixp)

(%autoprove prefixp-when-not-consp-one
            (%restrict default prefixp (equal x 'x)))

(%autoprove prefixp-when-not-consp-two
            (%restrict default prefixp (equal x 'x)))

(%autoprove prefixp-of-cons-and-cons
            (%restrict default prefixp (equal x '(cons a x)))
            (%auto :strategy (cleanup split crewrite)))

(%autoprove booleanp-of-prefixp
            (%cdr-cdr-induction x y))

(%autoprove prefixp-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove prefixp-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove same-length-prefixes-equal-cheap
            (%cdr-cdr-induction x y))

(%autoprove prefixp-when-lengths-wrong
            (%cdr-cdr-induction x y))

(defsection prefixp-when-lengths-wrong-replacement
  ;; BOZO see if we still need this?  If so, change the ACL2 rule to
  ;; add a backchain limit.  Else, just use the above autoprove.
  (%prove (%rule prefixp-when-lengths-wrong-replacement
                 :hyps (list (%hyp (< (len y) (len x)) :limit 1))
                 :lhs (prefixp x y)
                 :rhs nil))
  (%auto)
  (%qed)
  (%disable default prefixp-when-lengths-wrong)
  (%enable default prefixp-when-lengths-wrong-replacement))



(%autoadmit prefixp-badguy)

(%autoprove prefixp-badguy-when-not-consp
            (%restrict default prefixp-badguy (equal x 'x)))

(%autoprove prefixp-badguy-of-cons
            (%restrict default prefixp-badguy (equal x '(cons a x)))
            (%auto :strategy (cleanup split crewrite)))

(local (%enable default prefixp-badguy-when-not-consp prefixp-badguy-of-cons))

(%autoprove natp-of-prefixp-badguy
            (%cdr-induction x))

(%autoprove lemma-for-prefixp-badguy-index-property
  (%induct (rank x)
           ((not (consp x))
            nil)
           ((consp x)
            (((x (cdr x))
              (y (cdr y)))))))

(%autoprove lemma-2-for-prefixp-badguy-index-property
  (%induct (rank x)
           ((not (consp x))
            nil)
           ((consp x)
            (((x (cdr x))
              (y (cdr y)))))))

(%autoprove prefixp-badguy-index-property
            (%enable default
                     lemma-for-prefixp-badguy-index-property
                     lemma-2-for-prefixp-badguy-index-property))

(%autoprove forcing-prefixp-when-not-prefixp-badguy
            (%cdr-cdr-induction x y))

(local (%disable default prefixp-badguy-when-not-consp prefixp-badguy-of-cons))



(%autoprove subsetp-when-prefixp-cheap
            (%cdr-cdr-induction x y))


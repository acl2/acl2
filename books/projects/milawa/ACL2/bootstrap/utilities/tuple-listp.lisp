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
(include-book "deflist")
(include-book "strip-firsts")
(include-book "strip-seconds")
(include-book "strip-lens")
(%interactive)


(%deflist true-list-listp (x)
          (true-listp x))



(%deflist tuple-listp (n x)
          (tuplep n x))

(%autoprove rank-of-strip-firsts-when-tuple-listp-2
            (%cdr-induction x))

(%autoprove rank-of-strip-seconds-when-tuple-listp-2
            (%cdr-induction x))

(%autoprove strip-lens-when-tuple-listp
            (%cdr-induction x)
            (%auto)
            (%fertilize (strip-lens x2) (repeat (nfix n) (len x2))))



(%autoadmit list2-list)

(%autoprove list2-list-when-not-consp-one
            (%restrict default list2-list (equal x 'x)))

(%autoprove list2-list-when-not-consp-two
            (%restrict default list2-list (equal x 'x)))

(%autoprove list2-list-of-cons-and-cons
            (%restrict default list2-list (equal x '(cons a x))))

(%autoprove true-listp-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove true-listp-list-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove list2-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove list2-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove len-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove strip-lens-of-list2-list
            (%cdr-cdr-induction x y))


(defsection more-than-two-when-not-zero-one-or-two
  ;; This isn't needed in ACL2.  not sure why we need it.
  ;; BOZO might this have to do with our missing rule?
  (%prove (%rule more-than-two-when-not-zero-one-or-two
                 :hyps (list (%hyp (not (zp n)))
                             (%hyp (not (equal 1 n)))
                             (%hyp (not (equal 2 n))))
                 :lhs (< 2 n)
                 :rhs t))
  (%use (%instance (%thm squeeze-law-one) (b 2) (a n)))
  (%auto)
  (%qed))

(%autoprove tuple-listp-of-list2-list
            (%cdr-cdr-induction x y)
            (%enable default more-than-two-when-not-zero-one-or-two))

(%autoprove forcing-strip-firsts-of-list2-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-strip-seconds-of-list2-list
            (%cdr-cdr-induction x y))

(%ensure-exactly-these-rules-are-missing "../../utilities/tuple-listp")


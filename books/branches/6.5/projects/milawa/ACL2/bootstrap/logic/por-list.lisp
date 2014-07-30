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
(include-book "formulas")
(%interactive)


(defthm forcing-equal-of-logic.por-list-rewrite-alt
  ;; BOZO add this to the acl2 model
  (implies (and (force (equal (len x) (len y)))
                (force (logic.formula-listp x))
                (force (logic.formula-listp y)))
           (equal (equal z (logic.por-list x y))
                  (and (true-listp z)
                       (logic.formula-listp z)
                       (logic.all-disjunctionsp z)
                       (equal (list-fix x) (logic.vlhses z))
                       (equal (list-fix y) (logic.vrhses z))))))


(%autoadmit logic.por-list)

(%autoprove logic.por-list-when-not-consp-one
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove logic.por-list-when-not-consp-two
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove logic.por-list-of-cons-and-cons
            (%restrict default logic.por-list (equal x '(cons a x))))

(%autoprove logic.por-list-under-iff)

(%autoprove logic.por-list-of-list-fix-one
            (%cdr-cdr-induction x y))

(%autoprove logic.por-list-of-list-fix-two
            (%cdr-cdr-induction x y))

(%autoprove true-listp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formulap-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.formula-atblp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove consp-of-logic.por-list)

(%autoprove car-of-logic.por-list
            ;; BOZO elim goes berserk
            (%restrict default logic.por-list (equal x 'x)))

(%autoprove cdr-of-logic.por-list)

(%autoprove len-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.por-list-of-singleton-lhs)



(%deflist logic.all-disjunctionsp (x)
          (equal (logic.fmtype x) 'por*)
          :hintsmap
          ((logic.all-disjunctionsp-of-remove-duplicates
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp)
                             (a x1)
                             (x x2))))
           (logic.all-disjunctionsp-of-subsetp-when-logic.all-disjunctionsp
            (%cdr-induction x)
            (%auto)
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp)
                             (a x1)
                             (x y))))))

(%autoprove logic.fmtype-of-car-when-logic.all-disjunctionsp
            (%enable default equal-of-car-when-logic.all-disjunctionsp))

(%autoprove logic.fmtype-when-memberp-of-logic.all-disjunctionsp
            (%use (%instance (%thm equal-when-memberp-of-logic.all-disjunctionsp))))

(%autoprove logic.fmtype-when-memberp-of-logic.all-disjunctionsp-alt)


(%autoprove forcing-logic.all-disjunctionsp-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.all-disjunctionsp-of-logic.por-list-free)

(%autoprove logic.fmtype-of-nth-when-logic.all-disjunctionsp)




(%defprojection :list (logic.vlhses x)
                :element (logic.vlhs x)
                :nil-preservingp t)

(%autoprove forcing-logic.formula-listp-of-logic.vlhses
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.vlhses
            (%cdr-induction x))

(%autoprove forcing-logic.vlhses-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.vlhses-of-logic.por-list-free)

(%autoprove logic.vlhs-of-car-when-all-equalp-of-logic.vlhses)




(%defprojection :list (logic.vrhses x)
                :element (logic.vrhs x)
                :nil-preservingp t)

(%autoprove forcing-logic.formula-listp-of-logic.vrhses
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.vrhses
            (%cdr-induction x))

(%autoprove forcing-logic.vrhses-of-logic.por-list
            (%cdr-cdr-induction x y))

(%autoprove forcing-logic.vrhses-of-logic.por-list-free)

(%autoprove forcing-equal-of-logic.por-list-rewrite
            (%cdr-cdr-cdr-induction x y z))

(%autoprove forcing-equal-of-logic.por-list-rewrite-alt
            (%use (%instance (%thm forcing-equal-of-logic.por-list-rewrite))))


(%ensure-exactly-these-rules-are-missing "../../logic/por-list")


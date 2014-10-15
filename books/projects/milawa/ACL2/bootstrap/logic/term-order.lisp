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
(include-book "term-order-vars")
(include-book "term-order-fns")
(include-book "term-order-consts")
(%interactive)


(%autoadmit logic.flag-count-term-sizes)

(%autoprove natp-of-car-of-logic.flag-count-term-sizes
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoprove natp-of-cdar-of-logic.flag-count-term-sizes
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoprove natp-of-cddr-of-logic.flag-count-term-sizes
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoprove car-of-logic.flag-count-term-sizes
            (%forcingp nil)
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x))
            (%restrict default logic.flag-count-variable-occurrences (equal x 'x)))

(%autoprove cadr-of-logic.flag-count-term-sizes
            (%forcingp nil)
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x))
            (%restrict default logic.flag-count-function-occurrences (equal x 'x)))

(%autoprove cddr-of-logic.flag-count-term-sizes
            (%forcingp nil)
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x))
            (%restrict default logic.flag-count-constant-sizes (equal x 'x)))

(%autoprove consp-of-logic.flag-count-term-sizes-1
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoprove consp-of-logic.flag-count-term-sizes-2
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoprove consp-of-logic.flag-count-term-sizes-3
            (%autoinduct logic.flag-count-term-sizes)
            (%restrict default logic.flag-count-term-sizes (equal x 'x)))

(%autoadmit logic.count-term-sizes)

(%autoprove definition-of-logic.count-term-sizes
            (%enable default
                     logic.count-term-sizes
                     consp-of-logic.flag-count-term-sizes-1
                     consp-of-logic.flag-count-term-sizes-2
                     consp-of-logic.flag-count-term-sizes-3))

(%autoadmit logic.term-<)

(%autoprove definition-of-logic.term-<
            (%enable default
                     logic.term-<
                     logic.count-term-sizes))

(%autoprove booleanp-of-logic.term-<
            (%enable default definition-of-logic.term-<))

(%autoprove irreflexivity-of-logic.term-<
            (%enable default definition-of-logic.term-<))

(%autoprove antisymmetry-of-logic.term-<
            (%enable default definition-of-logic.term-<))

(%autoprove transitivity-of-logic.term-<
            (%enable default definition-of-logic.term-<))

(%autoprove trichotomy-of-logic.term-<
            (%enable default definition-of-logic.term-<))

(%autoprove transitivity-of-logic.term-<-two
            (%disable default trichotomy-of-logic.term-<)
            (%use (%instance (%thm trichotomy-of-logic.term-<)
                             (x y)
                             (y z))))

(%autoprove forcing-transitivity-of-logic.term-<-three)
(%autoprove forcing-transitivity-of-logic.term-<-four)

(%autoprove forcing-minimality-of-constants-under-logic.term-<
            (%enable default definition-of-logic.term-<)
            (%auto)
            ;; We don't have a :cases hint, but this eqsubst is a sneaky way of
            ;; emulating it.  We replace (logic.constantp y) into this big if
            ;; expression that introduces the cases for y, and then the
            ;; if-lifting/splitting tactic creates new clauses for these cases.
            (%eqsubst (logic.termp y)
                      (logic.constantp y)
                      (if (logic.variablep y)
                          'nil
                        (if (logic.functionp y)
                            'nil
                          (if (logic.lambdap y)
                              'nil
                            't)))))



(%deflist logic.all-terms-largerp (b x)
          (logic.term-< b x))

(%autoprove all-terms-larger-when-all-terms-larger-than-something-bigger
            (%cdr-induction x))

(%autoprove logic.term-<-when-memberp-of-logic.all-terms-largerp-two)

(%autoprove logic.term-<-when-memberp-of-logic.all-terms-largerp-two-alt)

(%autoprove memberp-when-logic.all-terms-larger-cheap
            (%cdr-induction x))


(%autoadmit logic.all-terms-largerp-badguy)

(%autoprove logic.all-terms-largerp-badguy-when-not-consp
            (%restrict default logic.all-terms-largerp-badguy (equal x 'x)))

(%autoprove logic.all-terms-largerp-badguy-of-cons
            (%restrict default logic.all-terms-largerp-badguy (equal x '(cons b x))))

(defsection logic.all-terms-largerp-badguy-membership-property
  ;; BOZO add to autoprove; we need to change this to rule-classes nil since the
  ;; dual :rewrite rules screw up autoprove.
  (%prove (%rule logic.all-terms-largerp-badguy-membership-property
                 :hyps (list (%hyp (logic.all-terms-largerp-badguy a x)))
                 :lhs (and (memberp (logic.all-terms-largerp-badguy a x) x)
                           (not (logic.term-< a (logic.all-terms-largerp-badguy a x))))
                 :rhs t))
  (%cdr-induction x)
  (%auto)
  (%qed))

(%autoprove logic.all-terms-largerp-when-not-logic.all-terms-largerp-badguy
            ;; BOZO do we want to switch this rule to target atl-badguy under iff like
            ;; the subset badguy?
            (%cdr-induction x))


(%ensure-exactly-these-rules-are-missing "../../logic/term-order")


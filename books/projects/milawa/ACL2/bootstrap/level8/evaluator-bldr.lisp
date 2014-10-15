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
(include-book "evaluator")
(%interactive)

(%autoadmit flag-generic-evaluator-bldr)
(%autoadmit generic-evaluator-bldr)
(%autoadmit generic-evaluator-list-bldr)

(%autoprove definition-of-generic-evaluator-bldr
            (%enable default generic-evaluator-bldr generic-evaluator-list-bldr)
            (%restrict default flag-generic-evaluator-bldr (equal x 'x)))

(%autoprove definition-of-generic-evaluator-list-bldr
            (%enable default generic-evaluator-bldr generic-evaluator-list-bldr)
            (%restrict default flag-generic-evaluator-bldr (equal x 'x)))

(%autoprove flag-generic-evaluator-bldr-of-term
            (%enable default generic-evaluator-bldr))

(%autoprove flag-generic-evaluator-bldr-of-list
            (%enable default generic-evaluator-list-bldr))

(%autoprove forcing-len-of-cdr-of-generic-evaluator-list-bldr
            (%cdr-induction x)
            (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x)))



(defthmd lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr
  ;; BOZO called "crock" and local in the other file.
  (implies (submapp (logic.initial-arity-table) atbl)
           (equal (lookup 'if atbl)
                  '(if . 3)))
  :hints(("Goal"
          :in-theory (enable logic.initial-arity-table)
          :use ((:instance equal-of-lookups-when-submapp
                           (x (logic.initial-arity-table))
                           (y atbl)
                           (a 'if))))))

(%autoprove lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr
            (%enable default logic.initial-arity-table)
            (%use (%instance (%thm equal-of-lookups-when-submapp)
                           (x (logic.initial-arity-table))
                           (y atbl)
                           (a 'if))))

(local (%enable default lemma-2-for-forcing-logic.appealp-of-generic-evaluator-bldr))





(encapsulate
 ()
 (local (%max-proof-size 1200000000))
 (%autoprove lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr
             ;; This is a particularly difficult proof because of the complexity
             ;; of the induction scheme and the number of cases involved when we
             ;; open up the functions.  Our approach is not very complicated --
             ;; we basically try to solve as much as we can "on the cheap" by
             ;; only using urewrite and very limited crewriting.  Only after the
             ;; big mess is made do we cheaply
             (%flag-generic-evaluator-induction flag x defs n)
             (%disable default
                       formula-decomposition
                       expensive-term/formula-inference
                       expensive-arithmetic-rules
                       expensive-arithmetic-rules-two
                       expensive-subsetp-rules
                       type-set-like-rules
                       forcing-logic.function-of-logic.function-name-and-logic.function-args
                       forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                       forcing-lookup-of-logic.function-name
                       same-length-prefixes-equal-cheap
                       definitionp-when-memberp-of-definition-listp
                       definition-list-lookup-when-not-consp)
             (%auto :strategy (split urewrite))
             (%forcingp nil)
             (%crewrite default)
             (%restrict default definition-of-generic-evaluator (equal x 'x))
             (%restrict default definition-of-generic-evaluator-bldr (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list (equal x 'x))
             (%restrict default definition-of-generic-evaluator-list-bldr (equal x 'x))
             (%auto :strategy (split urewrite))
             (%crewrite default)
             (%forcingp t)
             (%enable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules)
             (%disable default
                       logic.termp-when-logic.formulap
                       logic.termp-when-invalid-maybe-expensive
                       logic.formulap-when-logic.termp
                       logic.formula-listp-when-definition-listp
                       consp-when-logic.lambdap-cheap
                       consp-when-logic.functionp-cheap
                       consp-of-car-when-none-consp
                       consp-of-car-when-cons-listp
                       logic.substitute-when-malformed-cheap
                       logic.lambdap-when-not-anything-else-maybe-expensive)
             (%cheapen default
                       logic.substitute-when-logic.constantp
                       logic.substitute-when-logic.variablep
                       logic.constantp-when-logic.variablep
                       logic.variablep-when-logic.constantp
                       logic.constantp-when-logic.functionp)
             (%auto :strategy (split cleanup urewrite crewrite elim))))

(%autoprove forcing-logic.appealp-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-generic-evaluator-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'term))))

(%autoprove forcing-consp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.appeal-listp-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-generic-evaluator-list-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-generic-evaluator-bldr)
                             (flag 'list))))

(%autoprove forcing-generic-evaluator-bldr-under-iff
            (%disable default forcing-logic.appealp-of-generic-evaluator-bldr)
            (%use (%instance (%thm forcing-logic.appealp-of-generic-evaluator-bldr))))

(%autoprove forcing-generic-evaluator-list-bldr-under-iff
            (%disable default forcing-consp-of-generic-evaluator-list-bldr)
            (%use (%instance (%thm forcing-consp-of-generic-evaluator-list-bldr))))



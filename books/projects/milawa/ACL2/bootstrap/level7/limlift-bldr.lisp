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
(include-book "limlift")
(include-book "casesplit-bldr")
(%interactive)

(%autoadmit clause.limlift-term1-bldr)

(%autoprove cdr-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x)))


(defthm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
  ;; BOZO it's local
  (implies (logic.termp x)
           (and (logic.appealp (car (clause.limlift-term1-bldr x k)))
                (equal (logic.conclusion (car (clause.limlift-term1-bldr x k)))
                       (logic.pequal x (car (clause.limlift-term1 x k))))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x))
            (%disable default
                      clause.simple-termp-openers
                      clause.lifted-termp-openers
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      same-length-prefixes-equal-cheap
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      logic.termp-when-logic.formulap))

(%autoprove forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-car-of-clause.limlift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr)
                             (flag 'list))))

(%autoprove forcing-logic.proofp-of-car-of-clause.limlift-term1-bldr
            (%autoinduct clause.limlift-term1-bldr x k)
            (%restrict default clause.limlift-term1-bldr (equal x 'x))
            (%restrict default clause.limlift-term1 (equal x 'x))
            (%disable default
                      clause.simple-termp-openers
                      clause.lifted-termp-openers
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      same-length-prefixes-equal-cheap
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      logic.termp-when-logic.formulap))



(%autoadmit clause.limlift-term-bldr)

(defthm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr
  ;; BOZO local in the file.
  (implies (logic.termp x)
           (and (logic.appealp (clause.limlift-term-bldr x k))
                (equal (logic.conclusion (clause.limlift-term-bldr x k))
                       (logic.pequal x (clause.limlift-term x k)))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal x 'x))
            (%restrict default clause.limlift-term-bldr (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.limlift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.limlift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.limlift-term-bldr))))

(%autoprove forcing-logic.proofp-of-clause.limlift-term-bldr
            (%autoinduct clause.limlift-term x k)
            (%restrict default clause.limlift-term (equal x 'x))
            (%restrict default clause.limlift-term-bldr (equal x 'x)))



(%defprojection :list (clause.limlift-term-list-bldr x k)
                :element (clause.limlift-term-bldr x k))

(%autoprove forcing-logic.appeal-listp-of-clause.limlift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-clause.limlift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.proof-listp-of-clause.limlift-term-list-bldr
            (%cdr-induction x))



(%autoadmit clause.limlift-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.limlift-clauses-bldr
            (%autoinduct clause.limlift-clauses-bldr)
            (%restrict default clause.limlift-clauses-bldr (equal x 'x)))


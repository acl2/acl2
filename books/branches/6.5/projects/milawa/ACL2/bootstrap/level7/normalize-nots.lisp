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
(%interactive)

(local (%enable default lemma-split-up-list-of-quoted-nil))


(%autoadmit clause.normalize-nots-term)

(defmacro %clause.normalize-nots-term-induction (x)
  `(%induct (rank ,x)
            ((not (clause.negative-termp ,x))
             nil)
            ((and (clause.negative-termp ,x)
                  (not (clause.negative-termp (clause.negative-term-guts ,x))))
             nil)
            ((and (clause.negative-termp ,x)
                  (clause.negative-termp (clause.negative-term-guts ,x)))
             (((,x (clause.negative-term-guts (clause.negative-term-guts ,x))))))))

(%autoprove forcing-logic.termp-of-clause.normalize-nots-term
            (%clause.normalize-nots-term-induction x)
            (%restrict default clause.normalize-nots-term (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-clause.normalize-nots-term
            (%clause.normalize-nots-term-induction x)
            (%restrict default clause.normalize-nots-term (equal x 'x)))

(%autoprove no-double-negatives-after-clause.normalize-nots-term
            (%clause.normalize-nots-term-induction x)
            (%restrict default clause.normalize-nots-term (equal x 'x)))

(%autoadmit clause.normalize-nots-term-bldr)


(defthmd lemma-1-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr
  ;; BOZO need to unlocalize this in the clean-clauses.lisp
  ;; NOTE -- changing the order of the equality to match term order.
  (implies (not (cdr (cdr x)))
           (equal (equal 2 (len x))
                  (and (consp x)
                       (consp (cdr x))))))

(defthm lemma-2-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr
  ;; BOZO need to unlocalize this in the clean-clauses.lisp
  (implies (logic.termp a)
           (and (logic.appealp (clause.normalize-nots-term-bldr a))
                (equal (logic.conclusion (clause.normalize-nots-term-bldr a))
                       (logic.pequal (logic.function 'iff (list a (clause.normalize-nots-term a)))
                                     ''t))))
  :rule-classes nil)

(%autoprove lemma-1-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr)

(%autoprove lemma-2-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr
            (%clause.normalize-nots-term-induction a)
            (%enable default lemma-1-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr)
            (%disable default
                      aggressive-equal-of-logic.pors
                      aggressive-equal-of-logic.pnots
                      aggressive-equal-of-logic.pequals)
            (%restrict default clause.normalize-nots-term (equal x 'a))
            (%restrict default clause.normalize-nots-term-bldr (equal a 'a))
            (%enable default theorem-not-of-not-under-iff)
            (%disable default
                      forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                      equal-of-booleans-rewrite
                      equal-of-cons-rewrite)
            (%auto :strategy (cleanup split urewrite))
            (%forcingp t)
            (%disable default
                      EQUAL-OF-LOGIC.FUNCTION-REWRITE-ALT
                      EQUAL-OF-LOGIC.FUNCTION-REWRITE
                      equal-of-logic.function-and-logic.function
                      [outside]equal-of-logic.function-and-logic.function)
            (%enable default
                     equal-of-booleans-rewrite
                     equal-of-cons-rewrite)
            (%auto)
            (%enable default
                     equal-of-logic.function-and-logic.function
                     [outside]equal-of-logic.function-and-logic.function
                     EQUAL-OF-LOGIC.FUNCTION-REWRITE-ALT
                     EQUAL-OF-LOGIC.FUNCTION-REWRITE))

(%autoprove forcing-logic.appealp-of-clause.normalize-nots-term-bldr
            (%use (%instance (%thm lemma-2-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.normalize-nots-term-bldr
            (%use (%instance (%thm lemma-2-for-forcing-logic.appealp-of-clause.normalize-nots-term-bldr))))

(%autoprove forcing-logic.proofp-of-clause.normalize-nots-term-bldr
            (%clause.normalize-nots-term-induction a)
            (%restrict default clause.normalize-nots-term (equal x 'a))
            (%restrict default clause.normalize-nots-term-bldr (equal a 'a))
            (%enable default theorem-not-of-not-under-iff))



(%defprojection :list (clause.normalize-nots-term-list x)
                :element (clause.normalize-nots-term x))

(%autoprove forcing-logic.term-listp-of-clause.normalize-nots-term-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.normalize-nots-term-list
            (%cdr-induction x))

(%autoprove clause.double-negative-free-listp-of-clause.normalize-nots-term-list
            (%cdr-induction x))



(%defprojection :list (clause.normalize-nots-term-list-bldr x)
                :element (clause.normalize-nots-term-bldr x))

(%autoprove forcing-logic.appeal-listp-of-clause.normalize-nots-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-clause.normalize-nots-term-list-bldr
            (%cdr-induction x)
            ;; bleh why are we having rlimit loops here?
            (%auto :strategy (cleanup split urewrite elim)))

(%autoprove forcing-logic.proof-listp-of-clause.normalize-nots-term-list-bldr
            (%cdr-induction x)
            ;; bleh why are we having rlimit loops here?
            (%auto :strategy (cleanup split urewrite elim)))



(%defprojection :list (clause.normalize-nots-clauses x)
                :element (clause.normalize-nots-term-list x))

(%autoprove forcing-logic.term-list-listp-of-clause.normalize-nots-clauses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.normalize-nots-clauses
            (%cdr-induction x))

(%autoprove cons-listp-of-clause.normalize-nots-clauses
            (%cdr-induction x))



(%autoadmit clause.normalize-nots-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.normalize-nots-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.normalize-nots-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.normalize-nots-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.normalize-nots-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.normalize-nots-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.normalize-nots-clauses-bldr (equal x 'x)))


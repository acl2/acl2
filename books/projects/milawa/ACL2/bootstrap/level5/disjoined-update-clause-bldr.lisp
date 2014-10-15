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
(include-book "disjoined-update-clause-bldr-support")
(include-book "fuse")
(%interactive)


(%autoadmit clause.aux-disjoined-update-clause-bldr)

(local (%enable default logic.term-formula))

(%autoprove clause.aux-disjoined-update-clause-bldr-under-iff
            (%autoinduct clause.aux-disjoined-update-clause-bldr)
            (%restrict default clause.aux-disjoined-update-clause-bldr (equal todo 'todo)))


(defthm lemma-for-forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr
  ;; BOZO unlocalize/rename in clauses/disjoined-update-clause-bldr
  (implies (and (logic.formulap p)
                (logic.term-listp todo)
                (logic.term-listp done)
                (or (consp todo) (consp done))
                (logic.appealp proof)
                (logic.appeal-listp t-proofs)
                (equal (logic.conclusion proof)
                       (cond ((and (consp done) (consp todo))
                              (logic.por p (logic.por (clause.clause-formula done)
                                                      (clause.clause-formula todo))))
                             ((consp done)
                              (logic.por p (clause.clause-formula done)))
                             (t
                              (logic.por p (clause.clause-formula todo)))))
                (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo))
           (and (logic.appealp (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                (equal (logic.conclusion (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                       (logic.por p (clause.clause-formula (app (rev (logic.=lhses (logic.vrhses (logic.strip-conclusions t-proofs)))) done))))))
  ;;:hints(("Goal"
  ;;        :induct (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))))
  :rule-classes nil
  )

(%autoprove lemma-for-forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr
            (%autoinduct clause.aux-disjoined-update-clause-bldr)
            (%forcingp nil)

            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      unusual-consp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap
                      unusual-subsetp-rules
                      unusual-memberp-rules)

            (%auto :strategy (cleanup split urewrite crewrite))

            (%restrict default clause.aux-disjoined-update-clause-bldr (equal todo 'todo))
            (%enable default expensive-term/formula-inference)

            (%auto :strategy (cleanup split urewrite crewrite))

            (%enable default formula-decomposition)
            (%auto))

(%autoprove forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.aux-disjoined-update-clause-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr))))

(%autoprove forcing-logic.proofp-of-clause.aux-disjoined-update-clause-bldr
            (%autoinduct clause.aux-disjoined-update-clause-bldr)
            (%forcingp nil)

            (%disable default
                      type-set-like-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      unusual-consp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap
                      unusual-subsetp-rules
                      unusual-memberp-rules)

            (%auto :strategy (cleanup split urewrite crewrite))

            (%restrict default clause.aux-disjoined-update-clause-bldr (equal todo 'todo))
            (%enable default expensive-term/formula-inference)

            (%auto :strategy (cleanup split urewrite crewrite))

            (%enable default formula-decomposition)
            (%auto))



;; (%enable default build.disjoined-rev-disjunction)

(%autoadmit clause.disjoined-update-clause-bldr)

(encapsulate
 ()
 (local (%enable default
                 clause.disjoined-update-clause-bldr
                 build.disjoined-rev-disjunction))
 (%autoprove clause.disjoined-update-clause-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-clause.disjoined-update-clause-bldr)
 (%autoprove forcing-logic.conclusion-of-clause.disjoined-update-clause-bldr)
 (%autoprove forcing-logic.proofp-of-clause.disjoined-update-clause-bldr))





(defsection clause.disjoined-update-clause-bldr-okp

  (%autoadmit clause.disjoined-update-clause-bldr-okp)

  (%autoprove booleanp-of-clause.disjoined-update-clause-bldr-okp
              (%enable default clause.disjoined-update-clause-bldr-okp))

  (%autoprove clause.disjoined-update-clause-bldr-okp-of-logic.appeal-identity
              (%enable default clause.disjoined-update-clause-bldr-okp))

  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))

  (%autoprove lemma-1-for-soundness-of-clause.disjoined-update-clause-bldr-okp
              (%enable default clause.disjoined-update-clause-bldr-okp))

  (%autoprove lemma-2-for-soundness-of-clause.disjoined-update-clause-bldr-okp
              (%enable default clause.disjoined-update-clause-bldr-okp))

  (%autoprove forcing-soundness-of-clause.disjoined-update-clause-bldr-okp
              (%disable default [OUTSIDE]CONSP-OF-LOGIC.STRIP-CONCLUSIONS) ;; why is this a problem??
              (%enable default
                       lemma-1-for-soundness-of-clause.disjoined-update-clause-bldr-okp
                       lemma-2-for-soundness-of-clause.disjoined-update-clause-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.disjoined-update-clause-bldr
                                   (logic.=rhses
                                    (logic.vrhses
                                     (logic.strip-conclusions
                                      (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                   axioms thms atbl))))
                                   (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                   (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                axioms thms atbl)))))
              (%forcingp nil)
              (%auto :strategy (cleanup split crewrite))
              (%enable default clause.disjoined-update-clause-bldr-okp)
              (%auto)))


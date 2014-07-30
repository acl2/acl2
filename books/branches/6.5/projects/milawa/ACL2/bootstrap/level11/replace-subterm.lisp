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


;; BOZO consider moving all of this to a previous level??
;; Consider making a high-level proof step checker for this stuff??

(%autoadmit build.flag-replace-subterm)
(%autoadmit build.replace-subterm)
(%autoadmit build.replace-subterm-list)

(%autoprove definition-of-build.replace-subterm
            (%enable default
                     build.replace-subterm-list
                     build.replace-subterm)
            (%restrict default build.flag-replace-subterm (or (equal x 'x)
                                                              (equal x 'old))))

(%autoprove definition-of-build.replace-subterm-list
            (%enable default
                     build.replace-subterm-list
                     build.replace-subterm)
            (%restrict default build.flag-replace-subterm (equal x 'x)))

(%autoprove build.flag-replace-subterm-of-term
            (%enable default build.replace-subterm))

(%autoprove build.flag-replace-subterm-of-list
            (%enable default build.replace-subterm-list))

(%autoprove build.replace-subterm-list-when-not-consp
            (%restrict default definition-of-build.replace-subterm-list (equal x 'x)))

(%autoprove build.replace-subterm-list-of-cons
            (%restrict default definition-of-build.replace-subterm-list (equal x '(cons a x))))

(%defprojection
 :list (build.replace-subterm-list x old new proof)
 :element (build.replace-subterm x old new proof))



(defthm lemma-for-forcing-logic.appealp-of-build.replace-subterm
  ;; BOZO unlocalize/rename in build/replace-subterm.lisp
  (if (equal flag 'term)
      (implies (and (logic.termp x)
                    (logic.termp old)
                    (logic.termp new)
                    (logic.appealp proof)
                    (equal (logic.conclusion proof) (logic.pequal old new)))
               (and (logic.appealp (build.replace-subterm x old new proof))
                    (equal (logic.conclusion (build.replace-subterm x old new proof))
                           (logic.pequal x (logic.replace-subterm x old new)))))
    (implies (and (logic.term-listp x)
                  (logic.termp old)
                  (logic.termp new)
                  (logic.appealp proof)
                  (equal (logic.conclusion proof) (logic.pequal old new)))
             (and (logic.appeal-listp (build.replace-subterm-list x old new proof))
                  (equal (logic.strip-conclusions (build.replace-subterm-list x old new proof))
                         (logic.pequal-list x (logic.replace-subterm-list x old new))))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-build.replace-subterm
            (%autoinduct build.flag-replace-subterm flag x old new proof)
            (%auto)
            (%restrict default definition-of-build.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.CONCLUSION PROOF)))))
            (%restrict default definition-of-logic.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.CONCLUSION PROOF))))))

(%autoprove forcing-logic.appealp-of-build.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-build.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.appeal-listp-of-build.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.replace-subterm)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-build.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.replace-subterm)
                             (flag 'list))))

(defthm@ lemma-for-forcing-logic.proofp-of-build.replace-subterm
  ;; BOZO unlocalize/rename in build/replace-subterm
  (if (equal flag 'term)
      (implies (and (logic.termp x)
                    (logic.termp old)
                    (logic.termp new)
                    (logic.appealp proof)
                    (equal (logic.conclusion proof) (logic.pequal old new))
                    ;; ---
                    (logic.term-atblp x atbl)
                    (logic.proofp proof axioms thms atbl)
                    (@obligations build.replace-subterm))
               (logic.proofp (build.replace-subterm x old new proof) axioms thms atbl))
    (implies (and (logic.term-listp x)
                  (logic.termp old)
                  (logic.termp new)
                  (logic.appealp proof)
                  (equal (logic.conclusion proof) (logic.pequal old new))
                  ;; ---
                  (logic.term-list-atblp x atbl)
                  (logic.proofp proof axioms thms atbl)
                  (@obligations build.replace-subterm-list))
             (logic.proof-listp (build.replace-subterm-list x old new proof) axioms thms atbl)))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.proofp-of-build.replace-subterm
            (%autoinduct build.flag-replace-subterm flag x old new proof)
            (%auto)
            (%restrict default definition-of-build.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.CONCLUSION PROOF)))))
            (%restrict default definition-of-logic.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.CONCLUSION PROOF))))))

(%autoprove forcing-logic.proofp-of-build.replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-build.replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.replace-subterm)
                             (flag 'list))))






(%autoadmit build.flag-disjoined-replace-subterm)
(%autoadmit build.disjoined-replace-subterm)
(%autoadmit build.disjoined-replace-subterm-list)

(%autoprove definition-of-build.disjoined-replace-subterm
            (%enable default
                     build.disjoined-replace-subterm
                     build.disjoined-replace-subterm-list)
            (%restrict default build.flag-disjoined-replace-subterm
                       (or (equal x 'x)
                           (equal x 'old))))

(%autoprove definition-of-build.disjoined-replace-subterm-list
            (%enable default
                     build.disjoined-replace-subterm
                     build.disjoined-replace-subterm-list)
            (%restrict default build.flag-disjoined-replace-subterm (equal x 'x)))

(%autoprove build.flag-disjoined-replace-subterm-of-term
            (%enable default build.disjoined-replace-subterm))

(%autoprove build.flag-disjoined-replace-subterm-of-list
            (%enable default build.disjoined-replace-subterm-list))

(%autoprove build.disjoined-replace-subterm-list-when-not-consp
            (%restrict default definition-of-build.disjoined-replace-subterm-list
                       (equal x 'x)))

(%autoprove build.disjoined-replace-subterm-list-of-cons
            (%restrict default definition-of-build.disjoined-replace-subterm-list
                       (equal x '(cons a x))))

(%defprojection
 :list (build.disjoined-replace-subterm-list x old new proof)
 :element (build.disjoined-replace-subterm x old new proof))



(defthm lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm
  ;; BOZO unlocalize/rename in build.replace-subterm
  (if (equal flag 'term)
      (implies (and (logic.termp x)
                    (logic.termp old)
                    (logic.termp new)
                    (logic.appealp proof)
                    (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                    (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
               (and (logic.appealp (build.disjoined-replace-subterm x old new proof))
                    (equal (logic.conclusion (build.disjoined-replace-subterm x old new proof))
                           (logic.por (logic.vlhs (logic.conclusion proof))
                                      (logic.pequal x (logic.replace-subterm x old new))))))
    (implies (and (logic.term-listp x)
                  (logic.termp old)
                  (logic.termp new)
                  (logic.appealp proof)
                  (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                  (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new)))
             (and (logic.appeal-listp (build.disjoined-replace-subterm-list x old new proof))
                  (equal (logic.strip-conclusions (build.disjoined-replace-subterm-list x old new proof))
                         (logic.por-list (repeat (logic.vlhs (logic.conclusion proof)) (len x))
                                         (logic.pequal-list x (logic.replace-subterm-list x old new)))))))
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm
            (%autoinduct build.flag-disjoined-replace-subterm)
            (%auto)
            (%restrict default definition-of-build.disjoined-replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.VRHS (LOGIC.CONCLUSION PROOF))))))
            (%restrict default definition-of-logic.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.VRHS (LOGIC.CONCLUSION PROOF)))))))

(%autoprove forcing-logic.appealp-of-build.disjoined-replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.conclusion-of-build.disjoined-replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.appeal-listp-of-build.disjoined-replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm)
                             (flag 'list))))

(%autoprove forcing-logic.strip-conclusions-of-build.disjoined-replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-build.disjoined-replace-subterm)
                             (flag 'list))))


(defthm@ lemma-for-forcing-logic.proofp-of-build.disjoined-replace-subterm
  ;; BOZO unlocalize/rename in build/replace-subterm
  (if (equal flag 'term)
      (implies (and (logic.termp x)
                    (logic.termp old)
                    (logic.termp new)
                    (logic.appealp proof)
                    (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                    (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                    ;; ---
                    (logic.term-atblp x atbl)
                    (logic.proofp proof axioms thms atbl)
                    (@obligations build.disjoined-replace-subterm))
               (logic.proofp (build.disjoined-replace-subterm x old new proof) axioms thms atbl))
    (implies (and (logic.term-listp x)
                  (logic.termp old)
                  (logic.termp new)
                  (logic.appealp proof)
                  (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                  (equal (logic.vrhs (logic.conclusion proof)) (logic.pequal old new))
                  ;; ---
                  (logic.term-list-atblp x atbl)
                  (logic.proofp proof axioms thms atbl)
                  (@obligations build.disjoined-replace-subterm-list))
             (logic.proof-listp (build.disjoined-replace-subterm-list x old new proof) axioms thms atbl)))
  :rule-classes nil)


(%autoprove lemma-for-forcing-logic.proofp-of-build.disjoined-replace-subterm
            (%autoinduct build.flag-disjoined-replace-subterm)
            (%auto)
            (%restrict default definition-of-build.disjoined-replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.VRHS (LOGIC.CONCLUSION PROOF))))))
            (%restrict default definition-of-logic.replace-subterm
                       (or (equal x 'x)
                           (equal x 'old)
                           (equal x '(LOGIC.=LHS (LOGIC.VRHS (LOGIC.CONCLUSION PROOF)))))))

(%autoprove forcing-logic.proofp-of-build.disjoined-replace-subterm
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.disjoined-replace-subterm)
                             (flag 'term))))

(%autoprove forcing-logic.proof-listp-of-build.disjoined-replace-subterm-list
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-build.disjoined-replace-subterm)
                             (flag 'list))))

(%ensure-exactly-these-rules-are-missing "../../build/replace-subterm")
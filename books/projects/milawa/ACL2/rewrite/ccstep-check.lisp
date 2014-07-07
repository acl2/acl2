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
(include-book "ccsteps")
(include-book "ccstep-arities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defthm forcing-rw.hypbox-listp-of-rw.ccstep-list-hypboxes
  (implies (force (rw.ccstep-listp x))
           (equal (rw.hypbox-listp (rw.ccstep-list-hypboxes x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-listp-of-rw.ccstep-list-terms
  (implies (force (rw.ccstep-listp x))
           (equal (logic.term-listp (rw.ccstep-list-terms x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.trace-listp-of-rw.ccstep-list-gather-traces
  (implies (force (rw.ccstep-listp x))
           (equal (rw.trace-listp (rw.ccstep-list-gather-traces x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.eqtrace-listp-of-rw.ccstep-list-gather-contradictions
   (implies (force (rw.ccstep-listp x))
            (equal (rw.eqtrace-listp (rw.ccstep-list-gather-contradictions x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formulap-of-rw.ccstep-list->original-goal
  (implies (force (and (rw.ccstep-listp x)
                       (consp x)))
           (equal (logic.formulap (rw.ccstep-list->original-goal x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list->original-goal rw.ccstep->original-goal))))

(defthm logic.provable-listp-of-remove-duplicates-when-logic.provable-listp-free
  (implies (and (equal (remove-duplicates x) free)
                (logic.provable-listp free axioms thms atbl))
           (equal (logic.provable-listp x axioms thms atbl)
                  t)))


(defsection rw.ccstep-list-bldr-okp

  (defund rw.ccstep-list-bldr-okp (x defs thms atbl)
    (declare (xargs :guard (and (logic.appealp x)
                                (definition-listp defs)
                                (logic.formula-listp thms)
                                (logic.arity-tablep atbl))))
    (let ((method     (logic.method x))
          (conclusion (logic.conclusion x))
          (subproofs  (logic.subproofs x))
          (extras     (logic.extras x)))
      (and (equal method 'rw.ccstep-list-bldr)
           ;; extras holds the list of ccsteps
           (consp extras)
           (rw.faster-ccstep-listp extras)
           (rw.ccstep-list->compatiblep extras)
           (equal conclusion (rw.ccstep-list->original-goal extras))
           ;; BOZO we could develop a much more efficient test here.
           (let ((traces         (rw.ccstep-list-gather-traces extras))
                 (forced-goals   (remove-duplicates (rw.ccstep-list-forced-goals extras))))
             (and
              (logic.fast-arities-okp (rw.ccstep-list-arities extras nil) atbl)
              (rw.trace-list-okp traces defs)
              (rw.trace-list-env-okp traces defs thms atbl)
              (if (rw.ccstep->provedp (first extras))
                  (equal (logic.strip-conclusions subproofs) forced-goals)
                (and (consp subproofs)
                     (equal (logic.conclusion (car subproofs)) (rw.ccstep->result-goal (first extras)))
                     (equal (logic.strip-conclusions (cdr subproofs)) forced-goals))))))))

  (defund rw.ccstep-list-bldr-high (x defs proof fproofs)
    (declare (xargs :guard (and (consp x)
                                (rw.ccstep-listp x)
                                (rw.ccstep-list->compatiblep x)
                                (definition-listp defs)
                                (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                                (if (rw.ccstep->provedp (first x))
                                    (not proof)
                                  (and (logic.appealp proof)
                                       (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))))
             (ignore defs))
    (let* ((forced-goals         (rw.ccstep-list-forced-goals x))
           (cleaned-forced-goals (remove-duplicates forced-goals)))
      (ACL2::prog2$
       (if (same-lengthp forced-goals cleaned-forced-goals)
           nil
         (ACL2::cw! ";;; Removing forced duplicates reduced ~x0 goals to ~x1. (ccstep-list)~%"
                    (fast-len forced-goals 0)
                    (fast-len cleaned-forced-goals 0)))
       (logic.appeal 'rw.ccstep-list-bldr
                     (rw.ccstep-list->original-goal x)
                     (if (rw.ccstep->provedp (first x))
                         (logic.find-proofs cleaned-forced-goals fproofs)
                       (cons proof (logic.find-proofs cleaned-forced-goals fproofs)))
                     x))))

  (defthmd rw.ccstep-list-bldr-okp-of-rw.ccstep-list-bldr-high
    ;; we don't really need this, but it makes us sure everything's okay.
    (implies (and (consp x)
                  (rw.ccstep-listp x)
                  (rw.ccstep-list->compatiblep x)
                  (definition-listp defs)
                  (rw.trace-list-okp (rw.ccstep-list-gather-traces x) defs)
                  (if (rw.ccstep->provedp (first x))
                      (not proof)
                    (and (logic.appealp proof)
                         (equal (logic.conclusion proof) (rw.ccstep->result-goal (first x)))))
                  (logic.appeal-listp fproofs)
                  (subsetp (rw.ccstep-list-forced-goals x) (logic.strip-conclusions fproofs))
                  ;; ---
                  (mapp atbl)
                  (logic.term-list-atblp (rw.ccstep-list-terms x) atbl)
                  (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl)
                  (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions x) atbl)
                  (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl)
                  (rw.trace-list-env-okp (rw.ccstep-list-gather-traces x) defs thms atbl)
                  )
             (equal (rw.ccstep-list-bldr-okp (rw.ccstep-list-bldr-high x defs proof fproofs)
                                             defs thms atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.ccstep-list-bldr-okp
                                      rw.ccstep-list-bldr-high))))

  (local (in-theory (enable rw.ccstep-list-bldr-okp)))

  (defthm booleanp-of-rw.ccstep-list-bldr-okp
    (equal (booleanp (rw.ccstep-list-bldr-okp x defs thms atbl))
           t)
    :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

  (defthm rw.ccstep-list-bldr-okp-of-logic.appeal-identity
    (equal (rw.ccstep-list-bldr-okp (logic.appeal-identity x) defs thms atbl)
           (rw.ccstep-list-bldr-okp x defs thms atbl))
    :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

  (defthmd lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp
    (implies (and (rw.ccstep-list-bldr-okp x defs thms atbl)
                  (logic.appealp x)
                  (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                  (definition-listp defs))
             (equal (logic.conclusion
                     (rw.ccstep-list-bldr (logic.extras x)
                                          defs
                                          (if (rw.ccstep->provedp (first (logic.extras x)))
                                              nil
                                            (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                    axioms thms atbl))
                                          (logic.provable-list-witness (RW.CCSTEP-LIST-FORCED-GOALS (LOGIC.EXTRAS X))
                                                                       axioms thms atbl)))
                    (logic.conclusion x))))

  (defthmd@ lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp
    (implies (and (rw.ccstep-list-bldr-okp x defs thms atbl)
                  (logic.appealp x)
                  (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                  (definition-listp defs)
                  ;; ---
                  (mapp atbl)
                  (logic.formula-list-atblp defs atbl)
                  (subsetp defs axioms)
                  (@obligations rw.ccstep-list-bldr)
                  (equal (cdr (lookup 'not atbl)) 1)
                  (equal (cdr (lookup 'equal atbl)) 2)
                  (equal (cdr (lookup 'iff atbl)) 2)
                  (equal (cdr (lookup 'if atbl)) 3))
             (equal (logic.proofp
                     (rw.ccstep-list-bldr (logic.extras x)
                                          defs
                                          (if (rw.ccstep->provedp (first (logic.extras x)))
                                              nil
                                            (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                    axioms thms atbl))
                                          (logic.provable-list-witness (RW.CCSTEP-LIST-FORCED-GOALS (LOGIC.EXTRAS X))
                                                                       axioms thms atbl))
                     axioms thms atbl)
                    t)))

  (defthm@ forcing-soundness-of-rw.ccstep-list-bldr-okp
    (implies (and (rw.ccstep-list-bldr-okp x defs thms atbl)
                  (force (and (logic.appealp x)
                              (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                              (mapp atbl)
                              (definition-listp defs)
                              (logic.formula-list-atblp defs atbl)
                              (subsetp defs axioms)
                              (@obligations rw.ccstep-list-bldr)
                              (equal (cdr (lookup 'not atbl)) 1)
                              (equal (cdr (lookup 'iff atbl)) 2)
                              (equal (cdr (lookup 'equal atbl)) 2)
                              (equal (cdr (lookup 'if atbl)) 3))))
             (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                    t))
    :hints (("Goal"
             :use ((:instance lemma-1-for-soundness-of-rw.ccstep-list-bldr-okp)
                   (:instance lemma-2-for-soundness-of-rw.ccstep-list-bldr-okp)
                   (:instance forcing-logic.provablep-when-logic.proofp
                              (x (rw.ccstep-list-bldr (logic.extras x)
                                                      defs
                                                      (if (rw.ccstep->provedp (first (logic.extras x)))
                                                          nil
                                                        (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                                                axioms thms atbl))
                                                      (logic.provable-list-witness (RW.CCSTEP-LIST-FORCED-GOALS (LOGIC.EXTRAS X))
                                                                                   axioms thms atbl)))))))))






;; Original check is below.  The new check is much faster.
;;
;; (defund rw.ccstep-list-bldr-okp (x defs thms atbl)
;;     (declare (xargs :guard (and (logic.appealp x)
;;                                 (definition-listp defs)
;;                                 (logic.formula-listp thms)
;;                                 (logic.arity-tablep atbl))))
;;     (let ((method     (logic.method x))
;;           (conclusion (logic.conclusion x))
;;           (subproofs  (logic.subproofs x))
;;           (extras     (logic.extras x)))
;;       (and (equal method 'rw.ccstep-list-bldr)
;;            ;; extras holds the list of ccsteps
;;            (consp extras)
;;            (rw.ccstep-listp extras)
;;            (rw.ccstep-list->compatiblep extras)
;;            (equal conclusion (rw.ccstep-list->original-goal extras))
;;            ;; BOZO we could develop a much more efficient test here.
;;            (let ((terms          (rw.ccstep-list-terms extras))
;;                  (hypboxes       (rw.ccstep-list-hypboxes extras))
;;                  (traces         (rw.ccstep-list-gather-traces extras))
;;                  (contradictions (rw.ccstep-list-gather-contradictions extras))
;;                  (forced-goals   (remove-duplicates (rw.ccstep-list-forced-goals extras))))
;;              ;; Efficient arity check:
;;              ;; This replaces
;;              ;;    (and (logic.term-list-atblp terms atbl)
;;              ;;         (rw.hypbox-list-atblp hypboxes atbl)
;;              ;;         (rw.eqtrace-list-atblp contradictions atbl)
;;              ;;         (rw.fast-trace-list-atblp traces atbl))
;;              (and
;;               (let* ((acc (logic.term-list-arities terms nil))
;;                      (acc (rw.hypbox-list-arities hypboxes acc))
;;                      (acc (rw.eqtrace-list-arities contradictions acc))
;;                      (acc (rw.trace-list-arities traces acc)))
;;                 (logic.fast-arities-okp acc atbl))
;;               (rw.trace-list-okp traces defs)
;;               (rw.trace-list-env-okp traces defs thms atbl)
;;               (if (rw.ccstep->provedp (first extras))
;;                   (equal (logic.strip-conclusions subproofs) forced-goals)
;;                 (and (consp subproofs)
;;                      (equal (logic.conclusion (car subproofs)) (rw.ccstep->result-goal (first extras)))
;;                      (equal (logic.strip-conclusions (cdr subproofs)) forced-goals))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "trace-okp")
(include-book "urewrite-if-lemmas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(local (in-theory (enable rw.trace-conclusion-formula rw.trace-formula)))


(defund rw.compile-urewrite-if-specialcase-same-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-if-specialcase-same-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((lhs (rw.trace->lhs x))   ;; (if a b c)
         (a   (first (logic.function-args lhs)))
         ;; This is sort of goofy.  Basically, our builder function is set up to handle assumptions
         ;; for the conditional rewriter.  But we don't use assumptions, so we need to fake having an
         ;; assumption about the condition.
         (test-proof (build.iff-reflexivity a))
         (then-proof (build.expansion (logic.pnot (logic.pequal (logic.function 'not (list a)) ''nil))
                                      (first proofs)))
         (else-proof (build.expansion (logic.pnot (logic.pequal a ''nil))
                                      (second proofs))))
    (if (rw.trace->iffp x)
        (rw.iff-of-if-x-y-y-bldr test-proof then-proof else-proof)
      (rw.equal-of-if-x-y-y-bldr test-proof then-proof else-proof))))

(defobligations rw.compile-urewrite-if-specialcase-same-trace
  (build.iff-reflexivity
   build.expansion
   rw.iff-of-if-x-y-y-bldr
   rw.equal-of-if-x-y-y-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-specialcase-same-tracep rw.compile-urewrite-if-specialcase-same-trace)))

 (verify-guards rw.compile-urewrite-if-specialcase-same-trace)

 (defthm rw.compile-urewrite-if-specialcase-same-trace-under-iff
   (iff (rw.compile-urewrite-if-specialcase-same-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-urewrite-if-specialcase-same-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-urewrite-if-specialcase-same-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-urewrite-if-specialcase-same-trace
   (implies (force (and (rw.urewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-urewrite-if-specialcase-same-trace)))
            (equal (logic.proofp (rw.compile-urewrite-if-specialcase-same-trace x proofs) axioms thms atbl)
                   t))))




(defund rw.compile-urewrite-if-generalcase-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-if-generalcase-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((rhs        (rw.trace->rhs x))  ;; (if a2 b2 c2)
         (a2         (first (logic.function-args rhs)))
         (test-proof (first proofs))
         (then-proof (build.expansion (logic.pnot (logic.pequal (logic.function 'not (list a2)) ''nil))
                                      (second proofs)))
         (else-proof (build.expansion (logic.pnot (logic.pequal a2 ''nil))
                                      (third proofs))))
    (if (rw.trace->iffp x)
        (rw.iff-implies-iff-if-bldr test-proof then-proof else-proof)
      (rw.iff-implies-equal-if-bldr test-proof then-proof else-proof))))

(defobligations rw.compile-urewrite-if-generalcase-trace
  (build.expansion
   rw.iff-implies-iff-if-bldr
   rw.iff-implies-equal-if-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-generalcase-tracep rw.compile-urewrite-if-generalcase-trace)))

 (verify-guards rw.compile-urewrite-if-generalcase-trace)

 (defthm rw.compile-urewrite-if-generalcase-trace-under-iff
   (iff (rw.compile-urewrite-if-generalcase-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-urewrite-if-generalcase-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-urewrite-if-generalcase-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-urewrite-if-generalcase-trace
   (implies (force (and (rw.urewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.compile-urewrite-if-generalcase-trace)))
            (equal (logic.proofp (rw.compile-urewrite-if-generalcase-trace x proofs) axioms thms atbl)
                   t))))



(defund@ rw.compile-urewrite-rule-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-rule-tracep x))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (extras (rw.trace->extras x))
         (rule   (first extras))
         (sigma  (second extras)))
    (let ((main-proof
           (cond ((and iffp (equal (rw.rule->equiv rule) 'equal))
                  ;; The rule uses equal, but we just want iff.
                  (@derive ((!= (equal rule-lhs rule-rhs) nil)  (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (equal rule-lhs rule-rhs) t)     (build.equal-t-from-not-nil @-))
                           ((= (equal lhs rhs) t)               (build.instantiation @- sigma))
                           ((= (iff lhs rhs) t)                 (build.iff-from-equal @-))))
                 (iffp
                  ;; The rule uses iff and we want iff.
                  (@derive ((!= (iff rule-lhs rule-rhs) nil)    (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (iff rule-lhs rule-rhs) t)       (build.iff-t-from-not-nil @-))
                           ((= (iff lhs rhs) t)                 (build.instantiation @- sigma))))
                 (t
                  ;; The rule uses equal and we want equal.
                  (@derive ((!= (equal rule-lhs rule-rhs) nil)  (build.theorem (clause.clause-formula (rw.rule-clause rule))))
                           ((= (equal rule-lhs rule-rhs) t)     (build.equal-t-from-not-nil @-))
                           ((= (equal lhs rhs) t)               (build.instantiation @- sigma)))))))
      (if (and (not (rw.hypbox->left hypbox))
               (not (rw.hypbox->right hypbox)))
          main-proof
        (build.expansion (rw.hypbox-formula hypbox) main-proof)))))

(defobligations rw.compile-urewrite-rule-trace
  (build.expansion
   build.instantiation
   build.iff-from-equal
   build.equal-t-from-not-nil
   build.iff-t-from-not-nil))

(encapsulate
 ()
 (local (in-theory (enable logic.term-formula
                           rw.rule-env-okp
                           rw.urewrite-rule-tracep
                           rw.urewrite-rule-trace-env-okp
                           rw.compile-urewrite-rule-trace)))

 (verify-guards rw.compile-urewrite-rule-trace)

 (defthm rw.compile-urewrite-rule-trace-under-iff
   (iff (rw.compile-urewrite-rule-trace x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-logic.appealp-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-tracep x)
                        (rw.tracep x)))
            (equal (logic.appealp (rw.compile-urewrite-rule-trace x))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-tracep x)
                        (rw.tracep x)))
            (equal (logic.conclusion (rw.compile-urewrite-rule-trace x))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-urewrite-rule-trace
   (implies (force (and (rw.urewrite-rule-trace-env-okp x thms atbl)
                        (rw.urewrite-rule-tracep x)
                        (rw.tracep x)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-urewrite-rule-trace)))
            (equal (logic.proofp (rw.compile-urewrite-rule-trace x) axioms thms atbl)
                   t))))


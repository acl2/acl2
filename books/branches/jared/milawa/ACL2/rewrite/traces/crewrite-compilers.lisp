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
(include-book "../prop")
(include-book "trace-okp")
(include-book "urewrite-if-lemmas")
(include-book "crewrite-if-lemmas")
(include-book "crewrite-if-lemmas2")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(local (in-theory (enable rw.trace-conclusion-formula rw.trace-formula)))

(defund rw.compile-crewrite-if-specialcase-same-trace-iff (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.trace->iffp x)
                              (rw.crewrite-if-specialcase-same-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (left   (rw.hypbox->left hypbox))
         (right  (rw.hypbox->right hypbox)))
    (cond ((and left right)
           ;; Proof1 is (L v R) v (iff a1 a2) = t
           ;; Proof2 is (( (not a2) != nil v L) v R) v (equiv b d) = t
           ;; Proof3 is ((    a2 != nil    v L) v R) v (equiv c d) = t
           (let ((proof2* (rw.crewrite-twiddle2-bldr (second proofs))) ;; (L v R) v (not a2) != nil (equiv b d) = t
                 (proof3* (rw.crewrite-twiddle2-bldr (third proofs)))) ;; (L v R) v a2 != nil v (equiv b d) = t
             (rw.disjoined-iff-of-if-x-y-y-bldr (first proofs) proof2* proof3*)))
          ((or left right)
           ;; Proof1 is L/R v (iff a1 a2) = t
           ;; Proof2 is ( (not a2) != nil v L/R ) v (equiv b d) = t
           ;; Proof3 is (    a2 != nil    v L/R ) v (equiv c d) = t
           (let ((proof2* (rw.crewrite-twiddle-bldr (second proofs))) ;; L/R v (not a2) != nil v (equiv b d) = t
                 (proof3* (rw.crewrite-twiddle-bldr (third proofs)))) ;; L/R v a2 != nil v (equiv c d) = t
             (rw.disjoined-iff-of-if-x-y-y-bldr (first proofs) proof2* proof3*)))
          (t
           ;; Proof1 is (iff a1 a2) = t
           ;; Proof2 is (not a2) != nil v (equiv b d) = t
           ;; Proof3 is a2 != nil v (equiv c d) = t
           (rw.iff-of-if-x-y-y-bldr (first proofs) (second proofs) (third proofs))))))

(defund rw.compile-crewrite-if-specialcase-same-trace-equal (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (not (rw.trace->iffp x))
                              (rw.crewrite-if-specialcase-same-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (left   (rw.hypbox->left hypbox))
         (right  (rw.hypbox->right hypbox)))
    (cond ((and left right)
           (let ((proof2* (rw.crewrite-twiddle2-bldr (second proofs)))
                 (proof3* (rw.crewrite-twiddle2-bldr (third proofs))))
             (rw.disjoined-equal-of-if-x-y-y-bldr (first proofs) proof2* proof3*)))
          ((or left right)
           (let ((proof2* (rw.crewrite-twiddle-bldr (second proofs)))
                 (proof3* (rw.crewrite-twiddle-bldr (third proofs))))
             (rw.disjoined-equal-of-if-x-y-y-bldr (first proofs) proof2* proof3*)))
          (t
           (rw.equal-of-if-x-y-y-bldr (first proofs) (second proofs) (third proofs))))))


(defund rw.compile-crewrite-if-specialcase-same-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.crewrite-if-specialcase-same-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (if (rw.trace->iffp x)
      (rw.compile-crewrite-if-specialcase-same-trace-iff x proofs)
    (rw.compile-crewrite-if-specialcase-same-trace-equal x proofs)))

(defobligations rw.compile-crewrite-if-specialcase-same-trace-iff
  (rw.crewrite-twiddle-bldr
   rw.crewrite-twiddle2-bldr
   rw.iff-of-if-x-y-y-bldr
   rw.disjoined-iff-of-if-x-y-y-bldr))

(defobligations rw.compile-crewrite-if-specialcase-same-trace-equal
  (rw.crewrite-twiddle-bldr
   rw.crewrite-twiddle2-bldr
   rw.equal-of-if-x-y-y-bldr
   rw.disjoined-equal-of-if-x-y-y-bldr))

(defobligations rw.compile-crewrite-if-specialcase-same-trace
  (rw.compile-crewrite-if-specialcase-same-trace-iff
   rw.compile-crewrite-if-specialcase-same-trace-equal))



(defthmd lemma-1-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (consp proofs)
                  t)))

(defthmd lemma-2-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (consp (cdr proofs))
                  t))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-3-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (consp (cdr (cdr proofs)))
                  t))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-4-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (logic.conclusion (first proofs))
                  (rw.trace-formula (first (rw.trace->subtraces x)))))
  :hints(("Goal" :in-theory (disable rw.trace-formula))))

(defthmd lemma-5-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (logic.conclusion (second proofs))
                  (rw.trace-formula (second (rw.trace->subtraces x)))))
  :hints(("Goal" :in-theory (disable rw.trace-formula))))

(defthmd lemma-6-for-rw.compile-crewrite-if-specialcase-same-trace
  (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                (equal (len (rw.trace->subtraces x)) 3))
           (equal (logic.conclusion (third proofs))
                  (rw.trace-formula (third (rw.trace->subtraces x)))))
  :hints(("Goal" :in-theory (disable rw.trace-formula))))

(defthmd lemma-7-for-rw.compile-crewrite-if-specialcase-same-trace
  (equal (equal (len (logic.function-args x)) 1)
         (and (consp (logic.function-args x))
              (not (consp (cdr (logic.function-args x))))))
  :hints(("Goal" :expand (len (logic.function-args x)))))

(local (in-theory (enable
                   lemma-1-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-2-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-3-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-4-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-5-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-6-for-rw.compile-crewrite-if-specialcase-same-trace
                   lemma-7-for-rw.compile-crewrite-if-specialcase-same-trace)))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-if-specialcase-same-tracep
                           rw.compile-crewrite-if-specialcase-same-trace-iff
                           logic.term-formula
                           rw.assms-formula
                           rw.hypbox-formula
                           rw.assms-emptyp)))

 (verify-guards rw.compile-crewrite-if-specialcase-same-trace-iff)

 (defthm rw.compile-crewrite-if-specialcase-same-trace-iff-under-iff
   (iff (rw.compile-crewrite-if-specialcase-same-trace-iff x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-iff
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (rw.trace->iffp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-crewrite-if-specialcase-same-trace-iff x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace-iff
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (rw.trace->iffp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-crewrite-if-specialcase-same-trace-iff x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace-iff
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (rw.trace->iffp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.compile-crewrite-if-specialcase-same-trace-iff)))
            (equal (logic.proofp (rw.compile-crewrite-if-specialcase-same-trace-iff x proofs) axioms thms atbl)
                   t))))



(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-if-specialcase-same-tracep
                           rw.compile-crewrite-if-specialcase-same-trace-equal
                           logic.term-formula
                           rw.assms-formula
                           rw.hypbox-formula
                           rw.assms-emptyp)))

 (verify-guards rw.compile-crewrite-if-specialcase-same-trace-equal)

 (defthm rw.compile-crewrite-if-specialcase-same-trace-equal-under-equal
   (iff (rw.compile-crewrite-if-specialcase-same-trace-equal x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace-equal
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (not (rw.trace->iffp x))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-crewrite-if-specialcase-same-trace-equal x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace-equal
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (not (rw.trace->iffp x))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-crewrite-if-specialcase-same-trace-equal x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace-equal
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (not (rw.trace->iffp x))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.compile-crewrite-if-specialcase-same-trace-equal)))
            (equal (logic.proofp (rw.compile-crewrite-if-specialcase-same-trace-equal x proofs) axioms thms atbl)
                   t))))


(encapsulate
 ()
 (verify-guards rw.compile-crewrite-if-specialcase-same-trace)

 (local (in-theory (enable rw.compile-crewrite-if-specialcase-same-trace)))

 (defthm rw.compile-crewrite-if-specialcase-same-trace-under-equal
   (iff (rw.compile-crewrite-if-specialcase-same-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-crewrite-if-specialcase-same-trace
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-crewrite-if-specialcase-same-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-crewrite-if-specialcase-same-trace
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-crewrite-if-specialcase-same-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-crewrite-if-specialcase-same-trace
   (implies (force (and (rw.crewrite-if-specialcase-same-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.compile-crewrite-if-specialcase-same-trace)))
            (equal (logic.proofp (rw.compile-crewrite-if-specialcase-same-trace x proofs) axioms thms atbl)
                   t))))






(defund rw.compile-crewrite-if-generalcase-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.crewrite-if-generalcase-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (left   (rw.hypbox->left hypbox))
         (right  (rw.hypbox->right hypbox)))
    (cond ((and left right)
           ;; Proof1 is (L v R) v (iff a1 a2) = t
           ;; Proof2 is (( (not a2) != nil v L) v R) v (equiv b1 b2) = t
           ;; Proof3 is ((    a2 != nil    v L) v R) v (equiv c1 c2) = t
           (let ((proof2* ;; (L v R) v (not a2) != nil (equiv b1 v2) = t
                  (rw.crewrite-twiddle2-bldr (second proofs)))
                 (proof3* ;; (L v R) v a2 != nil v (equiv c1 c2) = t
                  (rw.crewrite-twiddle2-bldr (third proofs))))
             (if iffp
                 (rw.disjoined-iff-implies-iff-if-bldr (first proofs) proof2* proof3*)
               (rw.disjoined-iff-implies-equal-if-bldr (first proofs) proof2* proof3*))))
          ((or left right)
           ;; Proof1 is L/R v (iff a1 a2) = t
           ;; Proof2 is ( (not a2) != nil v L/R ) v (equiv b1 b2) = t
           ;; Proof3 is (    a2 != nil    v L/R ) v (equiv c1 c2) = t
           (let ((proof2* ;; L/R v (not a2) != nil (equiv b1 v2) = t
                  (rw.crewrite-twiddle-bldr (second proofs)))
                 (proof3* ;; L/R v a2 != nil v (equiv c1 c2) = t
                  (rw.crewrite-twiddle-bldr (third proofs))))
             (if iffp
                 (rw.disjoined-iff-implies-iff-if-bldr (first proofs) proof2* proof3*)
               (rw.disjoined-iff-implies-equal-if-bldr (first proofs) proof2* proof3*))))
           (t
            ;; Proof1 is (iff a1 a2) = t
            ;; Proof2 is (not a2) != nil v (equiv b1 b2) = t
            ;; Proof3 is a2 != nil v (equiv c1 c2) = t
            (if iffp
                (rw.iff-implies-iff-if-bldr (first proofs) (second proofs) (third proofs))
              (rw.iff-implies-equal-if-bldr (first proofs) (second proofs) (third proofs)))))))

(defobligations rw.compile-crewrite-if-generalcase-trace
  (rw.crewrite-twiddle-bldr
   rw.iff-implies-iff-if-bldr
   rw.iff-implies-equal-if-bldr
   rw.disjoined-iff-implies-iff-if-bldr
   rw.disjoined-iff-implies-equal-if-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-if-generalcase-tracep
                           rw.compile-crewrite-if-generalcase-trace
                           logic.term-formula
                           rw.assms-formula
                           rw.hypbox-formula
                           rw.assms-emptyp)))

 (verify-guards rw.compile-crewrite-if-generalcase-trace)

 (defthm rw.compile-crewrite-if-generalcase-trace-under-iff
   (iff (rw.compile-crewrite-if-generalcase-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-crewrite-if-generalcase-trace
   (implies (force (and (rw.crewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-crewrite-if-generalcase-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-crewrite-if-generalcase-trace
   (implies (force (and (rw.crewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-crewrite-if-generalcase-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-crewrite-if-generalcase-trace
   (implies (force (and (rw.crewrite-if-generalcase-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.compile-crewrite-if-generalcase-trace)))
            (equal (logic.proofp (rw.compile-crewrite-if-generalcase-trace x proofs) axioms thms atbl)
                   t))))




(defund@ rw.compile-assumptions-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.assumptions-tracep x))
                  :verify-guards nil))
  (let* ((hypbox     (rw.trace->hypbox x))
         (extras     (rw.trace->extras x))
         (iffp       (rw.trace->iffp x))
         (main-proof (rw.eqtrace-bldr extras hypbox)))
    (if iffp
        (build.disjoined-commute-iff main-proof)
      (build.disjoined-commute-equal main-proof))))

(defobligations rw.compile-assumptions-trace
  (rw.eqtrace-bldr
   build.disjoined-commute-equal
   build.disjoined-commute-iff))

(defthm rw.eqtrace-bldr-under-iff
  ;; BOZO move to assms
  (iff (rw.eqtrace-bldr x box)
       t)
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-bldr))))

(encapsulate
 ()
 (local (in-theory (enable rw.assumptions-tracep
                           rw.compile-assumptions-trace
                           rw.trace-formula
                           rw.eqtrace-formula)))

 (verify-guards rw.compile-assumptions-trace)

 (defthm rw.compile-assumptions-trace-under-iff
   (iff (rw.compile-assumptions-trace x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm forcing-logic.appealp-of-rw.compile-assumptions-trace
   (implies (force (and (rw.tracep x)
                        (rw.assumptions-tracep x)))
            (equal (logic.appealp (rw.compile-assumptions-trace x))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-assumptions-trace
   (implies (force (and (rw.tracep x)
                        (rw.assumptions-tracep x)))
            (equal (logic.conclusion (rw.compile-assumptions-trace x))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-assumptions-trace
   (implies (force (and (rw.tracep x)
                        (rw.assumptions-tracep x)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.compile-assumptions-trace)))
            (equal (logic.proofp (rw.compile-assumptions-trace x) axioms thms atbl)
                   t))))




(defund rw.compile-force-trace (x fproofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.force-tracep x)
                              (logic.appeal-listp fproofs)
                              (memberp (rw.trace-formula x)
                                       (logic.strip-conclusions fproofs)))))
  (logic.appeal-identity
   (logic.find-proof (rw.trace-formula x) fproofs)))

(defthm rw.compile-force-trace-under-iff
  (iff (rw.compile-force-trace x fproofs)
       t)
  :hints(("Goal" :in-theory (enable rw.compile-force-trace))))

(defthm forcing-logic.appealp-of-rw.compile-force-trace
  (implies (force (and (rw.tracep x)
                       (rw.force-tracep x)
                       (logic.appeal-listp fproofs)
                       (memberp (rw.trace-formula x) (logic.strip-conclusions fproofs))))
           (equal (logic.appealp (rw.compile-force-trace x fproofs))
                  t))
  :hints(("Goal" :in-theory (enable rw.compile-force-trace))))

(defthm forcing-logic.conclusion-of-rw.compile-force-trace
  (implies (force (and (rw.tracep x)
                       (rw.force-tracep x)
                       (logic.appeal-listp fproofs)
                       (memberp (rw.trace-formula x) (logic.strip-conclusions fproofs))))
           (equal (logic.conclusion (rw.compile-force-trace x fproofs))
                  (rw.trace-formula x)))
  :hints(("Goal" :in-theory (enable rw.compile-force-trace))))

(defthm forcing-logic.proofp-of-rw.compile-force-trace
  (implies (force (and (rw.tracep x)
                       (rw.force-tracep x)
                       (logic.appeal-listp fproofs)
                       (logic.proof-listp fproofs axioms thms atbl)
                       (memberp (rw.trace-formula x) (logic.strip-conclusions fproofs))))
           (equal (logic.proofp (rw.compile-force-trace x fproofs) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.compile-force-trace))))




(defund rw.compile-weakening-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.weakening-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :guard-hints (("Goal" :in-theory (enable rw.weakening-tracep)))))
  (let ((hypbox (rw.trace->hypbox x)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (logic.appeal-identity (first proofs))
      (build.expansion (rw.hypbox-formula hypbox)
                       (first proofs)))))

(defthm rw.compile-weakening-trace-under-iff
  (iff (rw.compile-weakening-trace x proofs)
       t)
  :hints(("Goal" :in-theory (enable rw.compile-weakening-trace))))

(defthm forcing-logic.appealp-of-rw.compile-weakening-trace
  (implies (force (and (rw.tracep x)
                       (rw.weakening-tracep x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (rw.trace-list-formulas (rw.trace->subtraces x)))))
           (equal (logic.appealp (rw.compile-weakening-trace x proofs))
                  t))
  :hints(("Goal" :in-theory (enable rw.weakening-tracep
                                    rw.compile-weakening-trace))))

(defthm forcing-logic.conclusion-of-rw.compile-weakening-trace
  (implies (force (and (rw.tracep x)
                       (rw.weakening-tracep x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (rw.trace-list-formulas (rw.trace->subtraces x)))))
           (equal (logic.conclusion (rw.compile-weakening-trace x proofs))
                  (rw.trace-formula x)))
  :hints(("Goal" :in-theory (enable rw.weakening-tracep
                                    rw.trace-formula
                                    rw.trace-conclusion-formula
                                    rw.compile-weakening-trace))))

(defthm forcing-logic.proofp-of-rw.compile-weakening-trace
  (implies (force (and (rw.tracep x)
                       (rw.weakening-tracep x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (rw.trace-list-formulas (rw.trace->subtraces x)))
                       (logic.proof-listp proofs axioms thms atbl)
                       (rw.trace-atblp x atbl)))
           (equal (logic.proofp (rw.compile-weakening-trace x proofs) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.weakening-tracep
                                    rw.compile-weakening-trace))))

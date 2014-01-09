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
(include-book "assmsp")
(include-book "contradiction-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO move this stuff to eqdatabasep.

(defthm forcing-rw.eqset-okp-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box))
                (force (rw.eqsetp x)))
           (equal (rw.eqset-okp x box)
                  nil))
  :hints(("Goal" :in-theory (e/d (rw.eqset-okp rw.eqsetp)
                                 ((:e acl2::force))))))

(defthm forcing-rw.eqset-list-okp-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box))
                (force (rw.eqset-listp x)))
           (equal (rw.eqset-list-okp x box)
                  (not (consp x))))
  :hints(("Goal" :in-theory (enable rw.eqset-list-okp))))

(defthm forcing-rw.eqdatabase-okp-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box))
                (force (rw.eqdatabasep eqdatabase)))
           (equal (rw.eqdatabase-okp eqdatabase box)
                  (and (not (consp (rw.eqdatabase->equalsets eqdatabase)))
                       (not (consp (rw.eqdatabase->iffsets eqdatabase)))
                       (not (rw.eqdatabase->contradiction eqdatabase)))))
  :hints(("Goal" :in-theory (enable rw.eqdatabasep
                                    rw.eqdatabase-okp
                                    rw.eqdatabase->equalsets
                                    rw.eqdatabase->contradiction))))

(defthm rw.eqrow-list-lookup-when-not-consp
  (implies (not (consp eqsets))
           (equal (rw.eqset-list-lookup term eqsets)
                  nil))
  :hints(("Goal" :in-theory (enable rw.eqset-list-lookup))))

(defthm forcing-rw.try-equalities-when-empty-box
  (implies (and (not (rw.hypbox->left box))
                (not (rw.hypbox->right box))
                (force (rw.eqdatabasep eqdatabase))
                (force (rw.eqdatabase-okp eqdatabase box)))
           (equal (rw.try-equiv-database term eqdatabase iffp)
                  nil))
  :hints(("Goal" :in-theory (enable rw.try-equiv-database))))






;; USING ASSUMPTIONS.

(definlined rw.try-assms (assms term iffp)
  (declare (xargs :guard (and (rw.assmsp assms)
                              (logic.termp term)
                              (booleanp iffp))))

  ;; When I originally designed this, I was expecting the iff database to always
  ;; be better than the equal database, because of weakening traces, etc.  But now,
  ;; since you can turn on/off various kinds of traces, it might be the case that
  ;; direct/negative traces are both off, in which case we are only building equal
  ;; traces.  Then, I don't want to look in the iff database even if iffp is true,
  ;; because it will be empty.  Instead, look only in the equal database, which is
  ;; sound since we can weaken it afterwards.

  (let* ((iffp (and iffp
                    (let ((ctrl (rw.assms->ctrl assms)))
                      (or (rw.assmctrl->directp ctrl)
                          (rw.assmctrl->negativep ctrl)))))
         (eqtrace (rw.try-equiv-database term (rw.assms->eqdatabase assms) iffp)))
    (and eqtrace
         ;; The trace has the form term' = term, so we want the left hand side.
         (rw.eqtrace->lhs eqtrace))))

(defthm forcing-logic.termp-of-rw.try-assms
  (implies (and (rw.try-assms assms term iffp)
                (force (logic.termp term))
                (force (rw.assmsp assms)))
           (equal (logic.termp (rw.try-assms assms term iffp))
                  t))
  :hints(("Goal" :in-theory (enable rw.try-assms))))

(defthm forcing-logic.term-atblp-of-rw.try-assms
  (implies (and (rw.try-assms assms term iffp)
                (force (logic.term-atblp term atbl))
                (force (rw.assms-atblp assms atbl)))
           (equal (logic.term-atblp (rw.try-assms assms term iffp) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.try-assms))))

(defthm forcing-rw.try-assms-when-empty-hypbox
  (implies (and (not (rw.hypbox->left (rw.assms->hypbox assms)))
                (not (rw.hypbox->right (rw.assms->hypbox assms)))
                (force (rw.assmsp assms)))
           (equal (rw.try-assms assms term iffp)
                  nil))
  :hints(("Goal" :in-theory (enable rw.try-assms
                                    rw.assmsp
                                    rw.assms->eqdatabase
                                    rw.assms->hypbox))))




(defund rw.try-assms-bldr (assms term iffp)
  (declare (xargs :guard (and (rw.assmsp assms)
                              (logic.termp term)
                              (booleanp iffp)
                              (rw.try-assms assms term iffp))
                  :verify-guards nil))
  (let* ((new-iffp (and iffp
                        (let ((ctrl (rw.assms->ctrl assms)))
                          (or (rw.assmctrl->directp ctrl)
                              (rw.assmctrl->negativep ctrl)))))
         (eqtrace (rw.try-equiv-database term (rw.assms->eqdatabase assms) new-iffp)))
    (and eqtrace
         (cond ((and new-iffp iffp)
                ;; Case 1.  We really did look in the iff database, and we wanted
                ;; to find an iff trace there.
                ;; 1. hypbox v (iff term' term) = t         Eqtrace Builder
                ;; 2. hypbox v (iff term term') = t         DJ Commute Equal
                (build.disjoined-commute-iff
                 (rw.eqtrace-bldr eqtrace (rw.assms->hypbox assms))))
               (iffp
                ;; Case 2. We want an iff-trace, but we actually looked in the
                ;; equal database (because iff is disabled in this assms structure).
                ;; Now, get the eqtrace and weaken it.
                ;; 1. hypbox v (equal term' term) = t       Eqtrace Builder
                ;; 2. hypbox v (equal term term') = t       DJ Commute Equal
                ;; 3. hypbox v (iff term term') = t         DJ IFF from Equal
                (build.disjoined-iff-from-equal
                 (build.disjoined-commute-equal
                  (rw.eqtrace-bldr eqtrace (rw.assms->hypbox assms)))))
               (t
                ;; Case 3. We want an equal trace and got one.
                ;; 1. hypbox v (equal term' term) = t       Eqtrace Builder
                ;; 2. hypbox v (equal term term') = t       DJ Commute Equal
                (build.disjoined-commute-equal
                 (rw.eqtrace-bldr eqtrace (rw.assms->hypbox assms))))))))

(defobligations rw.try-assms-bldr
  (rw.eqtrace-bldr
   build.disjoined-commute-iff
   build.disjoined-commute-equal))

(encapsulate
 ()
 (local (in-theory (enable rw.try-assms
                           rw.try-assms-bldr
                           rw.eqtrace-formula)))

 (verify-guards rw.try-assms-bldr)

 (defthm forcing-logic.appealp-of-rw.try-assms-bldr
   (implies (force (and (rw.try-assms assms term iffp)
                        (logic.termp term)
                        (rw.assmsp assms)))
            (equal (logic.appealp (rw.try-assms-bldr assms term iffp))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.try-assms-bldr
   (implies (force (and (rw.try-assms assms term iffp)
                        (logic.termp term)
                        (rw.assmsp assms)))
            (equal (logic.conclusion (rw.try-assms-bldr assms term iffp))
                   (logic.por (rw.hypbox-formula (rw.assms->hypbox assms))
                              (logic.pequal (logic.function (if iffp 'iff 'equal)
                                                            (list term (rw.try-assms assms term iffp)))
                                            ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.try-assms-bldr
   (implies (force (and (rw.try-assms assms term iffp)
                        (logic.termp term)
                        (rw.assmsp assms)
                        ;; ---
                        (rw.assms-atblp assms atbl)
                        (logic.term-atblp term atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.try-assms-bldr)))
            (equal (logic.proofp (rw.try-assms-bldr assms term iffp) axioms thms atbl)
                   t))))


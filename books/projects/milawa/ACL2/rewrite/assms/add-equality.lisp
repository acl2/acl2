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
(include-book "eqdatabasep")
(include-book "try-equiv-database")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defthm forcing-uniquep-of-remove-all
  (implies (force (uniquep x))
           (equal (uniquep (remove-all a x))
                  t)))


(defthmd memberp-when-not-memberp-of-cdr
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (and (consp x)
                       (equal a (car x))))))

(defthm equal-of-rw.eqset->heads-when-uniquep-of-rw.eqset-list-heads
  (implies (and (uniquep (rw.eqset-list-heads eqsets))
                (memberp a eqsets)
                (memberp b eqsets))
           (equal (equal (rw.eqset->head a) (rw.eqset->head b))
                  (equal a b)))
  :hints(("Goal"
          :induct (cdr-induction eqsets)
          :in-theory (enable memberp-when-not-memberp-of-cdr))))



(defthm uniquep-when-mutually-disjointp-and-cons-listp
  ;; BOZO move to mutually-disjoint.lisp
  (implies (and (mutually-disjointp x)
                (cons-listp x))
           (equal (uniquep x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defthm rw.eqset-list-heads-of-remove-all
  (implies (and (memberp a x)
                (uniquep (rw.eqset-list-heads x)))
           (equal (rw.eqset-list-heads (remove-all a x))
                  (remove-all (rw.eqset->head a)
                              (rw.eqset-list-heads x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-rw.eqset-list-rhses-when-memberp
  (implies (memberp a eqsets)
           (memberp (rw.eqtrace-list-rhses (rw.eqset->tail a))
                    (rw.eqset-list-rhses eqsets)))
  :hints(("Goal"
          :in-theory (enable rw.eqset->rhses)
          :induct (cdr-induction eqsets))))

(defthm cons-listp-of-rw.eqset-list-rhses
  (implies (rw.eqset-listp eqsets)
           (equal (cons-listp (rw.eqset-list-rhses eqsets))
                  t))
  :hints(("Goal"
          :in-theory (enable rw.eqset->rhses)
          :induct (cdr-induction eqsets))))

(defthm uniquep-of-rw.eqset-list-rhses-when-mutually-disjointp
  (implies (and (mutually-disjointp (rw.eqset-list-rhses eqsets))
                (force (rw.eqset-listp eqsets)))
           (equal (uniquep (rw.eqset-list-rhses eqsets))
                  t)))





(encapsulate
 ()
 (defthmd lemma-for-rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp
   (implies (memberp a x)
            (equal (equal (rw.eqset-list-rhses (remove-all a x))
                          (rw.eqset-list-rhses x))
                   nil))
   :hints(("Goal" :use ((:instance equal-when-length-different
                                   (a (rw.eqset-list-rhses (remove-all a x)))
                                   (b (rw.eqset-list-rhses x)))))))

 (defthm rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp
   (implies (and (mutually-disjointp (rw.eqset-list-rhses eqsets))
                 (all-equalp (rw.eqset->iffp set) (rw.eqset-list-iffps eqsets))
                 (memberp set eqsets)
                 (rw.eqset-listp eqsets))
            (equal (rw.eqset-list-rhses (remove-all set eqsets))
                   (remove-all (rw.eqset->rhses set) (rw.eqset-list-rhses eqsets))))
   :hints(("Goal"
           :induct (cdr-induction eqsets)
           :in-theory (enable lemma-for-rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp)))))






(defthmd lemma-for-disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses
  (implies (and (memberp a eqsets)
                (memberp b eqsets)
                (mutually-disjointp (rw.eqset-list-rhses eqsets))
                (rw.eqset-listp eqsets))
           (equal (equal (rw.eqtrace-list-rhses (rw.eqset->tail a))
                         (rw.eqtrace-list-rhses (rw.eqset->tail b)))
                  (equal a b)))
  :hints(("Goal"
          :induct (cdr-induction eqsets)
          :in-theory (enable rw.eqset->rhses
                             memberp-when-not-memberp-of-cdr))))

(defthm disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses
  (implies (and (rw.eqset-listp eqsets)
                (mutually-disjointp (rw.eqset-list-rhses eqsets))
                (memberp a eqsets)
                (memberp b eqsets)
                (not (equal a b)))
           (equal (disjointp (rw.eqtrace-list-rhses (rw.eqset->tail a))
                             (rw.eqtrace-list-rhses (rw.eqset->tail b)))
                  t))
  :hints(("Goal" :in-theory (enable lemma-for-disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses))))




(defprojection :list (rw.eqtrace-list-update iffp e x)
               :element (rw.trans1-eqtrace iffp e x)
               :guard (and (booleanp iffp)
                           (rw.eqtracep e)
                           (rw.eqtrace-listp x)
                           (all-equalp (rw.eqtrace->rhs e) (rw.eqtrace-list-lhses x))
                           (implies (not iffp)
                                    (and (not (rw.eqtrace->iffp e))
                                         (all-equalp nil (rw.eqtrace-list-iffps x))))))

(defthm rw.eqtrace-list-iffps-of-rw.eqtrace-list-update
  (equal (rw.eqtrace-list-iffps (rw.eqtrace-list-update iffp e x))
         (repeat iffp (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.eqtrace-list-lhses-of-rw.eqtrace-list-update
  (equal (rw.eqtrace-list-lhses (rw.eqtrace-list-update iffp e x))
         (repeat (rw.eqtrace->lhs e) (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.eqtrace-list-rhses-of-rw.eqtrace-list-update
  (equal (rw.eqtrace-list-rhses (rw.eqtrace-list-update iffp e x))
         (rw.eqtrace-list-rhses x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.eqtrace-listp-of-rw.eqtrace-list-update
  (implies (force (and (booleanp iffp)
                       (rw.eqtracep e)
                       (rw.eqtrace-listp x)
                       (all-equalp (rw.eqtrace->rhs e) (rw.eqtrace-list-lhses x))))
           (equal (rw.eqtrace-listp (rw.eqtrace-list-update iffp e x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.eqtrace-list-atblp-of-rw.eqtrace-list-update
  (implies (force (and (rw.eqtrace-atblp e atbl)
                       (rw.eqtrace-list-atblp x atbl)))
           (equal (rw.eqtrace-list-atblp (rw.eqtrace-list-update iffp e x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.eqtrace-list-okp-of-rw.eqtrace-list-update
  (implies (force (and (rw.eqtrace-okp e box)
                       (rw.eqtrace-list-okp x box)
                       (all-equalp (rw.eqtrace->rhs e) (rw.eqtrace-list-lhses x))
                       (implies (not iffp)
                                (and (not (rw.eqtrace->iffp e))
                                     (all-equalp nil (rw.eqtrace-list-iffps x))))))
           (equal (rw.eqtrace-list-okp (rw.eqtrace-list-update iffp e x) box)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))






(definlined rw.eqset-relevant (term eqset)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqsetp eqset))))
  (or (equal (rw.eqset->head eqset) term)
      (rw.eqset-lookup term eqset)))

(defund rw.find-relevant-eqset (term eqsets)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqset-listp eqsets))))
  (if (consp eqsets)
      (if (rw.eqset-relevant term (car eqsets))
          (car eqsets)
        (rw.find-relevant-eqset term (cdr eqsets)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-relevant-eqset
                           rw.eqset-relevant)))

 (defthm forcing-rw.eqsetp-of-rw.find-relevant-eqset
   (implies (force (and (rw.find-relevant-eqset term eqsets)
                        (rw.eqset-listp eqsets)))
            (equal (rw.eqsetp (rw.find-relevant-eqset term eqsets))
                   t)))

 (defthm forcing-rw.eqset-lookup-of-rw.find-relevant-eqset-under-iff
   (implies (force (and (rw.find-relevant-eqset term eqsets)
                        (not (equal (rw.eqset->head (rw.find-relevant-eqset term eqsets)) term))))
            (iff (rw.eqset-lookup term (rw.find-relevant-eqset term eqsets))
                 t)))

 (defthm forcing-memberp-of-rw.find-relevant-eqset
   (implies (force (rw.eqset-listp eqsets))
            (equal (memberp (rw.find-relevant-eqset term eqsets) eqsets)
                   (if (rw.find-relevant-eqset term eqsets)
                       t
                     nil))))

 (defthm forcing-rw.eqeqset-relevant-of-rw.find-relevant-eqset
   (implies (and (logic.termp term)
                 (rw.eqset-listp eqsets))
            (iff (rw.eqset-relevant term (rw.find-relevant-eqset term eqsets))
                 (rw.find-relevant-eqset term eqsets))))

 (defthm forcing-rw.eqset->iffp-of-rw.find-relevant-eqset-when-all-equalp
   (implies (and (all-equalp iffp (rw.eqset-list-iffps eqsets))
                 (force (rw.find-relevant-eqset term eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (rw.eqset->iffp (rw.find-relevant-eqset term eqsets))
                   iffp)))

 (defthm memberp-of-rw.eqtrace-list-rhses-when-irrelevant
   (implies (and (not (rw.eqset-relevant term eqset))
                 (force (rw.eqsetp eqset)))
            (equal (memberp term (rw.eqtrace-list-rhses (rw.eqset->tail eqset)))
                   nil))
   :hints(("Goal" :in-theory (enable rw.eqset-lookup))))

 (defthm memberp-of-rw.eqtrace-list-rhses-when-irrelevant-from-all
   (implies (and (not (rw.find-relevant-eqset term eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (member-of-nonep term (rw.eqset-list-rhses eqsets))
                   t))
   :hints(("Goal"
           :induct (cdr-induction eqsets)
           :in-theory (enable rw.eqset->rhses))))

 (defthm memberp-of-rw.eqtrace-list-rhses-when-memberp-of-irrelevant-from-all
   (implies (and (not (rw.find-relevant-eqset term eqsets))
                 (memberp eqset eqsets)
                 (force (rw.eqset-listp eqsets)))
            (equal (memberp term (rw.eqtrace-list-rhses (rw.eqset->tail eqset)))
                   nil))
   :hints(("Goal" :induct (cdr-induction eqsets))))

 (defthm equal-to-rw.eqset->head-when-memberp-of-irrelevant-from-all
   (implies (and (not (rw.find-relevant-eqset term eqsets))
                 (memberp eqset eqsets)
                 (force (rw.eqset-listp eqsets)))
            (equal (equal term (rw.eqset->head eqset))
                   nil))
   :hints(("Goal" :induct (cdr-induction eqsets))))

 (defthm memberp-of-rw.eqset-list-heads-when-all-irrelevant
   (implies (and (not (rw.find-relevant-eqset term eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (memberp term (rw.eqset-list-heads eqsets))
                   nil))
   :hints(("Goal" :induct (cdr-induction eqsets))))

 (defthm memberp-of-rw.eqtrace->lhs-in-rw.eqset-list-heads-when-no-relevant-sets
   (implies (and (not (rw.find-relevant-eqset (rw.eqtrace->lhs trace) eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (memberp (rw.eqtrace->lhs trace) (rw.eqset-list-heads eqsets))
                   nil)))

 (defthm rw.eqset->head-of-rw.find-relevant-eqset-when-among-heads
   (implies (and (memberp term (rw.eqset-list-heads eqsets))
                 (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                     (rw.eqset-list-rhses eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (rw.eqset->head (rw.find-relevant-eqset term eqsets))
                   term))
   :hints(("Goal"
           :in-theory (enable rw.eqset-lookup
                              rw.eqset->rhses)
           :induct (cdr-induction eqsets)))))




(definlined rw.join-eqsets (trace lhs-set rhs-set)
  ;; We are given a trace, say lhs equiv rhs, and two distinct eqsets which are
  ;; relevant to lhs and rhs, respectively.  We are to union these eqsets using
  ;; trace as a bridge.
  (declare (xargs :guard (and (rw.eqtracep trace)
                              (rw.eqsetp lhs-set)
                              (rw.eqsetp rhs-set)
                              (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                              (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                              (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                              (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)
                              (not (equal (rw.eqset->head lhs-set)
                                          (rw.eqset->head rhs-set)))
                              (disjointp (rw.eqset->rhses lhs-set)
                                         (rw.eqset->rhses rhs-set)))
                  :verify-guards nil))
  (let* ((lhs      (rw.eqtrace->lhs trace))
         (rhs      (rw.eqtrace->rhs trace))
         (iffp     (rw.eqtrace->iffp trace))
         (lhs*     (rw.eqset->head lhs-set))
         (rhs*     (rw.eqset->head rhs-set)))
    (if (logic.term-< lhs* rhs*)
        (let ((lhs*=rhs* (cond ((and (equal lhs lhs*)
                                     (equal rhs rhs*))
                                trace)
                               ((equal lhs lhs*)
                                (let ((rhs*=rhs (rw.eqset-lookup rhs rhs-set)))
                                  ;;   lhs* = rhs      trace
                                  ;;   rhs* = rhs      rhs*=rhs
                                  ;; ---------------
                                  ;;   lhs* = rhs*
                                  (rw.trans3-eqtrace iffp trace rhs*=rhs)))
                               ((equal rhs rhs*)
                                (let ((lhs*=lhs (rw.eqset-lookup lhs lhs-set)))
                                  ;;   lhs* = lhs      lhs*=lhs
                                  ;;   lhs = rhs*      trace
                                  ;; ---------------
                                  ;;   lhs* = rhs*
                                  (rw.trans1-eqtrace iffp lhs*=lhs trace)))
                               (t
                                (let* ((lhs*=lhs (rw.eqset-lookup lhs lhs-set))
                                       (rhs*=rhs (rw.eqset-lookup rhs rhs-set))
                                       ;;   lhs* = lhs     lhs*=lhs
                                       ;;   lhs = rhs      trace
                                       ;; --------------
                                       ;;   lhs* = rhs
                                       (lhs*=rhs (rw.trans1-eqtrace iffp lhs*=lhs trace)))
                                  ;;   lhs* = rhs     lhs*=rhs
                                  ;;   rhs* = rhs     rhs*=rhs
                                  ;; ---------------
                                  ;;   lhs* = rhs*
                                  (rw.trans3-eqtrace iffp lhs*=rhs rhs*=rhs))))))
          (rw.eqset lhs* iffp
                    (revappend (rw.eqset->tail lhs-set)
                               (rw.eqtrace-list-update iffp lhs*=rhs*
                                                       (rw.eqset->tail rhs-set)))))
      ;; Otherwise, we know rhs* < lhs*.
      ;;
      ;; We can assume rhs != rhs*, since otherwise we have the following
      ;; contradiction:
      ;;    lhs* < lhs < rhs = rhs* < lhs*
      (let ((rhs*=lhs* (if (equal lhs lhs*)
                           (let ((rhs*=rhs (rw.eqset-lookup rhs rhs-set)))
                             ;;   rhs* = rhs      rhs*=rhs
                             ;;   lhs* = rhs      trace
                             ;; ---------------
                             ;;   rhs* = lhs*
                             (rw.trans3-eqtrace iffp rhs*=rhs trace))
                         (let* ((lhs*=lhs (rw.eqset-lookup lhs lhs-set))
                                (rhs*=rhs (rw.eqset-lookup rhs rhs-set))
                                ;;   lhs* = lhs     lhs*=lhs
                                ;;   lhs = rhs      trace
                                ;; --------------
                                ;;   lhs* = rhs
                                (lhs*=rhs (rw.trans1-eqtrace iffp lhs*=lhs trace)))
                           ;;   rhs* = rhs      rhs*=rhs
                           ;;   lhs* = rhs      lhs*=rhs
                           ;; ---------------
                           ;;   rhs* = lhs*
                           (rw.trans3-eqtrace iffp rhs*=rhs lhs*=rhs)))))
        (rw.eqset rhs* iffp
                  (revappend (rw.eqtrace-list-update iffp rhs*=lhs*
                                                     (rw.eqset->tail lhs-set))
                             (rw.eqset->tail rhs-set)))))))

(encapsulate
 ()
 (local (in-theory (enable rw.join-eqsets
                           rw.eqset-relevant
                           rw.eqset->rhses)))

 (local (in-theory (e/d (rw.eqtrace-list-iffps-of-rev
                         rw.eqtrace-list-lhses-of-rev
                         rw.eqtrace-list-rhses-of-rev)
                        (rev-of-rw.eqtrace-list-iffps
                         rev-of-rw.eqtrace-list-lhses
                         rev-of-rw.eqtrace-list-rhses))))

 (encapsulate
  ()
  (local (ACL2::allow-fertilize t))
  (defthmd lemma-for-rw.join-eqsets
    (implies (and (not (equal (rw.eqset->head lhs-set)
                              (rw.eqset->head rhs-set)))
                  (equal (rw.eqset->head rhs-set)
                         (rw.eqtrace->rhs trace))
                  (rw.eqset-lookup (rw.eqtrace->lhs trace) lhs-set)
                  (rw.eqtracep trace)
                  (rw.eqsetp lhs-set)
                  (rw.eqsetp rhs-set))
             (equal (logic.term-< (rw.eqset->head lhs-set)
                                  (rw.eqset->head rhs-set))
                    t))
    :hints(("Goal"
            :in-theory (disable transitivity-of-logic.term-<
                                forcing-transitivity-of-logic.term-<-three)
            :use ((:instance transitivity-of-logic.term-<
                             (x (rw.eqset->head lhs-set))
                             (y (rw.eqtrace->lhs trace))
                             (z (rw.eqtrace->rhs trace))))))))

 (local (in-theory (enable lemma-for-rw.join-eqsets)))

 (verify-guards rw.join-eqsets)

 (defthm forcing-rw.eqsetp-of-rw.join-eqsets
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp lhs-set)
                        (rw.eqsetp rhs-set)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                        (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                        (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)
                        (not (equal (rw.eqset->head lhs-set) (rw.eqset->head rhs-set)))
                        (disjointp (rw.eqset->rhses lhs-set) (rw.eqset->rhses rhs-set))))
            (equal (rw.eqsetp (rw.join-eqsets trace lhs-set rhs-set))
                   t)))

 (defthm forcing-rw.eqset-atblp-of-rw.join-eqsets
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp lhs-set)
                        (rw.eqsetp rhs-set)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                        (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                        (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)
                        (not (equal (rw.eqset->head lhs-set) (rw.eqset->head rhs-set)))
                        (disjointp (rw.eqset->rhses lhs-set) (rw.eqset->rhses rhs-set))
                        ;; ---
                        (rw.eqtrace-atblp trace atbl)
                        (rw.eqset-atblp lhs-set atbl)
                        (rw.eqset-atblp rhs-set atbl)))
            (equal (rw.eqset-atblp (rw.join-eqsets trace lhs-set rhs-set) atbl)
                   t)))

 (defthm forcing-rw.eqset-okp-of-rw.join-eqsets
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp lhs-set)
                        (rw.eqsetp rhs-set)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                        (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                        (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)
                        (not (equal (rw.eqset->head lhs-set) (rw.eqset->head rhs-set)))
                        (disjointp (rw.eqset->rhses lhs-set) (rw.eqset->rhses rhs-set))
                        ;; ---
                        (rw.eqtrace-okp trace box)
                        (rw.eqset-okp lhs-set box)
                        (rw.eqset-okp rhs-set box)))
            (equal (rw.eqset-okp (rw.join-eqsets trace lhs-set rhs-set) box)
                   t)))

 (defthm forcing-rw.eqset->iffp-of-rw.join-eqsets
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp lhs-set)
                        (rw.eqsetp rhs-set)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp lhs-set))
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp rhs-set))
                        (rw.eqset-relevant (rw.eqtrace->lhs trace) lhs-set)
                        (rw.eqset-relevant (rw.eqtrace->rhs trace) rhs-set)
                        (not (equal (rw.eqset->head lhs-set) (rw.eqset->head rhs-set)))
                        (disjointp (rw.eqset->rhses lhs-set) (rw.eqset->rhses rhs-set))))
            (equal (rw.eqset->iffp (rw.join-eqsets trace lhs-set rhs-set))
                   (rw.eqset->iffp lhs-set))))

 (defthm forcing-rw.eqtrace-list-rhses-of-rw.eqset->tail-of-rw.join-eqsets
   (implies (force (and (rw.eqsetp lhs-set)
                        (rw.eqsetp rhs-set)))
            (equal (rw.eqtrace-list-rhses
                    (rw.eqset->tail
                     (rw.join-eqsets trace lhs-set rhs-set)))
                   (app
                    (rw.eqtrace-list-rhses (rev (rw.eqset->tail lhs-set)))
                    (rw.eqtrace-list-rhses (rw.eqset->tail rhs-set))))))

 (defthm forcing-rw.eqset->head-of-rw.join-eqsets
   (implies (force (rw.eqtracep trace))
            (equal (rw.eqset->head (rw.join-eqsets trace lhs-set rhs-set))
                   (if (logic.term-< (rw.eqset->head rhs-set)
                                     (rw.eqset->head lhs-set))
                       (rw.eqset->head rhs-set)
                     (rw.eqset->head lhs-set))))))





(definlined rw.eqset-extend (trace eqset)
  ;; Try to extend an eqset using a new trace.  The eqset is only actually
  ;; extended if the trace is relevant, i.e., if the trace's lhs or rhs occurs
  ;; somewhere in the set.
  (declare (xargs :guard (and (rw.eqtracep trace)
                              (rw.eqsetp eqset)
                              (equal (rw.eqtrace->iffp trace)
                                     (rw.eqset->iffp eqset)))
                  :verify-guards nil))
  (let* ((iffp      (rw.eqtrace->iffp trace))
         (trace-lhs (rw.eqtrace->lhs trace))
         (trace-rhs (rw.eqtrace->rhs trace))
         (set-head  (rw.eqset->head eqset))
         (set-tail  (rw.eqset->tail eqset)))
    (cond ((equal trace-lhs set-head)
           ;; Special case.
           ;;  * The set's head need not change.
           ;;  * The set's tail needs to be extended with trace-rhs exactly
           ;;    when trace-rhs is not already present.
           (if (rw.eqtrace-list-lookup trace-rhs set-tail)
               eqset
             (rw.eqset set-head iffp (cons trace set-tail))))
          ((equal trace-rhs set-head)
           ;; Special case.
           ;;  * The set's head needs to change from trace-rhs to trace-lhs.
           ;;  * All current members of the tail are currently of the form
           ;;    trace-rhs ~ x, and must be updated to trace-lhs ~ x.
           ;;  * The set's tail does not currently include trace-rhs, since
           ;;    trace-rhs is the set-head.  Hence, we need to add trace itself
           ;;    to the tail, to preserve trace-lhs ~ trace-rhs.
           (rw.eqset trace-lhs
                     iffp
                     (cons trace (rw.eqtrace-list-update iffp trace set-tail))))
          (t
           (let ((lhs-lookup (rw.eqtrace-list-lookup trace-lhs set-tail))
                 (rhs-lookup (rw.eqtrace-list-lookup trace-rhs set-tail)))
             (cond ((and lhs-lookup rhs-lookup)
                    ;; Trace-lhs and trace-rhs are already in the set.  There's
                    ;; no new information being added by this trace.
                    eqset)
                   (lhs-lookup
                    ;; Trace-lhs is in the set, but trace-rhs is not.  We need
                    ;; to add rhs to the set.
                    ;;  * The set's head will not change, since head < lhs < rhs
                    ;;    and we are only adding rhs.
                    ;;  * We need to add head ~ rhs to the set's tail.
                    (rw.eqset set-head
                              iffp
                              (cons (rw.trans1-eqtrace iffp lhs-lookup trace)
                                    set-tail)))
                   (rhs-lookup
                    ;; Trace-rhs is in the set, but trace-lhs is not.
                    (if (logic.term-< set-head trace-lhs)
                        ;; Case 1.
                        ;;  * The set's head will not change
                        ;;  * We need to add head ~ lhs to the set's tail.
                        (rw.eqset set-head
                                  iffp
                                  (cons (rw.trans3-eqtrace iffp rhs-lookup trace) set-tail))
                      ;; Case 2.
                      ;; We know that trace-lhs < set-head, since we already ruled
                      ;; out the possibility that they are equal, and we know that
                      ;; set-head is not less than trace-lhs.
                      ;;  * The set's head needs to become trace-lhs
                      ;;  * All the existing traces in the tail are currently of
                      ;;    the from set-head ~ x, and need to be updated to
                      ;;    become trace-lhs ~ x.
                      ;;  * We don't add trace-lhs ~ trace-rhs, because trace-rhs
                      ;;    is already a member of the tail.
                      ;;  * But trace-lhs ~ set-head needs to be added to the tail,
                      ;;    since it is not yet present.
                      (rw.eqset trace-lhs
                                iffp
                                (cons (rw.trans3-eqtrace iffp trace rhs-lookup)
                                      (rw.eqtrace-list-update iffp (rw.trans3-eqtrace iffp trace rhs-lookup) set-tail)))))
                   (t
                    ;; Neither trace-lhs nor trace-rhs are in the set.  The
                    ;; trace is not related to this set, so we won't need to
                    ;; change the set.
                    eqset)))))))

(encapsulate
 ()
 (local (in-theory (enable rw.eqset-extend)))

 (verify-guards rw.eqset-extend)

 (defthm forcing-rw.eqsetp-of-rw.eqset-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp eqset)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp eqset))))
            (equal (rw.eqsetp (rw.eqset-extend trace eqset))
                   t)))

 (defthm forcing-rw.eqset-atblp-of-rw.eqset-extend
   (implies (force (and (rw.eqtrace-atblp trace atbl)
                        (rw.eqsetp eqset)
                        (rw.eqset-atblp eqset atbl)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp eqset))))
            (equal (rw.eqset-atblp (rw.eqset-extend trace eqset) atbl)
                   t)))

 (defthm forcing-rw.eqset-okp-of-rw.eqset-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqtrace-okp trace box)
                        (rw.eqsetp eqset)
                        (rw.eqset-okp eqset box)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp eqset))))
            (equal (rw.eqset-okp (rw.eqset-extend trace eqset) box)
                   t)))

 (defthm forcing-rw.eqset->iffp-of-rw.eqset-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqsetp eqset)
                        (equal (rw.eqtrace->iffp trace) (rw.eqset->iffp eqset))))
            (equal (rw.eqset->iffp (rw.eqset-extend trace eqset))
                   (rw.eqtrace->iffp trace))))

 (defthmd choices-for-rw.eqset->head-of-rw.eqset-extend
   (memberp (rw.eqset->head (rw.eqset-extend trace eqset))
            (list (rw.eqset->head eqset)
                  (rw.eqtrace->lhs trace)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force))))))





(definlined rw.eqsets-extend (trace eqsets)
  ;; Eqsets are a proper, disjoint-set data structure, and trace is a new piece
  ;; of information we want to infer.  We want to create a new list of eqsets
  ;; which incorporates the new inference.
  (declare (xargs :guard (and (rw.eqtracep trace)
                              (rw.eqset-listp eqsets)
                              (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                              (uniquep (rw.eqset-list-heads eqsets))
                              (mutually-disjointp (rw.eqset-list-rhses eqsets))
                              (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                                  (rw.eqset-list-rhses eqsets)))
                  :verify-guards nil))
  (let* ((lhs     (rw.eqtrace->lhs trace))
         (rhs     (rw.eqtrace->rhs trace))
         (iffp    (rw.eqtrace->iffp trace))
         (lhs-set (rw.find-relevant-eqset lhs eqsets))
         (rhs-set (rw.find-relevant-eqset rhs eqsets)))
    (cond ((and (not lhs-set) (not rhs-set))
           ;; Neither term occurs in any existing set, so we want to create
           ;; a new set for these terms.
           (cons (rw.eqset lhs iffp (list trace)) eqsets))
          ((not lhs-set)
           ;; Only the rhs occurs in any set.  Update that set to include the
           ;; lhs.  There is no chance that this merges sets, since only one
           ;; set is relevant to the trace.
           (cons (rw.eqset-extend trace rhs-set)
                 (remove-all rhs-set eqsets)))
          ((not rhs-set)
           ;; Only the lhs occurs in any set. Update the set to include the
           ;; lhs.  As before, there is no chance that we need to merge sets,
           ;; since only one set is relevant.
           (cons (rw.eqset-extend trace lhs-set)
                 (remove-all lhs-set eqsets)))
          ((equal lhs-set rhs-set)
           ;; Both terms already occur in the same set, so we already know
           ;; they are equal.  No updates are necessary.
           eqsets)
          (t
           ;; Otherwise each term occurs in its own set.  This trace must now
           ;; be used to merge the sets.
           (cons (rw.join-eqsets trace lhs-set rhs-set)
                 (remove-all lhs-set
                             (remove-all rhs-set eqsets)))))))


(encapsulate
 ()
 (local (in-theory (enable rw.eqsets-extend)))
 (local (in-theory (enable rw.eqset->rhses)))

 (verify-guards rw.eqsets-extend)

 (defthm forcing-rw.eqset-listp-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))))
            (equal (rw.eqset-listp (rw.eqsets-extend trace eqsets))
                   t)))

 (defthm forcing-rw.eqset-list-atblp-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))
                        ;; ---
                        (rw.eqtrace-atblp trace atbl)
                        (rw.eqset-list-atblp eqsets atbl)))
            (equal (rw.eqset-list-atblp (rw.eqsets-extend trace eqsets) atbl)
                   t)))

 (defthm forcing-rw.eqrow-list-okp-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))
                        ;; ---
                        (rw.eqtrace-okp trace box)
                        (rw.eqset-list-okp eqsets box)))
            (equal (rw.eqset-list-okp (rw.eqsets-extend trace eqsets) box)
                   t)))

 (encapsulate
  ()
  (defthmd lemma-for-forcing-rw.eqset-list-iffps-of-rw.eqsets-extend
    (implies (force (and (rw.eqtracep trace)
                         (rw.eqset-listp eqsets)
                         (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                         (uniquep (rw.eqset-list-heads eqsets))
                         (mutually-disjointp (rw.eqset-list-rhses eqsets))))
             (equal (all-equalp (rw.eqtrace->iffp trace)
                                (rw.eqset-list-iffps (rw.eqsets-extend trace eqsets)))
                    t)))

  (defthm forcing-rw.eqset-list-iffps-of-rw.eqsets-extend
    (implies (force (and (rw.eqtracep trace)
                         (rw.eqset-listp eqsets)
                         (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                         (uniquep (rw.eqset-list-heads eqsets))
                         (mutually-disjointp (rw.eqset-list-rhses eqsets))))
             (equal (rw.eqset-list-iffps (rw.eqsets-extend trace eqsets))
                    (repeat (rw.eqtrace->iffp trace)
                            (len (rw.eqsets-extend trace eqsets)))))
    :hints(("Goal"
            :use ((:instance lemma-for-forcing-rw.eqset-list-iffps-of-rw.eqsets-extend))
            :in-theory (e/d (all-equalp-as-repeat)
                            (rw.eqsets-extend))))))

 (defthm forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))
                        (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                            (rw.eqset-list-rhses eqsets))))
            (equal (uniquep (rw.eqset-list-heads (rw.eqsets-extend trace eqsets)))
                   t))
   :hints(("Subgoal 4"
           :use ((:instance choices-for-rw.eqset->head-of-rw.eqset-extend
                            (trace trace)
                            (eqset (rw.find-relevant-eqset (rw.eqtrace->rhs trace) eqsets)))))
          ("Subgoal 3"
           :use ((:instance choices-for-rw.eqset->head-of-rw.eqset-extend
                            (trace trace)
                            (eqset (rw.find-relevant-eqset (rw.eqtrace->lhs trace) eqsets)))))))

 (defthmd lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
   (implies (and (equal term (rw.eqset->head eqset))
                 (memberp eqset eqsets)
                 (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                     (rw.eqset-list-rhses eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (MEMBER-OF-NONEP term (RW.EQSET-LIST-RHSES EQSETS))
                   t))
   :hints(("Goal" :induct (cdr-induction eqsets))))

 (defthm forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))
                        (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                            (rw.eqset-list-rhses eqsets))))
            (equal (mutually-disjointp (rw.eqset-list-rhses (rw.eqsets-extend trace eqsets)))
                   t))
   :hints(("Goal"
           :in-theory (e/d (rw.eqset-extend
                            rw.eqtrace-list-rhses-of-rev
                            lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend)
                           (rev-of-rw.eqtrace-list-rhses)))))

 (defthm disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
   (implies (force (and (rw.eqtracep trace)
                        (rw.eqset-listp eqsets)
                        (all-equalp (rw.eqtrace->iffp trace) (rw.eqset-list-iffps eqsets))
                        (uniquep (rw.eqset-list-heads eqsets))
                        (mutually-disjointp (rw.eqset-list-rhses eqsets))
                        (disjoint-from-allp (rw.eqset-list-heads eqsets)
                                            (rw.eqset-list-rhses eqsets))))
            (equal (disjoint-from-allp (rw.eqset-list-heads (rw.eqsets-extend trace eqsets))
                                       (rw.eqset-list-rhses (rw.eqsets-extend trace eqsets)))
                   t))
   :hints(("Goal"
           :in-theory (e/d (rw.eqset-extend
                            rw.eqtrace-list-rhses-of-rev
                            lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend)
                           (rev-of-rw.eqtrace-list-rhses))))))






(definlined rw.eqdatabase-extend (nhyp database primaryp secondaryp directp negativep)
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.eqdatabasep database)
                              (booleanp primaryp)
                              (booleanp secondaryp)
                              (booleanp directp)
                              (booleanp negativep))))
  (let ((trace1 (rw.primary-eqtrace primaryp nhyp))
        (trace2 (rw.secondary-eqtrace secondaryp nhyp))
        (trace3 (rw.direct-iff-eqtrace directp nhyp))
        (trace4 (rw.negative-iff-eqtrace negativep nhyp))
        (iffp   (or directp negativep)))
    (if (or trace1 trace2 trace3 trace4)
        (let* ((equalsets        (rw.eqdatabase->equalsets database))
               (iffsets          (rw.eqdatabase->iffsets database))
               (contradiction    (rw.eqdatabase->contradiction database))
               (equalsets-prime  (if trace1 (rw.eqsets-extend trace1 equalsets) equalsets))
               (equalsets-prime  (if trace2 (rw.eqsets-extend trace2 equalsets-prime) equalsets-prime))
               (iffsets-prime    (if (and iffp trace1)
                                     (rw.eqsets-extend (rw.weakening-eqtrace trace1) iffsets)
                                   iffsets))
               (iffsets-prime    (if (and iffp trace2)
                                     (rw.eqsets-extend (rw.weakening-eqtrace trace2) iffsets-prime)
                                   iffsets-prime))
               (iffsets-prime    (if trace3 (rw.eqsets-extend trace3 iffsets-prime) iffsets-prime))
               (iffsets-prime    (if trace4 (rw.eqsets-extend trace4 iffsets-prime) iffsets-prime)))
          (rw.eqdatabase equalsets-prime
                         iffsets-prime
                         (or contradiction
                             (rw.find-contradiction-in-eqset-list equalsets-prime)
                             (rw.find-contradiction-in-eqset-list iffsets-prime))))
      database)))

(encapsulate
 ()
 (local (in-theory (enable rw.eqdatabase-extend)))

 (defthm rw.eqdatabasep-of-rw.eqdatabase-extend
   (implies (force (and (logic.termp nhyp)
                        (rw.eqdatabasep database)))
            (equal (rw.eqdatabasep (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep))
                   t)))

 (defthm rw.eqdatabase-atblp-of-rw.eqdatabase-extend
   (implies (force (and (rw.eqdatabasep database)
                        (rw.eqdatabase-atblp database atbl)
                        (logic.termp nhyp)
                        (logic.term-atblp nhyp atbl)))
            (equal (rw.eqdatabase-atblp (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep) atbl)
                   t)))

 (defthm rw.eqdatabase-okp-of-rw.eqdatabase-extend
   (implies (force (and (logic.termp nhyp)
                        (rw.hypboxp box)
                        (rw.eqdatabasep database)
                        (or (memberp nhyp (rw.hypbox->left box))
                            (memberp nhyp (rw.hypbox->right box)))
                        (rw.eqdatabase-okp database box)))
            (equal (rw.eqdatabase-okp (rw.eqdatabase-extend nhyp database primaryp secondaryp directp negativep) box)
                   t))))




(encapsulate
 ()
 (local (defthm lemma
          (implies (and (equal (rw.primary-eqtrace t nhyp) trace)
                        (memberp nhyp x)
                        (force (logic.term-listp x)))
                   (iff (rw.find-nhyp-for-primary-eqtracep x trace)
                        t))
          :hints(("Goal" :in-theory (enable rw.find-nhyp-for-primary-eqtracep)))))

 (local (defthm lemma2
          (implies (and (subsetp sub sup)
                        (rw.find-nhyp-for-primary-eqtracep sub trace)
                        (force (logic.term-listp sub))
                        (force (logic.term-listp sup)))
                   (iff (rw.find-nhyp-for-primary-eqtracep sup trace)
                        t))
          :hints(("Goal" :use ((:instance lemma
                                          (nhyp (rw.find-nhyp-for-primary-eqtracep sub trace))
                                          (x sup)))))))

 (defthm rw.primary-eqtrace-okp-in-extended-hypbox
   (implies (and (rw.primary-eqtrace-okp trace sub)
                 (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.primary-eqtrace-okp trace sup)
                   t))
   :hints(("Goal" :in-theory (enable rw.primary-eqtrace-okp)))))


(encapsulate
 ()
 (local (defthm lemma
          (implies (and (equal (rw.secondary-eqtrace t nhyp) trace)
                        (memberp nhyp x)
                        (force (logic.term-listp x)))
                   (iff (rw.find-nhyp-for-secondary-eqtracep x trace)
                        t))
          :hints(("Goal" :in-theory (enable rw.find-nhyp-for-secondary-eqtracep)))))

 (local (defthm lemma2
          (implies (and (subsetp sub sup)
                        (rw.find-nhyp-for-secondary-eqtracep sub trace)
                        (force (logic.term-listp sub))
                        (force (logic.term-listp sup)))
                   (iff (rw.find-nhyp-for-secondary-eqtracep sup trace)
                        t))
          :hints(("Goal" :use ((:instance lemma
                                          (nhyp (rw.find-nhyp-for-secondary-eqtracep sub trace))
                                          (x sup)))))))

 (defthm rw.secondary-eqtrace-okp-in-extended-hypbox
   (implies (and (rw.secondary-eqtrace-okp trace sub)
                 (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.secondary-eqtrace-okp trace sup)
                   t))
   :hints(("Goal" :in-theory (enable rw.secondary-eqtrace-okp)))))


(encapsulate
 ()
 (local (defthm lemma
          (implies (and (equal (rw.direct-iff-eqtrace t nhyp) trace)
                        (memberp nhyp x)
                        (force (logic.term-listp x)))
                   (iff (rw.find-nhyp-for-direct-iff-eqtracep x trace)
                        t))
          :hints(("Goal" :in-theory (enable rw.find-nhyp-for-direct-iff-eqtracep)))))

 (local (defthm lemma2
          (implies (and (subsetp sub sup)
                        (rw.find-nhyp-for-direct-iff-eqtracep sub trace)
                        (force (logic.term-listp sub))
                        (force (logic.term-listp sup)))
                   (iff (rw.find-nhyp-for-direct-iff-eqtracep sup trace)
                        t))
          :hints(("Goal" :use ((:instance lemma
                                          (nhyp (rw.find-nhyp-for-direct-iff-eqtracep sub trace))
                                          (x sup)))))))

 (defthm rw.direct-iff-eqtrace-okp-in-extended-hypbox
   (implies (and (rw.direct-iff-eqtrace-okp trace sub)
                 (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.direct-iff-eqtrace-okp trace sup)
                   t))
   :hints(("Goal" :in-theory (enable rw.direct-iff-eqtrace-okp)))))


(encapsulate
 ()
 (local (defthm lemma
          (implies (and (equal (rw.negative-iff-eqtrace t nhyp) trace)
                        (memberp nhyp x)
                        (force (logic.term-listp x)))
                   (iff (rw.find-nhyp-for-negative-iff-eqtracep x trace)
                        t))
          :hints(("Goal" :in-theory (enable rw.find-nhyp-for-negative-iff-eqtracep)))))

 (local (defthm lemma2
          (implies (and (subsetp sub sup)
                        (rw.find-nhyp-for-negative-iff-eqtracep sub trace)
                        (force (logic.term-listp sub))
                        (force (logic.term-listp sup)))
                   (iff (rw.find-nhyp-for-negative-iff-eqtracep sup trace)
                        t))
          :hints(("Goal" :use ((:instance lemma
                                          (nhyp (rw.find-nhyp-for-negative-iff-eqtracep sub trace))
                                          (x sup)))))))

 (defthm rw.negative-iff-eqtrace-okp-in-extended-hypbox
   (implies (and (rw.negative-iff-eqtrace-okp trace sub)
                 (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.negative-iff-eqtrace-okp trace sup)
                   t))
   :hints(("Goal" :in-theory (enable rw.negative-iff-eqtrace-okp)))))


(encapsulate
 ()
 (local (in-theory (disable forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces)))

 (local (defthm lemma
          (implies (and (rw.hypboxp sub)
                        (rw.hypboxp sup)
                        (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                        (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup)))
                   (if (equal flag 'trace)
                       (implies (rw.eqtrace-okp x sub)
                                (rw.eqtrace-okp x sup))
                     (implies (rw.eqtrace-list-okp x sub)
                              (rw.eqtrace-list-okp x sup))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (rw.flag-eqtrace-okp flag x sub)
                  :in-theory (enable definition-of-rw.eqtrace-okp
                                     rw.eqtrace-step-okp)))))

 (defthm forcing-rw.eqtrace-okp-in-extended-hypbox
   (implies (and (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (rw.eqtrace-okp x sub)
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.eqtrace-okp x sup)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'trace))))))

 (defthm forcing-rw.eqtrace-list-okp-in-extended-hypbox
   (implies (and (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                 (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                 (rw.eqtrace-list-okp x sub)
                 (force (rw.hypboxp sub))
                 (force (rw.hypboxp sup)))
            (equal (rw.eqtrace-list-okp x sup)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))


(defthm rw.eqset-okp-in-extended-hypbox
  (implies (and (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                (rw.eqset-okp x sub)
                (force (rw.hypboxp sub))
                (force (rw.hypboxp sup)))
           (equal (rw.eqset-okp x sup)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqset-okp)
                                 ((:executable-counterpart ACL2::force))))))

(defthm rw.eqset-list-okp-in-extended-hypbox
  (implies (and (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                (rw.eqset-list-okp x sub)
                (force (rw.hypboxp sub))
                (force (rw.hypboxp sup)))
           (equal (rw.eqset-list-okp x sup)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.eqdatabase-okp-in-extended-hypbox
  (implies (and (subsetp (rw.hypbox->left sub) (rw.hypbox->left sup))
                (subsetp (rw.hypbox->right sub) (rw.hypbox->right sup))
                (rw.eqdatabase-okp x sub)
                (force (rw.hypboxp sub))
                (force (rw.hypboxp sup)))
           (equal (rw.eqdatabase-okp x sup)
                  t))
  :hints(("Goal" :in-theory (e/d (rw.eqdatabase-okp)
                                 (forcing-rw.eqset-list-okp-of-rw.eqdatabase->equalsets
                                  forcing-rw.eqset-list-okp-of-rw.eqdatabase->iffsets
                                  forcing-rw.trace-okp-of-rw.eqdatabase->contradiction)))))


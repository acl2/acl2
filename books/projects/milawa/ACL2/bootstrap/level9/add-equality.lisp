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
(%interactive)

(%autoprove forcing-uniquep-of-remove-all)

(%autoprove memberp-when-not-memberp-of-cdr)

(%autoprove equal-of-rw.eqset->heads-when-uniquep-of-rw.eqset-list-heads
            (%cdr-induction eqsets)
            (%enable default memberp-when-not-memberp-of-cdr))

(%autoprove uniquep-when-mutually-disjointp-and-cons-listp
            (%cdr-induction x))

(%autoprove rw.eqset-list-heads-of-remove-all
            (%cdr-induction x))

(%autoprove memberp-of-rw.eqset-list-rhses-when-memberp
            (%cdr-induction eqsets)
            (%enable default rw.eqset->rhses))

(%autoprove cons-listp-of-rw.eqset-list-rhses
            (%cdr-induction eqsets)
            (%enable default rw.eqset->rhses))

(%autoprove uniquep-of-rw.eqset-list-rhses-when-mutually-disjointp)

(%autoprove lemma-for-rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp
            (%use (%instance (%thm equal-when-length-different)
                             (a (rw.eqset-list-rhses (remove-all a x)))
                             (b (rw.eqset-list-rhses x)))))

(%autoprove rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp
            (%cdr-induction eqsets)
            (%enable default lemma-for-rw.eqset-list-rhses-of-remove-all-when-mutually-disjointp))

(%autoprove lemma-for-disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses
            (%cdr-induction eqsets)
            (%enable default rw.eqset->rhses memberp-when-not-memberp-of-cdr))

(%autoprove disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses
            (%enable default lemma-for-disjointp-of-rw.eqtrace-list-rhses-when-mutually-disjointp-of-rw.eqset-list-rhses))



(defsection rw.eqtrace-list-update

  (%defprojection :list (rw.eqtrace-list-update iffp e x)
                  :element (rw.trans1-eqtrace iffp e x))

  (%autoprove rw.eqtrace-list-iffps-of-rw.eqtrace-list-update
              (%cdr-induction x))

  (%autoprove rw.eqtrace-list-lhses-of-rw.eqtrace-list-update
              (%cdr-induction x))

  (%autoprove rw.eqtrace-list-rhses-of-rw.eqtrace-list-update
              (%cdr-induction x))

  (%autoprove forcing-rw.eqtrace-listp-of-rw.eqtrace-list-update
              (%cdr-induction x))

  (%autoprove forcing-rw.eqtrace-list-atblp-of-rw.eqtrace-list-update
              (%cdr-induction x))

  (%autoprove forcing-rw.eqtrace-list-okp-of-rw.eqtrace-list-update
              (%cdr-induction x)))




(defsection rw.find-relevant-eqset

  (%autoadmit rw.eqset-relevant)
  (%autoadmit rw.find-relevant-eqset)
  (local (%enable default rw.eqset-relevant))
  (local (%restrict default rw.find-relevant-eqset (equal eqsets 'eqsets)))

  (%autoprove forcing-rw.eqsetp-of-rw.find-relevant-eqset
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove forcing-rw.eqset-lookup-of-rw.find-relevant-eqset-under-iff
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove forcing-memberp-of-rw.find-relevant-eqset
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove forcing-rw.eqeqset-relevant-of-rw.find-relevant-eqset
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove forcing-rw.eqset->iffp-of-rw.find-relevant-eqset-when-all-equalp
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove memberp-of-rw.eqtrace-list-rhses-when-irrelevant
              (%enable default rw.eqset-lookup))

  (%autoprove memberp-of-rw.eqtrace-list-rhses-when-irrelevant-from-all
              (%autoinduct rw.find-relevant-eqset)
              (%enable default rw.eqset->rhses))

  (%autoprove memberp-of-rw.eqtrace-list-rhses-when-memberp-of-irrelevant-from-all
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove equal-to-rw.eqset->head-when-memberp-of-irrelevant-from-all
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove memberp-of-rw.eqset-list-heads-when-all-irrelevant
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove memberp-of-rw.eqtrace->lhs-in-rw.eqset-list-heads-when-no-relevant-sets
              (%autoinduct rw.find-relevant-eqset))

  (%autoprove rw.eqset->head-of-rw.find-relevant-eqset-when-among-heads
              (%autoinduct rw.find-relevant-eqset)
              (%enable default rw.eqset-lookup rw.eqset->rhses)))




(defsection rw.join-eqsets

  (%autoadmit rw.join-eqsets)

  (local (%enable default
                  rw.join-eqsets
                  rw.eqset-relevant
                  rw.eqset->rhses
                  rw.eqtrace-list-iffps-of-rev
                  [outside]rw.eqtrace-list-iffps-of-rev
                  rw.eqtrace-list-lhses-of-rev
                  [outside]rw.eqtrace-list-lhses-of-rev
                  rw.eqtrace-list-rhses-of-rev
                  [outside]rw.eqtrace-list-lhses-of-rev))

  (local (%disable default
                   rev-of-rw.eqtrace-list-iffps
                   [outside]rev-of-rw.eqtrace-list-iffps
                   rev-of-rw.eqtrace-list-lhses
                   [outside]rev-of-rw.eqtrace-list-lhses
                   rev-of-rw.eqtrace-list-rhses
                   [outside]rev-of-rw.eqtrace-list-rhses))

  (%autoprove lemma-for-rw.join-eqsets
              (%disable default transitivity-of-logic.term-< forcing-transitivity-of-logic.term-<-three)
              (%use (%instance (%thm transitivity-of-logic.term-<)
                               (x (rw.eqset->head lhs-set))
                               (y (rw.eqtrace->lhs trace))
                               (z (rw.eqtrace->rhs trace))))
              (%auto)
              (%fertilize (rw.eqset->head rhs-set) (rw.eqtrace->rhs trace))
              (%auto))

  (local (%enable default lemma-for-rw.join-eqsets))

  (%autoprove forcing-rw.eqsetp-of-rw.join-eqsets)
  (%autoprove forcing-rw.eqset-atblp-of-rw.join-eqsets)
  (%autoprove forcing-rw.eqset-okp-of-rw.join-eqsets)
  (%autoprove forcing-rw.eqset->iffp-of-rw.join-eqsets)
  (%autoprove forcing-rw.eqtrace-list-rhses-of-rw.eqset->tail-of-rw.join-eqsets)
  (%autoprove forcing-rw.eqset->head-of-rw.join-eqsets))


(defsection rw.eqset-extend
  (%autoadmit rw.eqset-extend)
  (local (%enable default rw.eqset-extend))
  (%autoprove forcing-rw.eqsetp-of-rw.eqset-extend)
  (%autoprove forcing-rw.eqset-atblp-of-rw.eqset-extend)
  (%autoprove forcing-rw.eqset-okp-of-rw.eqset-extend)
  (%autoprove forcing-rw.eqset->iffp-of-rw.eqset-extend)
  (%autoprove choices-for-rw.eqset->head-of-rw.eqset-extend))



(defsection rw.eqsets-extend

  (%autoadmit rw.eqsets-extend)
  (local (%enable default rw.eqsets-extend rw.eqset->rhses))
  (%autoprove forcing-rw.eqset-listp-of-rw.eqsets-extend)
  (%autoprove forcing-rw.eqset-list-atblp-of-rw.eqsets-extend)
  (%autoprove forcing-rw.eqrow-list-okp-of-rw.eqsets-extend)


  (%autoprove lemma-for-forcing-rw.eqset-list-iffps-of-rw.eqsets-extend)
  (%autoprove forcing-rw.eqset-list-iffps-of-rw.eqsets-extend
              (%use (%thm lemma-for-forcing-rw.eqset-list-iffps-of-rw.eqsets-extend))
              (%enable default all-equalp-removal)
              (%disable default rw.eqsets-extend))

  (%autoprove forcing-uniquep-of-rw.eqset-list-heads-of-rw.eqsets-extend
              (%auto)
              (%use (%instance (%thm choices-for-rw.eqset->head-of-rw.eqset-extend)
                               (trace trace)
                               (eqset (rw.find-relevant-eqset (rw.eqtrace->rhs trace) eqsets))))
              (%auto)
              (%use (%instance (%thm choices-for-rw.eqset->head-of-rw.eqset-extend)
                               (trace trace)
                               (eqset (rw.find-relevant-eqset (rw.eqtrace->lhs trace) eqsets)))))

  (%autoprove lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
              (%cdr-induction eqsets))

  (%autoprove forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
              (%enable default
                       lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
                       rw.eqset-extend
                       rw.eqtrace-list-rhses-of-rev)
              (%disable default
                        rev-of-rw.eqtrace-list-rhses
                        [outside]rev-of-rw.eqtrace-list-rhses))



  (defsection disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend

    ;; ACL2 seems smarter than Milawa and doesn't need these lemmas.
    (defthmd lemma-1-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
      (implies (force (rw.eqtracep x))
               (equal (equal (rw.eqtrace->lhs x) (rw.eqtrace->rhs x))
                      nil))
      :hints(("goal" :use ((:instance forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs)))))

    (defthmd lemma-2-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
      (implies (rw.eqtracep x)
               (iff (rw.eqtrace->lhs x)
                    t))
      :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep
                                        rw.eqtrace->lhs))))

    (defthmd lemma-3-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
      (implies (and (disjoint-from-allp heads rhses)
                    (memberp a rhses))
               (equal (disjointp a (remove-all b heads))
                      t)))

    (%autoprove lemma-1-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
                (%use (%instance (%thm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs))))

    (%autoprove lemma-2-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
                (%enable default definition-of-rw.eqtracep rw.eqtrace->lhs))

    (%autoprove lemma-3-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend)

    (%autoprove disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
                (%enable default
                         rw.eqsets-extend
                         rw.eqset-extend
                         rw.eqset->rhses
                         rw.eqtrace-list-rhses-of-rev
                         lemma-for-forcing-mutually-disjointp-of-rw.eqset-list-rhses-of-rw.eqsets-extend
                         lemma-1-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
                         lemma-2-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend
                         lemma-3-for-disjoint-from-allp-of-rw.eqrow-list-heads-and-rw.eqrow-list-rhses-of-rw.eqsets-extend)
                (%disable default
                          rev-of-rw.eqtrace-list-rhses
                          [outside]rev-of-rw.eqtrace-list-rhses)
                (%disable default
                          formula-decomposition
                          expensive-arithmetic-rules
                          expensive-arithmetic-rules-two
                          type-set-like-rules
                          same-length-prefixes-equal-cheap
                          unusual-consp-rules
                          expensive-term/formula-inference
                          unusual-memberp-rules
                          unusual-subsetp-rules))))




(defsection rw.eqdatabase-extend
  (%autoadmit rw.eqdatabase-extend)
  (local (%enable default rw.eqdatabase-extend))
  (%autoprove rw.eqdatabasep-of-rw.eqdatabase-extend)
  (%autoprove rw.eqdatabase-atblp-of-rw.eqdatabase-extend)
  (%autoprove rw.eqdatabase-okp-of-rw.eqdatabase-extend))


(defsection rw.primary-eqtrace-okp-in-extended-hypbox

  (defthmd lemma-1-for-rw.primary-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (equal (rw.primary-eqtrace t nhyp) trace)
                  (memberp nhyp x)
                  (force (logic.term-listp x)))
             (iff (rw.find-nhyp-for-primary-eqtracep x trace)
                  t))
    :hints(("Goal" :in-theory (enable rw.find-nhyp-for-primary-eqtracep))))

  (defthmd lemma-2-for-rw.primary-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (subsetp sub sup)
                  (rw.find-nhyp-for-primary-eqtracep sub trace)
                  (force (logic.term-listp sub))
                  (force (logic.term-listp sup)))
             (iff (rw.find-nhyp-for-primary-eqtracep sup trace)
                  t))
    :hints(("Goal" :use ((:instance lemma-1-for-rw.primary-eqtrace-okp-in-extended-hypbox
                                    (nhyp (rw.find-nhyp-for-primary-eqtracep sub trace))
                                    (x sup))))))

  (%autoprove lemma-1-for-rw.primary-eqtrace-okp-in-extended-hypbox
              (%autoinduct rw.find-nhyp-for-primary-eqtracep x trace)
              (%restrict default rw.find-nhyp-for-primary-eqtracep (equal nhyps 'x)))

  (%autoprove lemma-2-for-rw.primary-eqtrace-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-1-for-rw.primary-eqtrace-okp-in-extended-hypbox)
                               (nhyp (rw.find-nhyp-for-primary-eqtracep sub trace))
                               (x sup))))

  (%autoprove rw.primary-eqtrace-okp-in-extended-hypbox
              (%enable default
                       rw.primary-eqtrace-okp
                       lemma-1-for-rw.primary-eqtrace-okp-in-extended-hypbox
                       lemma-2-for-rw.primary-eqtrace-okp-in-extended-hypbox)))



(defsection rw.secondary-eqtrace-okp-in-extended-hypbox

  (defthmd lemma-1-for-rw.secondary-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (equal (rw.secondary-eqtrace t nhyp) trace)
                  (memberp nhyp x)
                  (force (logic.term-listp x)))
             (iff (rw.find-nhyp-for-secondary-eqtracep x trace)
                  t))
    :hints(("Goal" :in-theory (enable rw.find-nhyp-for-secondary-eqtracep))))

  (defthmd lemma-2-for-rw.secondary-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (subsetp sub sup)
                  (rw.find-nhyp-for-secondary-eqtracep sub trace)
                  (force (logic.term-listp sub))
                  (force (logic.term-listp sup)))
             (iff (rw.find-nhyp-for-secondary-eqtracep sup trace)
                  t))
    :hints(("Goal" :use ((:instance lemma-1-for-rw.secondary-eqtrace-okp-in-extended-hypbox
                                    (nhyp (rw.find-nhyp-for-secondary-eqtracep sub trace))
                                    (x sup))))))

  (%autoprove lemma-1-for-rw.secondary-eqtrace-okp-in-extended-hypbox
              (%autoinduct rw.find-nhyp-for-secondary-eqtracep x trace)
              (%restrict default rw.find-nhyp-for-secondary-eqtracep (equal nhyps 'x)))

  (%autoprove lemma-2-for-rw.secondary-eqtrace-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-1-for-rw.secondary-eqtrace-okp-in-extended-hypbox)
                               (nhyp (rw.find-nhyp-for-secondary-eqtracep sub trace))
                               (x sup))))

  (%autoprove rw.secondary-eqtrace-okp-in-extended-hypbox
              (%enable default
                       rw.secondary-eqtrace-okp
                       lemma-1-for-rw.secondary-eqtrace-okp-in-extended-hypbox
                       lemma-2-for-rw.secondary-eqtrace-okp-in-extended-hypbox)))



(defsection rw.direct-iff-eqtrace-okp-in-extended-hypbox

  (defthmd lemma-1-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (equal (rw.direct-iff-eqtrace t nhyp) trace)
                  (memberp nhyp x)
                  (force (logic.term-listp x)))
             (iff (rw.find-nhyp-for-direct-iff-eqtracep x trace)
                  t))
    :hints(("Goal" :in-theory (enable rw.find-nhyp-for-direct-iff-eqtracep))))

  (defthmd lemma-2-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (subsetp sub sup)
                  (rw.find-nhyp-for-direct-iff-eqtracep sub trace)
                  (force (logic.term-listp sub))
                  (force (logic.term-listp sup)))
             (iff (rw.find-nhyp-for-direct-iff-eqtracep sup trace)
                  t))
    :hints(("Goal" :use ((:instance lemma-1-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
                                    (nhyp (rw.find-nhyp-for-direct-iff-eqtracep sub trace))
                                    (x sup))))))

  (%autoprove lemma-1-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
              (%autoinduct rw.find-nhyp-for-direct-iff-eqtracep x trace)
              (%restrict default rw.find-nhyp-for-direct-iff-eqtracep (equal nhyps 'x)))

  (%autoprove lemma-2-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-1-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox)
                               (nhyp (rw.find-nhyp-for-direct-iff-eqtracep sub trace))
                               (x sup))))

  (%autoprove rw.direct-iff-eqtrace-okp-in-extended-hypbox
              (%enable default
                       rw.direct-iff-eqtrace-okp
                       lemma-1-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox
                       lemma-2-for-rw.direct-iff-eqtrace-okp-in-extended-hypbox)))



(defsection rw.negative-iff-eqtrace-okp-in-extended-hypbox

  (defthmd lemma-1-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
    ;; BOZO unlocalize
    (implies (and (equal (rw.negative-iff-eqtrace t nhyp) trace)
                  (memberp nhyp x)
                  (force (logic.term-listp x)))
             (iff (rw.find-nhyp-for-negative-iff-eqtracep x trace)
                  t))
    :hints(("Goal" :in-theory (enable rw.find-nhyp-for-negative-iff-eqtracep))))

  (defthmd lemma-2-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
    (implies (and (subsetp sub sup)
                  (rw.find-nhyp-for-negative-iff-eqtracep sub trace)
                  (force (logic.term-listp sub))
                  (force (logic.term-listp sup)))
             (iff (rw.find-nhyp-for-negative-iff-eqtracep sup trace)
                  t))
    :hints(("Goal" :use ((:instance lemma-1-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
                                    (nhyp (rw.find-nhyp-for-negative-iff-eqtracep sub trace))
                                    (x sup))))))

  (%autoprove lemma-1-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
              (%autoinduct rw.find-nhyp-for-negative-iff-eqtracep x trace)
              (%restrict default rw.find-nhyp-for-negative-iff-eqtracep (equal nhyps 'x)))

  (%autoprove lemma-2-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-1-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox)
                               (nhyp (rw.find-nhyp-for-negative-iff-eqtracep sub trace))
                               (x sup))))

  (%autoprove rw.negative-iff-eqtrace-okp-in-extended-hypbox
              (%enable default
                       rw.negative-iff-eqtrace-okp
                       lemma-1-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox
                       lemma-2-for-rw.negative-iff-eqtrace-okp-in-extended-hypbox)))



(defsection forcing-rw.eqtrace-okp-in-extended-hypbox

  ;; BOZO switch this to a defthms-flag and unlocalize.

  (local (in-theory (disable forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces)))
  (defthm lemma-for-forcing-rw.eqtrace-okp-in-extended-hypbox
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
                               rw.eqtrace-step-okp))))

  (%autoprove lemma-for-forcing-rw.eqtrace-okp-in-extended-hypbox
              (%autoinduct rw.flag-eqtrace-okp flag x sub)
              (%restrict default definition-of-rw.eqtrace-okp (equal x 'x))
              (%enable default rw.eqtrace-step-okp))

  (%autoprove forcing-rw.eqtrace-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-for-forcing-rw.eqtrace-okp-in-extended-hypbox)
                               (flag 'trace))))

  (%autoprove forcing-rw.eqtrace-list-okp-in-extended-hypbox
              (%use (%instance (%thm lemma-for-forcing-rw.eqtrace-okp-in-extended-hypbox)
                               (flag 'list)))))



(%autoprove rw.eqset-okp-in-extended-hypbox
            (%forcingp nil)
            (%enable default rw.eqset-okp))

(%autoprove rw.eqset-list-okp-in-extended-hypbox
            (%cdr-induction x))

(%autoprove rw.eqdatabase-okp-in-extended-hypbox
            (%enable default rw.eqdatabase-okp))



(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/add-equality")


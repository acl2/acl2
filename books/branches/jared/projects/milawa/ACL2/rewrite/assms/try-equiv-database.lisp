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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.eqtrace-list-lookup (term eqtraces)
  ;; Find the first eqtrace whose rhs is term.
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqtrace-listp eqtraces))))
  (if (consp eqtraces)
      (if (equal term (rw.eqtrace->rhs (car eqtraces)))
          (car eqtraces)
        (rw.eqtrace-list-lookup term (cdr eqtraces)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-list-lookup)))

 (defthm forcing-rw.eqtrace-list-lookup-under-iff
   (implies (force (rw.eqtrace-listp eqtraces))
            (iff (rw.eqtrace-list-lookup x eqtraces)
                 (memberp x (rw.eqtrace-list-rhses eqtraces)))))

 (local (in-theory (disable forcing-rw.eqtrace-list-lookup-under-iff)))

 (defthm forcing-rw.eqtracep-of-rw.eqtrace-list-lookup
   (implies (force (and (rw.eqtrace-list-lookup term eqtraces)
                        (rw.eqtrace-listp eqtraces)))
            (equal (rw.eqtracep (rw.eqtrace-list-lookup term eqtraces))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.eqtrace-list-lookup
   (implies (force (and (rw.eqtrace-list-lookup term eqtraces)
                        (rw.eqtrace-list-atblp eqtraces atbl)))
            (equal (rw.eqtrace-atblp (rw.eqtrace-list-lookup term eqtraces) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.eqtrace-list-lookup
   (implies (force (and (rw.eqtrace-list-lookup term eqtraces)
                        (rw.eqtrace-list-okp eqtraces box)))
            (equal (rw.eqtrace-okp (rw.eqtrace-list-lookup term eqtraces) box)
                   t)))

 (defthm forcing-memberp-of-rw.eqtrace-list-lookup
   (implies (force (rw.eqtrace-list-lookup term eqtraces))
            (equal (memberp (rw.eqtrace-list-lookup term eqtraces) eqtraces)
                   t)))

 (defthm forcing-eqtrace->rhs-of-rw.eqtrace-list-lookup
   (implies (force (rw.eqtrace-list-lookup term eqtraces))
            (equal (rw.eqtrace->rhs (rw.eqtrace-list-lookup term eqtraces))
                   term)))

 (defthm rw.eqtrace->lhs-of-rw.eqtrace-list-lookup-when-all-equalp
   (implies (and (all-equalp lhs (rw.eqtrace-list-lhses x))
                 (force (rw.eqtrace-list-lookup a x)))
            (equal (rw.eqtrace->lhs (rw.eqtrace-list-lookup a x))
                   lhs))))

(defthm forcing-rw.eqtrace->iffp-of-rw.eqtrace-list-lookup-in-rw.eqset->tail
   (implies (and (rw.eqtrace-list-lookup term (rw.eqset->tail eqset))
                 (force (rw.eqsetp eqset)))
            (equal (rw.eqtrace->iffp (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                   (rw.eqset->iffp eqset)))
   :hints(("Goal"
           :in-theory (disable rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps
                               rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps-alt)
           :use ((:instance rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps
                            (a    (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                            (x    (rw.eqset->tail eqset))
                            (iffp (rw.eqset->iffp eqset)))))))

(defthm forcing-rw.eqtrace->lhs-of-rw.eqtrace-list-lookup-in-rw.eqset->tail
   (implies (and (rw.eqtrace-list-lookup term (rw.eqset->tail eqset))
                 (force (rw.eqsetp eqset)))
            (equal (rw.eqtrace->lhs (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                   (rw.eqset->head eqset)))
   :hints(("Goal"
           :in-theory (disable rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
                               rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses-alt)
           :use ((:instance rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
                            (a    (rw.eqtrace-list-lookup term (rw.eqset->tail eqset)))
                            (x    (rw.eqset->tail eqset))
                            (lhs  (rw.eqset->head eqset)))))))




(definlined rw.eqset-lookup (term eqset)
  ;; Find the relevant eqtrace from an eqset.
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqsetp eqset))
                  :guard-hints (("Goal" :in-theory (enable rw.eqsetp)))))
  (if (logic.term-< term (rw.eqset->head eqset))
      ;; Optimization: we don't bother looking if term < head, since head < rhs
      ;; for every rhs in the tail.
      nil
    (rw.eqtrace-list-lookup term (rw.eqset->tail eqset))))

(encapsulate
 ()
 (local (in-theory (enable rw.eqset-lookup)))

 (defthm rw.eqset-lookup-of-term-and-nil
   (equal (rw.eqset-lookup term nil)
          nil))

 (local (in-theory (disable (:executable-counterpart ACL2::force))))

 (defthm forcing-rw.eqtracep-of-rw.eqset-lookup
   (implies (force (and (rw.eqset-lookup term eqset)
                        (rw.eqsetp eqset)))
            (equal (rw.eqtracep (rw.eqset-lookup term eqset))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.eqset-lookup
   (implies (force (and (rw.eqset-lookup term eqset)
                        (rw.eqset-atblp eqset atbl)))
            (equal (rw.eqtrace-atblp (rw.eqset-lookup term eqset) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.eqset-lookup
   (implies (force (and (rw.eqset-lookup term eqset)
                        (rw.eqset-okp eqset box)))
            (equal (rw.eqtrace-okp (rw.eqset-lookup term eqset) box)
                   t)))

 (defthm forcing-memberp-of-rw.eqset-lookup
   (implies (force (rw.eqset-lookup term eqset))
            (equal (memberp (rw.eqset-lookup term eqset)
                            (rw.eqset->tail eqset))
                   t)))

 (defthm forcing-eqtrace->iffp-of-rw.eqset-lookup
   (implies (force (and (rw.eqset-lookup term eqset)
                        (rw.eqsetp eqset)))
            (equal (rw.eqtrace->iffp (rw.eqset-lookup term eqset))
                   (rw.eqset->iffp eqset)))
   :hints(("Goal"
           :in-theory (disable rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps
                               rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps-alt)
           :use ((:instance rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps
                            (a    (rw.eqset-lookup term eqset))
                            (x    (rw.eqset->tail eqset))
                            (iffp (rw.eqset->iffp eqset)))))))

 (defthm forcing-eqtrace->rhs-of-rw.eqset-lookup
   (implies (force (rw.eqset-lookup term eqset))
            (equal (rw.eqtrace->rhs (rw.eqset-lookup term eqset))
                   term)))

 (defthm forcing-eqtrace->lhs-of-rw.eqset-lookup
   (implies (force (and (rw.eqset-lookup term eqset)
                        (rw.eqsetp eqset)))
            (equal (rw.eqtrace->lhs (rw.eqset-lookup term eqset))
                   (rw.eqset->head eqset)))
   :hints(("Goal"
           :in-theory (disable rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
                               rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses-alt)
           :use ((:instance rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
                            (a   (rw.eqset-lookup term eqset))
                            (x   (rw.eqset->tail eqset))
                            (lhs (rw.eqset->head eqset))))))))

(encapsulate
 ()
 (defthmd lemma-for-rw.eqset-lookup-of-rw.eqset->head
   (implies (and (rw.eqtrace-listp x)
                 (all-equalp lhs (rw.eqtrace-list-lhses x)))
            (equal (logic.all-terms-largerp lhs (rw.eqtrace-list-rhses x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthmd lemma-2-for-rw.eqset-lookup-of-rw.eqset->head
   (implies (and (logic.all-terms-largerp a (rw.eqtrace-list-rhses x))
                 (force (rw.eqtrace-listp x)))
            (equal (rw.eqtrace-list-lookup a x)
                   nil))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-rw.eqset-lookup-of-rw.eqset->head
   (implies (force (rw.eqsetp x))
            (equal (rw.eqset-lookup (rw.eqset->head x) x)
                   nil))
   :hints(("Goal" :in-theory (enable rw.eqset-lookup
                                     lemma-for-rw.eqset-lookup-of-rw.eqset->head
                                     lemma-2-for-rw.eqset-lookup-of-rw.eqset->head))))

 (defthm forcing-rw.eqset-lookup-of-rw.eqset->head-free
   (implies (and (equal (rw.eqset->head x) head)
                 (force (rw.eqsetp x)))
            (equal (rw.eqset-lookup head x)
                   nil)))

 (defthm forcing-memberp-of-rw.eqset->head-in-rw.eqtrace-list-rhses-of-rw.eqset->tail
   (implies (force (rw.eqsetp eqset))
            (equal (memberp (rw.eqset->head eqset)
                            (rw.eqtrace-list-rhses (rw.eqset->tail eqset)))
                   nil))
   :hints(("Goal" :use ((:instance lemma-for-rw.eqset-lookup-of-rw.eqset->head
                                   (lhs (rw.eqset->head eqset))
                                   (x   (rw.eqset->tail eqset)))))))

 (defthm forcing-memberp-of-rw.eqset->head-in-rw.eqtrace-list-rhses-of-rw.eqset->tail-free
   (implies (and (equal (rw.eqset->head eqset) free)
                 (force (rw.eqsetp eqset)))
            (equal (memberp free (rw.eqtrace-list-rhses (rw.eqset->tail eqset)))
                   nil)))

 (defthm forcing-memberp-of-rw.eqtrace-list-rhses-of-rw.eqset->tail-when-smaller-than-head
   (implies (and (logic.term-< term (rw.eqset->head eqset))
                 (force (rw.eqsetp eqset)))
            (equal (memberp term (rw.eqtrace-list-rhses (rw.eqset->tail eqset)))
                   nil))
   :hints(("Goal" :use ((:instance lemma-for-rw.eqset-lookup-of-rw.eqset->head
                                   (lhs (rw.eqset->head eqset))
                                   (x   (rw.eqset->tail eqset)))))))

 (defthm forcing-logic.term-<-of-rw.eqset->head-when-rw.eqset-lookup
   (implies (and (rw.eqset-lookup term eqset)
                 (force (rw.eqsetp eqset)))
            (logic.term-< (rw.eqset->head eqset)
                          term))
   :hints(("Goal" :in-theory (enable rw.eqset-lookup
                                     lemma-for-rw.eqset-lookup-of-rw.eqset->head
                                     lemma-2-for-rw.eqset-lookup-of-rw.eqset->head)))))






(defund rw.eqset-list-lookup (term eqsets)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqset-listp eqsets))))
  (if (consp eqsets)
      (or (rw.eqset-lookup term (car eqsets))
          (rw.eqset-list-lookup term (cdr eqsets)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.eqset-list-lookup)))

 (defthm forcing-rw.eqtracep-of-rw.eqset-list-lookup
   (implies (force (and (rw.eqset-list-lookup term eqsets)
                        (rw.eqset-listp eqsets)))
            (equal (rw.eqtracep (rw.eqset-list-lookup term eqsets))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.eqset-list-lookup
   (implies (force (and (rw.eqset-list-lookup term eqsets)
                        (rw.eqset-list-atblp eqsets atbl)))
            (equal (rw.eqtrace-atblp (rw.eqset-list-lookup term eqsets) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.eqset-list-lookup
   (implies (force (and (rw.eqset-list-lookup term eqsets)
                        (rw.eqset-list-okp eqsets box)))
            (equal (rw.eqtrace-okp (rw.eqset-list-lookup term eqsets) box)
                   t)))

 (defthm forcing-eqtrace->rhs-of-rw.eqset-list-lookup
   (implies (force (rw.eqset-list-lookup term eqsets))
            (equal (rw.eqtrace->rhs (rw.eqset-list-lookup term eqsets))
                   term)))

 (defthm forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp
   (implies (and (all-equalp iffp (rw.eqset-list-iffps eqsets))
                 (force (rw.eqset-list-lookup term eqsets))
                 (force (rw.eqset-listp eqsets)))
            (equal (rw.eqtrace->iffp (rw.eqset-list-lookup term eqsets))
                   iffp))))



(definlined rw.try-equiv-database (term database iffp)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.eqdatabasep database)
                              (booleanp iffp))))
  (if iffp
      (rw.eqset-list-lookup term (rw.eqdatabase->iffsets database))
    (rw.eqset-list-lookup term (rw.eqdatabase->equalsets database))))

(encapsulate
 ()
 (local (in-theory (enable rw.try-equiv-database)))

 (defthm forcing-rw.eqtracep-of-rw.try-equiv-database
   (implies (force (and (rw.try-equiv-database term database iffp)
                        (rw.eqdatabasep database)))
            (equal (rw.eqtracep (rw.try-equiv-database term database iffp))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.try-equiv-database
   (implies (force (and (rw.try-equiv-database term database iffp)
                        (rw.eqdatabase-atblp database atbl)))
            (equal (rw.eqtrace-atblp (rw.try-equiv-database term database iffp) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.try-equiv-database
   (implies (force (and (rw.try-equiv-database term database iffp)
                        (rw.eqdatabase-okp database box)))
            (equal (rw.eqtrace-okp (rw.try-equiv-database term database iffp) box)
                   t)))

 (defthm forcing-eqtrace->rhs-of-rw.try-equiv-database
   (implies (force (rw.try-equiv-database term database iffp))
            (equal (rw.eqtrace->rhs (rw.try-equiv-database term database iffp))
                   term)))

 (defthm forcing-eqtrace->iffp-of-rw.try-equiv-database
   (implies (force (and (rw.try-equiv-database term database iffp)
                        (rw.eqdatabasep database)))
            (equal (rw.eqtrace->iffp (rw.try-equiv-database term database iffp))
                   (if iffp
                       t
                     nil)))
   :hints(("Goal"
           :use ((:instance forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp
                            (iffp nil)
                            (eqsets (rw.eqdatabase->equalsets database))
                            (term term))
                 (:instance forcing-rw.eqtrace->iffp-of-rw.eqset-list-lookup-when-all-equalp
                            (iffp t)
                            (eqsets (rw.eqdatabase->iffsets database))
                            (term term)))))))


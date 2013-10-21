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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; We introduce some fused operations for greater efficiency.  IMO the compiler
;; should be smart enough to do this, but IRL it isn't.  I guess TANSTAAFL,
;; after all.

(defund logic.=rhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.=rhs (logic.conclusion (car x)))
            (logic.=rhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=rhses-of-strip-conclusions-removal
  (equal (logic.=rhses-of-strip-conclusions x)
         (logic.=rhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.=rhses-of-strip-conclusions))))



(defund logic.=lhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.=lhs (logic.conclusion (car x)))
            (logic.=lhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=lhses-of-strip-conclusions-removal
  (equal (logic.=lhses-of-strip-conclusions x)
         (logic.=lhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.=lhses-of-strip-conclusions))))




(defund logic.vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.vrhs (logic.conclusion (car x)))
            (logic.vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.vrhses-of-strip-conclusions-removal
  (equal (logic.vrhses-of-strip-conclusions x)
         (logic.vrhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.vrhses-of-strip-conclusions))))


(defund logic.vlhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (logic.vlhs (logic.conclusion (car x)))
            (logic.vlhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.vlhses-of-strip-conclusions-removal
  (equal (logic.vlhses-of-strip-conclusions x)
         (logic.vlhses (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.vlhses-of-strip-conclusions))))


(defund logic.=lhses-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (logic.=lhs (logic.vrhs (logic.conclusion (car x))))
            (logic.=lhses-of-vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=lhses-of-vrhses-of-strip-conclusions-removal
  (equal (logic.=lhses-of-vrhses-of-strip-conclusions x)
         (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.=lhses-of-vrhses-of-strip-conclusions))))


(defund logic.=rhses-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (logic.=rhs (logic.vrhs (logic.conclusion (car x))))
            (logic.=rhses-of-vrhses-of-strip-conclusions (cdr x)))
    nil))

(defthm logic.=rhses-of-vrhses-of-strip-conclusions-removal
  (equal (logic.=rhses-of-vrhses-of-strip-conclusions x)
         (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.=rhses-of-vrhses-of-strip-conclusions))))




(defund logic.all-atomicp-of-strip-conclusions (x)
  (declare (xargs :guard (logic.appeal-listp x)))
  (if (consp x)
      (and (equal (logic.fmtype (logic.conclusion (car x))) 'pequal*)
           (logic.all-atomicp-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-atomicp-of-strip-conclusions-removal
  (equal (logic.all-atomicp-of-strip-conclusions x)
         (logic.all-atomicp (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.all-atomicp-of-strip-conclusions))))



(defund logic.all-disjunctionsp-of-strip-conclusions (x)
  (declare (xargs :guard (logic.appeal-listp x)))
  (if (consp x)
      (and (equal (logic.fmtype (logic.conclusion (car x))) 'por*)
           (logic.all-disjunctionsp-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-disjunctionsp-of-strip-conclusions-removal
  (equal (logic.all-disjunctionsp-of-strip-conclusions x)
         (logic.all-disjunctionsp (logic.strip-conclusions x)))
  :hints(("Goal" :in-theory (enable logic.all-disjunctionsp-of-strip-conclusions))))


(defund logic.all-atomicp-of-vrhses-of-strip-conclusions (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x)))))
  (if (consp x)
      (and (equal (logic.fmtype (logic.vrhs (logic.conclusion (car x)))) 'pequal*)
           (logic.all-atomicp-of-vrhses-of-strip-conclusions (cdr x)))
    t))

(defthm logic.all-atomicp-of-vrhses-of-strip-conclusions-removal
  (equal (logic.all-atomicp-of-vrhses-of-strip-conclusions x)
         (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))
  :hints(("Goal" :in-theory (enable logic.all-atomicp-of-vrhses-of-strip-conclusions))))

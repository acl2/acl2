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
(include-book "rulep")
(include-book "worse-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Ancestors Checking
;;
;; Sometimes rewrite rules can cause backchaining loops.  For example, if we
;; have this rule:
;;
;;   (true-listp (cdr x)) --> (true-listp x)
;;
;; We might repeatedly try to apply it and get ourselves stuck in a loop:
;;
;;  *1 (true-listp a)                   ;; initial goal goal
;;  *2 (true-listp (cdr a))             ;; goal after applying to *1
;;  *3 (true-listp (cdr (cdr a)))       ;; goal after applying to *2
;;  *4 (true-listp (cdr (cdr (cdr a)))) ;; goal after applying to *3
;;  ...
;;
;; Similar loops can be caused by multiple rules, too.  For example:
;;
;;  a. (foo (cdr x)) --> (bar x)
;;  b. (bar (cdr x)) --> (foo x)
;;
;;  *1 (foo a)                          ;; initial goal
;;  *2 (bar (cdr a))                    ;; try b to rewrite *1
;;  *3 (foo (cdr (cdr a)))              ;; try a to rewrite *2
;;  *4 (bar (cdr (cdr (cdr a))))        ;; try b to rewrite *3
;;  ...
;;
;; Eventually these loops will hit the backchain limits, but it might be very
;; expensive to let them wander that long.  ACL2 avoids the ill effects of such
;; rules by using a heuristic "ancestors check" that sometimes prevents rules
;; from firing.  We implement a similar heuristic here.
;;
;; Our implementation of ancestors checking works much like ACL2's.  Each time
;; we backchain, we push a frame onto the ANCESTORS STACK.  These frames keep
;; track of the current hypothesis we are trying to relieve, the name of the
;; rule are backchaining on behalf of, and some other information.  Then,
;; before we backchain to relieve a new hyp, we check the hyp against the stack
;; of ancestors.  If it seems worse than a prior goal, we heuristically prevent
;; the backchain from occurring.

(definlined rw.anframep (x)
  (declare (xargs :guard t))
  (and (tuplep 4 x)
       (let ((term   (first x))
             (guts   (second x))
             (fcount (third x))
             (tokens (fourth x)))
         (declare (ignore tokens))
         (and (logic.termp term)
              (equal guts (if (clause.negative-termp term)
                              (clause.negative-term-guts term)
                            term))
              (equal (logic.count-function-occurrences guts) fcount)))))

(defthm booleanp-of-rw.anframep
  (equal (booleanp (rw.anframep x))
         t)
  :hints(("Goal" :in-theory (enable rw.anframep))))


(deflist rw.anstackp (x)
  (rw.anframep x)
  :elementp-of-nil nil)


(definlined rw.anframe->term (x)
  (declare (xargs :guard (rw.anframep x)
                  :guard-hints (("Goal" :in-theory (enable rw.anframep)))))
  (first x))

(definlined rw.anframe->guts (x)
  (declare (xargs :guard (rw.anframep x)
                  :guard-hints (("Goal" :in-theory (enable rw.anframep)))))
  (second x))

(definlined rw.anframe->fcount (x)
  (declare (xargs :guard (rw.anframep x)
                  :guard-hints (("Goal" :in-theory (enable rw.anframep)))))
  (third x))

(definlined rw.anframe->tokens (x)
  (declare (xargs :guard (rw.anframep x)
                  :guard-hints (("Goal" :in-theory (enable rw.anframep)))))
  (fourth x))


(defthm forcing-logic.termp-of-rw.anframe->term
  (implies (force (rw.anframep x))
           (equal (logic.termp (rw.anframe->term x))
                  t))
  :hints(("Goal" :in-theory (enable rw.anframe->term rw.anframep))))

(defthm forcing-logic.termp-of-rw.anframe->guts
  (implies (force (rw.anframep x))
           (equal (logic.termp (rw.anframe->guts x))
                  t))
  :hints(("Goal" :in-theory (enable rw.anframe->guts rw.anframep))))

(defthm forcing-rw.anframe->fcount-elimination
  (implies (force (rw.anframep x))
           (equal (rw.anframe->fcount x)
                  (logic.count-function-occurrences (rw.anframe->guts x))))
  :hints(("Goal" :in-theory (enable rw.anframep rw.anframe->fcount rw.anframe->guts))))



(definlined rw.anframe (term tokens)
  (declare (xargs :guard (logic.termp term)))
  (let* ((guts   (if (clause.negative-termp term)
                     (clause.negative-term-guts term)
                   term))
         (fcount (logic.count-function-occurrences guts)))
    (list term guts fcount tokens)))

(defthm rw.anframep-of-rw.anframe
  (implies (logic.termp term)
           (equal (rw.anframep (rw.anframe term tokens))
                  t))
  :hints(("Goal" :in-theory (enable rw.anframe rw.anframep))))



(defund rw.earlier-ancestor-biggerp (guts fcount tokens ancestors)
  (declare (xargs :guard (and (logic.termp guts)
                              (equal (logic.count-function-occurrences guts) fcount)
                              (rw.anstackp ancestors))))
  (if (consp ancestors)
      (let* ((ancestor1        (car ancestors))
             (ancestor1-guts   (rw.anframe->guts ancestor1))
             (ancestor1-fcount (rw.anframe->fcount ancestor1))
             (ancestor1-tokens (rw.anframe->tokens ancestor1)))
        (or (and (not (disjointp tokens ancestor1-tokens))
                 (or (< fcount ancestor1-fcount)
                     (and (equal fcount ancestor1-fcount)
                          (rw.worse-than-or-equal-termp guts ancestor1-guts))))
            (rw.earlier-ancestor-biggerp guts fcount tokens (cdr ancestors))))
    nil))

(defund rw.ancestors-check-aux (term guts fcount tokens ancestors)
  (declare (xargs :guard (and (logic.termp term)
                              (equal guts (if (clause.negative-termp term)
                                              (clause.negative-term-guts term)
                                            term))
                              (equal (logic.count-function-occurrences guts) fcount)
                              (rw.anstackp ancestors))))
  (if (consp ancestors)
      (let* ((ancestor1        (car ancestors))
             (ancestor1-term   (rw.anframe->term ancestor1))
             (ancestor1-guts   (rw.anframe->guts ancestor1))
             (ancestor1-fcount (rw.anframe->fcount ancestor1))
             (ancestor1-tokens (rw.anframe->tokens ancestor1)))
        (cond ((or (equal term ancestor1-term)
                   (equal guts ancestor1-guts))
               ;; Stop early, this hyp or its negation are already on the stack.
               t)
              ((not (disjointp tokens ancestor1-tokens))
               ;; Overlapping tokens case.  If the term has gotten worse and we
               ;; are comparing calls of the same function or lambda, then stop
               ;; early.
               (or (and (or (< ancestor1-fcount fcount)
                            (and (equal ancestor1-fcount fcount)
                                 (rw.worse-than-or-equal-termp guts ancestor1-guts)))
                        (or (and (logic.functionp guts)
                                 (logic.functionp ancestor1-guts)
                                 (equal (logic.function-name guts) (logic.function-name ancestor1-guts)))
                            (and (logic.lambdap guts)
                                 (logic.lambdap ancestor1-guts)
                                 (equal (logic.lambda-formals guts) (logic.lambda-formals ancestor1-guts))
                                 (equal (logic.lambda-body guts) (logic.lambda-body ancestor1-guts)))))
                   (rw.ancestors-check-aux term guts fcount tokens (cdr ancestors))))
              ((and (or (< ancestor1-fcount fcount)
                        (equal ancestor1-fcount fcount))
                    (rw.worse-than-or-equal-termp guts ancestor1-guts)
                    ;; Here we are blindly reimplementing what ACL2 does.  I
                    ;; only halfway understand this after reading the comments
                    ;; in the ACL2 sources, so I will not try to explain it.
                    (not (rw.earlier-ancestor-biggerp guts fcount ancestor1-tokens (cdr ancestors))))
               t)
              (t
               (rw.ancestors-check-aux term guts fcount tokens (cdr ancestors)))))
    nil))

(definlined rw.ancestors-check (term tokens ancestors)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.anstackp ancestors))))
  (let* ((guts (if (clause.negative-termp term)
                   (clause.negative-term-guts term)
                 term))
         (fcount (logic.count-function-occurrences guts)))
    (rw.ancestors-check-aux term guts fcount tokens ancestors)))


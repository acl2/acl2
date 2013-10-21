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
(include-book "hypboxp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Equivalence traces.
;;
;; Much like our rewriter, our assumptions system builds traces which can be
;; compiled into actual proofs.  This file introduces the generic recognizer
;; for syntactically valid equivalence traces.  (Object-oriented folks can
;; think of this as an abstract base class.)  See also eqtrace-okp, which
;; introduces the concrete kinds of traces (i.e., the subclasses), and finally
;; eqtrace-compiler.lisp, which defines the compilers for these subclasses.

(defun rw.flag-eqtracep (flag x)
  (declare (xargs :guard (or (equal flag 'trace)
                             (equal flag 'list))))
  (if (equal flag 'trace)
      ;; We use the cons structure (lhs . rhs) . (iffp . (method . subtraces))
      (let ((lhs       (car (car x)))
            (rhs       (cdr (car x)))
            (iffp      (car (cdr x)))
            (method    (car (cdr (cdr x))))
            (subtraces (cdr (cdr (cdr x)))))
        (and (symbolp method)
             (booleanp iffp)
             (logic.termp lhs)
             (logic.termp rhs)
             (logic.term-< lhs rhs)
             (rw.flag-eqtracep 'list subtraces)))
    (if (consp x)
        (and (rw.flag-eqtracep 'trace (car x))
             (rw.flag-eqtracep 'list (cdr x)))
      t)))

(definlined rw.eqtracep (x)
  (declare (xargs :guard t))
  (rw.flag-eqtracep 'trace x))

(definlined rw.eqtrace-listp (x)
  (declare (xargs :guard t))
  (rw.flag-eqtracep 'list x))

(defthmd definition-of-rw.eqtracep
  (equal (rw.eqtracep x)
         (let ((lhs       (car (car x)))
               (rhs       (cdr (car x)))
               (iffp      (car (cdr x)))
               (method    (car (cdr (cdr x))))
               (subtraces (cdr (cdr (cdr x)))))
           (and (symbolp method)
                (booleanp iffp)
                (logic.termp lhs)
                (logic.termp rhs)
                (logic.term-< lhs rhs)
                (rw.eqtrace-listp subtraces))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtracep rw.eqtrace-listp))))

(defthmd definition-of-rw.eqtrace-listp
  (equal (rw.eqtrace-listp x)
         (if (consp x)
             (and (rw.eqtracep (car x))
                  (rw.eqtrace-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtracep rw.eqtrace-listp))))

(defthm rw.flag-eqtracep-of-trace
  (equal (rw.flag-eqtracep 'trace x)
         (rw.eqtracep x))
  :hints(("Goal" :in-theory (enable rw.eqtracep))))

(defthm rw.flag-eqtracep-of-list
  (equal (rw.flag-eqtracep 'list x)
         (rw.eqtrace-listp x))
  :hints(("Goal" :in-theory (enable rw.eqtrace-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtracep))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-listp))))

(defthms-flag
  :thms ((trace booleanp-of-rw.eqtracep
                (equal (booleanp (rw.eqtracep x))
                       t))
         (t booleanp-of-rw.eqtrace-listp
            (equal (booleanp (rw.eqtrace-listp x))
                   t)))
  :hints(("Goal"
          :induct (rw.flag-eqtracep flag x)
          :in-theory (enable definition-of-rw.eqtracep
                             definition-of-rw.eqtrace-listp))))

(defthm rw.eqtrace-listp-when-not-consp
  (implies (not (consp x))
           (equal (rw.eqtrace-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-listp))))

(defthm rw.eqtrace-listp-of-cons
  (equal (rw.eqtrace-listp (cons a x))
         (and (rw.eqtracep a)
              (rw.eqtrace-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-listp))))

(deflist rw.eqtrace-listp (x)
  (rw.eqtracep x)
  :elementp-of-nil nil
  :already-definedp t)



(definlined rw.eqtrace->method (x)
  (declare (xargs :guard (rw.eqtracep x)))
  (car (cdr (cdr x))))

(definlined rw.eqtrace->iffp (x)
  (declare (xargs :guard (rw.eqtracep x)))
  (car (cdr x)))

(definlined rw.eqtrace->lhs (x)
  (declare (xargs :guard (rw.eqtracep x)))
  (car (car x)))

(definlined rw.eqtrace->rhs (x)
  (declare (xargs :guard (rw.eqtracep x)))
  (cdr (car x)))

(definlined rw.eqtrace->subtraces (x)
  (declare (xargs :guard (rw.eqtracep x)))
  (cdr (cdr (cdr x))))

(defthm forcing-symbolp-of-rw.eqtrace->method
  (implies (force (rw.eqtracep x))
           (equal (symbolp (rw.eqtrace->method x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->method))))

(defthm forcing-booleanp-of-rw.eqtrace->iffp
  (implies (force (rw.eqtracep x))
           (equal (booleanp (rw.eqtrace->iffp x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->iffp))))

(defthm forcing-logic.termp-of-rw.eqtrace->lhs
  (implies (force (rw.eqtracep x))
           (equal (logic.termp (rw.eqtrace->lhs x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->lhs))))

(defthm forcing-logic.termp-of-rw.eqtrace->rhs
  (implies (force (rw.eqtracep x))
           (equal (logic.termp (rw.eqtrace->rhs x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->rhs))))

(defthm forcing-rw.eqtrace-listp-of-rw.eqtrace->subtraces
  (implies (force (rw.eqtracep x))
           (equal (rw.eqtrace-listp (rw.eqtrace->subtraces x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->subtraces))))

(defthm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs
  (implies (force (rw.eqtracep x))
           (equal (logic.term-< (rw.eqtrace->lhs x)
                                (rw.eqtrace->rhs x))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep
                                    rw.eqtrace->lhs
                                    rw.eqtrace->rhs))))

(defthm forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs-free
  (implies (and (equal (rw.eqtrace->lhs x) lhs)
                (equal (rw.eqtrace->rhs x) rhs)
                (force (rw.eqtracep x)))
           (equal (logic.term-< lhs rhs)
                  t)))


(defthm |(< a (+ b c d e f a g))|
  (equal (< a (+ b (+ c (+ d (+ e (+ f (+ a g)))))))
         (< 0 (+ b (+ c (+ d (+ e (+ f g))))))))

(defthm rank-of-rw.eqtrace->subtraces-weak
  (equal (< (rank x) (rank (rw.eqtrace->subtraces x)))
         nil)
  :hints(("Goal" :in-theory (enable rw.eqtrace->subtraces))))




(defun rw.flag-eqtrace-atblp (flag x atbl)
  (declare (xargs :guard (if (equal flag 'trace)
                             (and (rw.eqtracep x)
                                  (logic.arity-tablep atbl))
                           (and (equal flag 'list)
                                (rw.eqtrace-listp x)
                                (logic.arity-tablep atbl)))
                  :measure (two-nats-measure (rank x) (if (equal flag 'trace) 1 0))))
  (if (equal flag 'trace)
      (and (logic.term-atblp (rw.eqtrace->lhs x) atbl)
           (logic.term-atblp (rw.eqtrace->rhs x) atbl)
           (rw.flag-eqtrace-atblp 'list (rw.eqtrace->subtraces x) atbl))
    (if (consp x)
        (and (rw.flag-eqtrace-atblp 'trace (car x) atbl)
             (rw.flag-eqtrace-atblp 'list (cdr x) atbl))
      t)))

(definlined rw.eqtrace-atblp (x atbl)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (logic.arity-tablep atbl))))
  (rw.flag-eqtrace-atblp 'trace x atbl))

(definlined rw.eqtrace-list-atblp (x atbl)
  (declare (xargs :guard (and (rw.eqtrace-listp x)
                              (logic.arity-tablep atbl))))
  (rw.flag-eqtrace-atblp 'list x atbl))

(defthmd definition-of-rw.eqtrace-atblp
  (equal (rw.eqtrace-atblp x atbl)
         (and (logic.term-atblp (rw.eqtrace->lhs x) atbl)
              (logic.term-atblp (rw.eqtrace->rhs x) atbl)
              (rw.eqtrace-list-atblp (rw.eqtrace->subtraces x) atbl)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-atblp
                                    rw.eqtrace-list-atblp))))

(defthmd definition-of-rw.eqtrace-list-atblp
  (equal (rw.eqtrace-list-atblp x atbl)
         (if (consp x)
             (and (rw.eqtrace-atblp (car x) atbl)
                  (rw.eqtrace-list-atblp (cdr x) atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-atblp
                                    rw.eqtrace-list-atblp))))

(defthm rw.flag-eqtrace-atblp-of-trace
  (equal (rw.flag-eqtrace-atblp 'trace x atbl)
         (rw.eqtrace-atblp x atbl))
  :hints(("Goal" :in-theory (enable rw.eqtrace-atblp))))

(defthm rw.flag-eqtrace-atblp-of-list
  (equal (rw.flag-eqtrace-atblp 'list x atbl)
         (rw.eqtrace-list-atblp x atbl))
  :hints(("Goal" :in-theory (enable rw.eqtrace-list-atblp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-atblp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-list-atblp))))

(defthms-flag
  :thms ((trace booleanp-of-rw.eqtrace-atblp
                (equal (booleanp (rw.eqtrace-atblp x atbl))
                       t))
         (t booleanp-of-rw.eqtrace-list-atblp
            (equal (booleanp (rw.eqtrace-list-atblp x atbl))
                   t)))
  :hints(("Goal"
          :induct (rw.flag-eqtrace-atblp flag x atbl)
          :in-theory (enable definition-of-rw.eqtrace-atblp
                             definition-of-rw.eqtrace-list-atblp))))

(defthm rw.eqtrace-list-atblp-when-not-consp
  (implies (not (consp x))
           (equal (rw.eqtrace-list-atblp x atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-atblp))))

(defthm rw.eqtrace-list-atblp-of-cons
  (equal (rw.eqtrace-list-atblp (cons a x) atbl)
         (and (rw.eqtrace-atblp a atbl)
              (rw.eqtrace-list-atblp x atbl)))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-atblp))))

(defthm rw.eqtrace-atblp-of-nil
  (equal (rw.eqtrace-atblp nil atbl)
         nil)
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-atblp))))

(deflist rw.eqtrace-list-atblp (x atbl)
  (rw.eqtrace-atblp x atbl)
  :elementp-of-nil nil
  :already-definedp t)

(defthm forcing-logic.term-atblp-of-rw.eqtrace->lhs
  (implies (force (rw.eqtrace-atblp x atbl))
           (equal (logic.term-atblp (rw.eqtrace->lhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-atblp))))

(defthm forcing-logic.term-atblp-of-rw.eqtrace->rhs
  (implies (force (rw.eqtrace-atblp x atbl))
           (equal (logic.term-atblp (rw.eqtrace->rhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-atblp))))

(defthm forcing-rw.eqtrace-list-atblp-of-rw.eqtrace->subtraces
  (implies (force (rw.eqtrace-atblp x atbl))
           (equal (rw.eqtrace-list-atblp (rw.eqtrace->subtraces x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-atblp))))




(defund rw.eqtrace (method iffp lhs rhs subtraces)
  (declare (xargs :guard (and (symbolp method)
                              (booleanp iffp)
                              (logic.termp lhs)
                              (logic.termp rhs)
                              (logic.term-< lhs rhs)
                              (rw.eqtrace-listp subtraces))))
  (cons (cons lhs rhs)
        (cons iffp
              (cons method subtraces))))

(defthm rw.eqtrace->method-of-rw.eqtrace
  (equal (rw.eqtrace->method (rw.eqtrace method iffp lhs rhs subtraces))
         method)
  :hints(("Goal" :in-theory (enable rw.eqtrace rw.eqtrace->method))))

(defthm rw.eqtrace->iffp-of-rw.eqtrace
  (equal (rw.eqtrace->iffp (rw.eqtrace method iffp lhs rhs subtraces))
         iffp)
  :hints(("Goal" :in-theory (enable rw.eqtrace rw.eqtrace->iffp))))

(defthm rw.eqtrace->lhs-of-rw.eqtrace
  (equal (rw.eqtrace->lhs (rw.eqtrace method iffp lhs rhs subtraces))
         lhs)
  :hints(("Goal" :in-theory (enable rw.eqtrace rw.eqtrace->lhs))))

(defthm rw.eqtrace->rhs-of-rw.eqtrace
  (equal (rw.eqtrace->rhs (rw.eqtrace method iffp lhs rhs subtraces))
         rhs)
  :hints(("Goal" :in-theory (enable rw.eqtrace rw.eqtrace->rhs))))

(defthm rw.eqtrace->subtraces-of-rw.eqtrace
  (equal (rw.eqtrace->subtraces (rw.eqtrace method iffp lhs rhs subtraces))
         subtraces)
  :hints(("Goal" :in-theory (enable rw.eqtrace rw.eqtrace->subtraces))))

(defthm forcing-rw.eqtracep-of-rw.eqtrace
  (implies (force (and (symbolp method)
                       (booleanp iffp)
                       (logic.termp lhs)
                       (logic.termp rhs)
                       (logic.term-< lhs rhs)
                       (rw.eqtrace-listp subtraces)))
           (equal (rw.eqtracep (rw.eqtrace method iffp lhs rhs subtraces))
                  t))
  :hints(("Goal" :in-theory (enable rw.eqtrace definition-of-rw.eqtracep))))

(defthm forcing-rw.eqtrace-atblp-of-rw.eqtrace
  (implies (force (and (logic.term-atblp lhs atbl)
                       (logic.term-atblp rhs atbl)
                       (rw.eqtrace-list-atblp subtraces atbl)))
           (equal (rw.eqtrace-atblp (rw.eqtrace method iffp lhs rhs subtraces) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-atblp))))

(defthm rw.eqtrace-under-iff
  (iff (rw.eqtrace method iffp lhs rhs subtraces)
       t)
  :hints(("Goal" :in-theory (enable rw.eqtrace))))

(defprojection :list (rw.eqtrace-list-iffps x)
               :element (rw.eqtrace->iffp x)
               :guard (rw.eqtrace-listp x)
               :nil-preservingp t)

(defprojection :list (rw.eqtrace-list-lhses x)
               :element (rw.eqtrace->lhs x)
               :guard (rw.eqtrace-listp x)
               :nil-preservingp t)

(defprojection :list (rw.eqtrace-list-rhses x)
               :element (rw.eqtrace->rhs x)
               :guard (rw.eqtrace-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-rw.eqtrace-list-lhses
  (implies (force (rw.eqtrace-listp x))
           (equal (logic.term-listp (rw.eqtrace-list-lhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-listp-of-rw.eqtrace-list-rhses
  (implies (force (rw.eqtrace-listp x))
           (equal (logic.term-listp (rw.eqtrace-list-rhses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.eqtrace-list-lhses
  (implies (force (rw.eqtrace-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.eqtrace-list-lhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-rw.eqtrace-list-rhses
  (implies (force (rw.eqtrace-list-atblp x atbl))
           (equal (logic.term-list-atblp (rw.eqtrace-list-rhses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(defthm rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps
  (implies (and (all-equalp iffp (rw.eqtrace-list-iffps x))
                (memberp a x))
           (equal (rw.eqtrace->iffp a)
                  iffp))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps-alt
  (implies (and (memberp a x)
                (all-equalp iffp (rw.eqtrace-list-iffps x)))
           (equal (rw.eqtrace->iffp a)
                  iffp)))

(defthm rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
  (implies (and (all-equalp lhs (rw.eqtrace-list-lhses x))
                (memberp a x))
           (equal (rw.eqtrace->lhs a)
                  lhs))
  :hints (("Goal" :induct (cdr-induction x))))

(defthm rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses-alt
  (implies (and (memberp a x)
                (all-equalp lhs (rw.eqtrace-list-lhses x)))
           (equal (rw.eqtrace->lhs a)
                  lhs))
  :hints (("Goal" :induct (cdr-induction x))))



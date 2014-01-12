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
(include-book "basic")
(include-book "basic-bldrs")
(include-book "update-clause-iff-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Clause cleaning.
;;
;; In this file, we introduce a function to clean up clause lists in some
;; trivial ways:
;;
;;   1. We eliminate double negation from the tops of literals,
;;   2. We standardize all not-variants to (not guts),
;;   3. We eliminate any clauses with "obvious" literals,
;;   4. We eliminate any clauses with complementary literals,
;;   5. We remove any "absurd" literals from each clause,
;;   6. We remove any duplicate literals within each clause, and
;;   7. We eliminate any "subsumed" clauses from the list.
;;
;; This process will generate a new list of clauses which should be nicer to
;; look at and perhaps easier to prove.  Given proofs of these resulting
;; clauses, we can create proofs of the original clauses using our cleanup
;; builder.
;;
;; Eliminating double negation is useful because it allows us to identify more
;; literals as obvious, complementary, or absurd.  It also is nicer to look at
;; clauses which don't have terms like (not (not x)).
;;
;; Standardizing not variants such as (if x t nil) to (not x) allows us to more
;; easily search for complementary literals and gives a clenaer presentation to
;; the reader.
;;
;; Each literal in the clause stands for the formula L != nil.  If a literal is
;; a constant, or if it is negative and its guts are a constant as in (NOT 3)
;; or (EQUAL 5 NIL), then we can immediately tell if this formula will be
;; valid.
;;
;;   Example: 3 and (NOT NIL) are "obvious" since 3 != NIL and (NOT NIL) != NIL
;;            are clearly true.
;;
;;   Example: NIL and (NOT 5) are "absurd" since NIL != NIL and (NOT 5) != NIL
;;            are clearly false.
;;
;; Obvious literals are useful since finding one will immediately let us prove
;; the clause: all we need to do is build a proof of L != nil, then expand this
;; proof with the formulas for the other literals.  This is even efficient;
;; it's just multi-expansion.
;;
;; Complementary literals, i.e., x and (not x), are useful because we can
;; immediately prove any clause containing them, since we know that one of x or
;; (not x) must hold.
;;
;; Absurd literals are useless in the sense that they are false, and we can
;; only prove A v FALSE when we can prove A.  By removing these literals from
;; each clause, we can reduce the amount that our users and clause processing
;; routines need to look at, which seems like progress.
;;
;; Duplicate literals are also useless since we can prove A v A exactly when we
;; can prove A.  As with absurd literals, we remove duplicates from each clause
;; so that we don't need to look at so many literals.
;;
;; A clause "subsumes" any of its supersets, e.g., A v B subsumes A v B v C.
;; Recall that a clause list represents a list of goals we are trying to prove,
;; so if both of these clauses appear in our list, we only need to prove A v B
;; since A v B implies A v B v C.  We therefore throw away any supersets we
;; find, which also has the effect of reoving duplicate clauses.



(local (defthm split-up-list-of-quoted-nil
          ;; We normally don't break up constants, but this one gets in the way if we don't.
          (equal (equal x '('nil))
                 (and (consp x)
                      (equal (car x) ''nil)
                      (not (cdr x))))))




(definlined clause.simple-negativep (x)
  ;; We say a term of the form (not foo) is a "simple negative term".  These
  ;; will come into play in a useful optimization later on.
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (equal (logic.function-name x) 'not)
       (equal (len (logic.function-args x)) 1)))

(definlined clause.simple-negative-guts (x)
  ;; Given a simple negative term, say (not foo), we call "foo" the guts of
  ;; the term.
  (declare (xargs :guard (and (logic.termp x)
                              (clause.simple-negativep x))
                  :guard-hints (("Goal" :in-theory (enable clause.simple-negativep)))))
  (first (logic.function-args x)))

(defthm booleanp-of-clause.simple-negativep
  (equal (booleanp (clause.simple-negativep x))
         t)
  :hints(("Goal" :in-theory (enable clause.simple-negativep))))

(defthm forcing-logic.termp-of-clause.simple-negative-guts
  (implies (force (and (logic.termp x)
                       (clause.simple-negativep x)))
           (equal (logic.termp (clause.simple-negative-guts x))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-negativep clause.simple-negative-guts))))

(defthm forcing-logic.term-atblp-of-clause.simple-negative-guts
  (implies (force (and (logic.termp x)
                       (logic.term-atblp x atbl)
                       (clause.simple-negativep x)))
           (equal (logic.term-atblp (clause.simple-negative-guts x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-negativep clause.simple-negative-guts))))

(defthm clause.simple-negativep-of-logic.function-of-not
  (equal (clause.simple-negativep (logic.function 'not (list a)))
         t)
  :hints(("Goal" :in-theory (enable clause.simple-negativep))))

(defthm clause.negative-termp-when-clause.simple-negativep
  (implies (clause.simple-negativep x)
           (equal (clause.negative-termp x)
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-negativep
                                    clause.negative-termp))))

(defthm clause.simple-negative-guts-of-logic.function-of-not
  (equal (clause.simple-negative-guts (logic.function 'not (list a)))
         a)
  :hints(("Goal" :in-theory (enable clause.simple-negative-guts))))

(defthm clause.simple-negative-guts-identity
  (implies (and (clause.simple-negativep x)
                (force (logic.termp x)))
           (equal (logic.function 'not (list (clause.simple-negative-guts x)))
                  x))
  :hints(("Goal" :in-theory (enable clause.simple-negativep
                                    clause.simple-negative-guts))))

(defthm forcing-clause.simple-negative-guts-under-iff
  (implies (force (and (clause.simple-negativep x)
                       (logic.termp x)))
           (iff (clause.simple-negative-guts x)
                t))
  :hints(("Goal" :in-theory (enable clause.simple-negative-guts
                                    clause.simple-negativep))))



(defund clause.double-negative-free-listp (x)
  ;; We say a list of terms is double-negative free if it has no terms of
  ;; the form (not (not x)).
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (and (or (not (clause.simple-negativep (car x)))
               (not (clause.simple-negativep (clause.simple-negative-guts (car x)))))
           (clause.double-negative-free-listp (cdr x)))
    t))

(defthm clause.double-negative-free-listp-when-not-consp
  (implies (not (consp x))
           (equal (clause.double-negative-free-listp x)
                  t))
  :hints(("Goal" :in-theory (enable clause.double-negative-free-listp))))

(defthm clause.double-negative-free-listp-of-cons
  (equal (clause.double-negative-free-listp (cons a x))
         (and (or (not (clause.simple-negativep a))
                  (not (clause.simple-negativep (clause.simple-negative-guts a))))
              (clause.double-negative-free-listp x)))
  :hints(("Goal" :in-theory (enable clause.double-negative-free-listp))))

(defthm booleanp-of-clause.double-negative-free-listp
  (equal (booleanp (clause.double-negative-free-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.double-negative-free-listp-of-list-fix
  (equal (clause.double-negative-free-listp (list-fix x))
         (clause.double-negative-free-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.double-negative-free-listp-of-app
  (equal (clause.double-negative-free-listp (app x y))
         (and (clause.double-negative-free-listp x)
              (clause.double-negative-free-listp y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.double-negative-free-listp-of-rev
  (equal (clause.double-negative-free-listp (rev x))
         (clause.double-negative-free-listp x))
  :hints(("Goal" :induct (cdr-induction x))))




(definlined clause.normalize-nots-term (x)
  ;; We only apply to the "top" of a term.  We eliminate any double negation,
  ;; and also standardize the term, if it is negative, to (not guts).
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (let ((guts (clause.negative-term-guts x)))
        (if (clause.negative-termp guts)
            (clause.normalize-nots-term (clause.negative-term-guts guts))
          (logic.function 'not (list guts))))
    x))

(defthm forcing-logic.termp-of-clause.normalize-nots-term
  (implies (force (logic.termp x))
           (equal (logic.termp (clause.normalize-nots-term x))
                  t))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-term))))

(defthm forcing-logic.term-atblp-of-clause.normalize-nots-term
  (implies (force (and (logic.termp x)
                       (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-atblp (clause.normalize-nots-term x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-term))))

(defthm no-double-negatives-after-clause.normalize-nots-term
  (implies (clause.simple-negativep (clause.normalize-nots-term x))
           (equal (clause.simple-negativep
                   (clause.simple-negative-guts
                    (clause.normalize-nots-term x)))
                  nil))
  :hints(("Goal" :in-theory (enable clause.normalize-nots-term))))





(defund@ clause.normalize-nots-term-bldr (a)
  ;; Prove (iff a (clause.normalize-nots-term a)) = t
  (declare (xargs :guard (logic.termp a)
                  :verify-guards nil))
  (if (not (clause.negative-termp a))
      ;; A is positive; no cancellation.
      (@derive ((= (iff a a) t)                                     (build.iff-reflexivity a)))
    (let ((guts (clause.negative-term-guts a)))
      (if (not (clause.negative-termp guts))
          ;; A has positive guts; we normalize it.
          (@derive ((= a (not guts))                                (clause.standardize-negative-term-bldr a))
                   ((= (iff a (not guts)) t)                        (build.iff-from-pequal @-)))
        (let ((guts-prime (clause.negative-term-guts guts)))
          ;; A has the form (not guts) or some variant of this
          ;; Guts has the from (not guts') or some variant of this
          (@derive ((= a (not (not guts-prime)))                    (clause.standardize-double-negative-term-bldr a))
                   ((= (iff a (not (not guts-prime))) t)            (build.iff-from-pequal @-)                               *1)
                   ;; ---
                   ((= (iff (not (not x)) x) t)                     (build.theorem (theorem-not-of-not-under-iff)))
                   ((= (iff (not (not guts-prime)) guts-prime) t)   (build.instantiation @- (list (cons 'x guts-prime))))
                   ((= (iff a guts-prime) t)                        (build.transitivity-of-iff *1 @-))
                   ((= (iff guts-prime result) t)                   (clause.normalize-nots-term-bldr guts-prime))
                   ((= (iff a result) t)                            (build.transitivity-of-iff @-- @-))))))))

(defobligations clause.normalize-nots-term-bldr
  (build.iff-reflexivity clause.standardize-negative-term-bldr
   build.iff-from-pequal clause.standardize-double-negative-term-bldr
   build.instantiation   build.transitivity-of-iff)
  :extra-thms ((theorem-not-of-not-under-iff)))

(encapsulate
 ()
 (local (in-theory (enable clause.normalize-nots-term-bldr
                           clause.normalize-nots-term
                           theorem-not-of-not-under-iff)))

 (local (defthm crock
          (implies (not (cdr (cdr x)))
                   (equal (equal (len x) 2)
                          (and (consp x)
                               (consp (cdr x)))))))

 (local (defthm lemma
          (implies (logic.termp a)
                   (and (logic.appealp (clause.normalize-nots-term-bldr a))
                        (equal (logic.conclusion (clause.normalize-nots-term-bldr a))
                               (logic.pequal (logic.function 'iff (list a (clause.normalize-nots-term a)))
                                             ''t))))))

 (defthm forcing-logic.appealp-of-clause.normalize-nots-term-bldr
   (implies (force (logic.termp a))
            (equal (logic.appealp (clause.normalize-nots-term-bldr a))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.normalize-nots-term-bldr
   (implies (force (logic.termp a))
            (equal (logic.conclusion (clause.normalize-nots-term-bldr a))
                   (logic.pequal (logic.function 'iff (list a (clause.normalize-nots-term a)))
                                 ''t))))

 (verify-guards clause.normalize-nots-term-bldr)

 (defthm@ forcing-logic.proofp-of-clause.normalize-nots-term-bldr
   (implies (force (and (logic.termp a)
                        ;; ---
                        (logic.term-atblp a atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.normalize-nots-term-bldr)))
            (equal (logic.proofp (clause.normalize-nots-term-bldr a) axioms thms atbl)
                   t))))




(defprojection :list (clause.normalize-nots-term-list x)
               :element (clause.normalize-nots-term x)
               :guard (logic.term-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-clause.normalize-nots-term-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (clause.normalize-nots-term-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-clause.normalize-nots-term-list
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-atblp (clause.normalize-nots-term-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.double-negative-free-listp-of-clause.normalize-nots-term-list
  (equal (clause.double-negative-free-listp
          (clause.normalize-nots-term-list x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))



(defprojection :list (clause.normalize-nots-term-list-bldr x)
               :element (clause.normalize-nots-term-bldr x)
               :guard (logic.term-listp x))

(defobligations clause.normalize-nots-term-list-bldr
  (clause.normalize-nots-term-bldr))

(defthm forcing-logic.appeal-listp-of-clause.normalize-nots-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.appeal-listp (clause.normalize-nots-term-list-bldr x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-conclusions-of-clause.normalize-nots-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.strip-conclusions (clause.normalize-nots-term-list-bldr x))
                  (logic.pequal-list
                   (logic.function-list 'iff (list2-list x (clause.normalize-nots-term-list x)))
                   (repeat ''t (len x)))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm@ forcing-logic.proof-listp-of-clause.normalize-nots-term-list-bldr
  (implies (force (and (logic.term-listp x)
                       ;; ---
                       (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (@obligations clause.normalize-nots-term-list-bldr)))
           (equal (logic.proof-listp (clause.normalize-nots-term-list-bldr x) axioms thms atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))





(defprojection :list (clause.normalize-nots-clauses x)
               :element (clause.normalize-nots-term-list x)
               :guard (logic.term-list-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-list-listp-of-clause.normalize-nots-clauses
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (clause.normalize-nots-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-clause.normalize-nots-clauses
  (implies (force (and (logic.term-list-listp x)
                       (logic.term-list-list-atblp x atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-list-atblp (clause.normalize-nots-clauses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-clause.normalize-nots-clauses
  (equal (cons-listp (clause.normalize-nots-clauses x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))


(defund clause.normalize-nots-clauses-bldr (x proofs)
  ;; Given a list of clauses, x, and proofs of all the clauses obtained by
  ;; undoublenegating x, we build proofs of each clause in x.
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (clause.normalize-nots-clauses x))))))
  (if (consp x)
      (let ((cancelled (clause.normalize-nots-term-list (car x)))
            (t-proofs  (clause.normalize-nots-term-list-bldr (car x))))
        (cons (clause.update-clause-iff-bldr cancelled (car proofs) t-proofs)
              (clause.normalize-nots-clauses-bldr (cdr x) (cdr proofs))))
    nil))

(defobligations clause.normalize-nots-clauses-bldr
  (clause.normalize-nots-term-list-bldr
   clause.update-clause-iff-bldr))

(encapsulate
 ()
 (in-theory (enable clause.normalize-nots-clauses-bldr))

 (defthm forcing-logic.appeal-listp-of-clause.normalize-nots-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.normalize-nots-clauses x)))))
            (equal (logic.appeal-listp (clause.normalize-nots-clauses-bldr x proofs))
                   t))
   :hints(("Goal" :induct (cdr-cdr-induction x proofs))))

 (defthm forcing-logic.strip-conclusions-of-clause.normalize-nots-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.normalize-nots-clauses x)))))
            (equal (logic.strip-conclusions (clause.normalize-nots-clauses-bldr x proofs))
                   (clause.clause-list-formulas x)))
   :hints(("Goal" :induct (cdr-cdr-induction x proofs))))

 (defthm@ forcing-logic.proof-listp-of-clause.normalize-nots-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.normalize-nots-clauses x)))
                        ;; ---
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.term-list-list-atblp x atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.normalize-nots-clauses-bldr)))
            (equal (logic.proof-listp (clause.normalize-nots-clauses-bldr x proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :induct (cdr-cdr-induction x proofs)))))




(definlined clause.obvious-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (equal (clause.negative-term-guts x) ''nil)
    (and (logic.constantp x)
         (not (equal x ''nil)))))

(defthm booleanp-of-clause.obvious-termp
  (equal (booleanp (clause.obvious-termp x))
         t)
  :hints(("Goal" :in-theory (enable clause.obvious-termp))))




(defund@ clause.obvious-term-bldr (x)
  ;; Prove the formula for an obvious term
  (declare (xargs :guard (and (logic.termp x)
                              (clause.obvious-termp x))
                  :guard-hints (("Goal" :in-theory (enable clause.obvious-termp
                                                           clause.negative-termp
                                                           clause.negative-term-guts
                                                           theorem-if-redux-nil
                                                           definition-of-not)))))
  (if (clause.negative-termp x)
      ;; A negative term is obvious when its guts are nil.
      (let ((name (logic.function-name x)))
        (cond ((equal name 'not)
               ;; (not guts) --> goal is (not nil) != nil
               (@derive ((= (not x) (if x nil t))     (build.axiom (definition-of-not)))
                        ((= (not nil) (if nil nil t)) (build.instantiation @- (@sigma (x . nil)))     *1)
                        ((= (if nil y z) z)           (build.theorem (theorem-if-redux-nil)))
                        ((= (if nil nil t) t)         (build.instantiation @- (@sigma (y . nil) (z . t))))
                        ((= (not nil) t)              (build.transitivity-of-pequal *1 @-))
                        ((!= (not nil) nil)           (build.not-nil-from-t @-))))
              ((equal name 'if)
               ;; (if guts nil t) --> goal is (if nil nil t) != nil
               (@derive ((= (if nil y z) z)           (build.theorem (theorem-if-redux-nil)))
                        ((= (if nil nil t) t)         (build.instantiation @- (@sigma (y . nil) (z . t))))
                        ((!= (if nil nil t) t)        (build.not-nil-from-t @-))))
              ((equal name 'equal)
               ;; (equal nil guts) --> goal is (equal nil nil) != nil
               ;; (equal guts nil) --> goal is (equal nil nil) != nil
               (@derive ((= (equal nil nil) t)        (build.equal-reflexivity ''nil))
                        ((!= (equal nil nil) nil)     (build.not-nil-from-t @-))))
              (t
               ;; (iff nil guts) --> goal is (iff nil nil) != nil
               ;; (iff guts nil) --> goal is (iff nil nil) != nil
               (@derive ((= (iff nil nil) t)          (build.iff-reflexivity ''nil))
                        ((!= (iff nil nil) t)         (build.not-nil-from-t @-))))))
    ;; A positive term is obvious when it is a non-nil constant.
    (@derive ((!= x nil)                              (build.not-pequal-constants x ''nil)))))

(defobligations clause.obvious-term-bldr
  (build.instantiation build.transitivity-of-pequal build.not-nil-from-t
   build.equal-reflexivity build.iff-reflexivity build.not-pequal-constants)
  :extra-axioms ((definition-of-not))
  :extra-thms ((theorem-if-redux-nil)))

(encapsulate
 ()
 (local (in-theory (enable clause.obvious-term-bldr
                           clause.obvious-termp
                           clause.negative-termp
                           clause.negative-term-guts
                           logic.term-formula
                           theorem-if-redux-nil
                           definition-of-not)))

 (defthm clause.obvious-term-bldr-under-iff
   (iff (clause.obvious-term-bldr x)
        t))

 (defthm forcing-logic.appealp-of-clause.obvious-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.obvious-termp x)))
            (equal (logic.appealp (clause.obvious-term-bldr x))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.obvious-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.obvious-termp x)))
            (equal (logic.conclusion (clause.obvious-term-bldr x))
                   (logic.term-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.obvious-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.obvious-termp x)
                        ;; ---
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.obvious-term-bldr)))
            (equal (logic.proofp (clause.obvious-term-bldr x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (disable forcing-lookup-of-logic.function-name-free)))))



(defund clause.obvious-term-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.obvious-term-bldr)
         (equal (logic.fmtype conclusion) 'pnot*)
         (equal (logic.fmtype (logic.~arg conclusion)) 'pequal*)
         (equal (logic.=rhs (logic.~arg conclusion)) ''nil)
         (clause.obvious-termp (logic.=lhs (logic.~arg conclusion)))
         (logic.term-atblp (logic.=lhs (logic.~arg conclusion)) atbl)
         (not subproofs)
         (not extras))))

(defund clause.obvious-term-bldr-high (x)
  (declare (xargs :guard (and (logic.termp x)
                              (clause.obvious-termp x))))
  (logic.appeal 'clause.obvious-term-bldr
                (logic.term-formula x)
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable clause.obvious-term-bldr-okp logic.term-formula)))

 (defthm booleanp-of-clause.obvious-term-bldr-okp
   (equal (booleanp (clause.obvious-term-bldr-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.obvious-term-bldr-okp-of-logic.appeal-identity
   (equal (clause.obvious-term-bldr-okp (logic.appeal-identity x) atbl)
          (clause.obvious-term-bldr-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthmd lemma-1-for-soundness-of-clause.obvious-term-bldr-okp
   (implies (and (clause.obvious-term-bldr-okp x atbl)
                 (force (logic.appealp x)))
            (equal (logic.conclusion (clause.obvious-term-bldr (logic.=lhs (logic.~arg (logic.conclusion x)))))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.obvious-term-bldr-okp
   (implies (and (clause.obvious-term-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (@obligations clause.obvious-term-bldr)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.proofp (clause.obvious-term-bldr (logic.=lhs (logic.~arg (logic.conclusion x))))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.obvious-term-bldr-okp
   (implies (and (clause.obvious-term-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.obvious-term-bldr)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.obvious-term-bldr-okp
                               lemma-2-for-soundness-of-clause.obvious-term-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.obvious-term-bldr (logic.=lhs (logic.~arg (logic.conclusion x)))))))))))






(defund clause.find-obvious-term (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (clause.obvious-termp (car x))
          (car x)
        (clause.find-obvious-term (cdr x)))
    nil))

(encapsulate
 ()
 (defthm clause.find-obvious-term-when-not-consp
   (implies (not (consp x))
            (equal (clause.find-obvious-term x)
                   nil))
   :hints(("Goal" :in-theory (enable clause.find-obvious-term))))

 (defthm clause.find-obvious-term-of-cons
   (equal (clause.find-obvious-term (cons a x))
          (if (clause.obvious-termp a)
              a
            (clause.find-obvious-term x)))
   :hints(("Goal" :in-theory (enable clause.find-obvious-term))))

 (defthm clause.find-obvious-term-of-list-fix
   (equal (clause.find-obvious-term (list-fix x))
          (clause.find-obvious-term x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.find-obvious-term-of-app
   (equal (clause.find-obvious-term (app x y))
          (or (clause.find-obvious-term x)
              (clause.find-obvious-term y)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.find-obvious-term-of-rev-under-iff
   (iff (clause.find-obvious-term (rev x))
        (clause.find-obvious-term x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-memberp-of-clause.find-obvious-term
   (implies (force (logic.term-listp x))
            (equal (memberp (clause.find-obvious-term x) x)
                   (if (clause.find-obvious-term x)
                       t
                     nil)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm logic.termp-of-clause.find-obvious-term
   (implies (and (clause.find-obvious-term x)
                 (force (logic.term-listp x)))
            (equal (logic.termp (clause.find-obvious-term x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.obvious-termp-of-clause.find-obvious-term
   (implies (clause.find-obvious-term x)
            (equal (clause.obvious-termp (clause.find-obvious-term x))
                   t))
   :hints(("Goal" :induct (cdr-induction x)))))




(defund clause.remove-obvious-clauses (x)
  (declare (xargs :guard (logic.term-list-listp x)))
  (if (consp x)
      (if (clause.find-obvious-term (car x))
          (clause.remove-obvious-clauses (cdr x))
        (cons (car x) (clause.remove-obvious-clauses (cdr x))))
    nil))

(encapsulate
 ()
 (defthm clause.remove-obvious-clauses-when-not-consp
   (implies (not (consp x))
            (equal (clause.remove-obvious-clauses x)
                   nil))
   :hints(("Goal" :in-theory (enable clause.remove-obvious-clauses))))

 (defthm clause.remove-obvious-clauses-of-cons
   (equal (clause.remove-obvious-clauses (cons a x))
          (if (clause.find-obvious-term a)
              (clause.remove-obvious-clauses x)
            (cons a (clause.remove-obvious-clauses x))))
   :hints(("Goal" :in-theory (enable clause.remove-obvious-clauses))))

 (defthm true-listp-of-clause.remove-obvious-clauses
   (equal (true-listp (clause.remove-obvious-clauses x))
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.remove-obvious-clauses-of-list-fix
   (equal (clause.remove-obvious-clauses (list-fix x))
          (clause.remove-obvious-clauses x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.remove-obvious-clauses-of-app
   (equal (clause.remove-obvious-clauses (app x y))
          (app (clause.remove-obvious-clauses x)
               (clause.remove-obvious-clauses y)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm rev-of-clause.remove-obvious-clauses
   (equal (rev (clause.remove-obvious-clauses x))
          (clause.remove-obvious-clauses (rev x)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthmd clause.remove-obvious-clauses-of-rev
   (equal (clause.remove-obvious-clauses (rev x))
          (rev (clause.remove-obvious-clauses x))))

 (ACL2::theory-invariant (ACL2::incompatible (:rewrite rev-of-clause.remove-obvious-clauses)
                                             (:rewrite clause.remove-obvious-clauses-of-rev)))

 (defthm subsetp-of-clause.remove-obvious-clauses
   (equal (subsetp (clause.remove-obvious-clauses x) x)
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-logic.term-list-listp-of-clause.remove-obvious-clauses
   (implies (force (logic.term-list-listp x))
            (equal (logic.term-list-listp (clause.remove-obvious-clauses x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-logic.term-list-list-atblp-of-clause.remove-obvious-clauses
   (implies (force (logic.term-list-list-atblp x atbl))
            (equal (logic.term-list-list-atblp (clause.remove-obvious-clauses x) atbl)
                   t))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm cons-listp-of-clause.remove-obvious-clauses
   (equal (cons-listp (clause.remove-obvious-clauses x))
          (cons-listp x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm all-superset-of-somep-of-clause.remove-obvious-clauses
   (equal (all-superset-of-somep (clause.remove-obvious-clauses x) x)
          t)
   :hints(("Goal" :induct (cdr-induction x)))))


(defund clause.remove-obvious-clauses-bldr (x proofs)
   ;; Suppose x is a list of clauses, and that after removing the obvious
   ;; clauses you are left with x'.  Suppose we have proofs of each clause in
   ;; x'.  Then, this function will construct proofs of each clause in x, by
   ;; filling in the proofs of the obvious clauses.
   (declare (xargs :guard (and (logic.term-list-listp x)
                               (cons-listp x)
                               (logic.appeal-listp proofs)
                               (equal (clause.clause-list-formulas (clause.remove-obvious-clauses x))
                                      (logic.strip-conclusions proofs)))))
   (if (consp x)
       (let* ((clause1 (car x))
              (obvious (clause.find-obvious-term clause1)))
         (if obvious
             ;; We need to fill in the proof of this clause.
             (let* ((term-proof   (clause.obvious-term-bldr obvious))
                    (clause-proof (build.multi-expansion term-proof (logic.term-list-formulas clause1))))
               (cons clause-proof
                     (clause.remove-obvious-clauses-bldr (cdr x) proofs)))
           ;; Else we can just reuse the given proof of this clause.
           (cons (car proofs)
                 (clause.remove-obvious-clauses-bldr (cdr x) (cdr proofs)))))
     nil))

(defobligations clause.remove-obvious-clauses-bldr
  (clause.obvious-term-bldr build.multi-expansion))

(encapsulate
 ()
 (local (in-theory (enable clause.remove-obvious-clauses-bldr)))

 (defthm forcing-logic.appeal-listp-of-clause.remove-obvious-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.remove-obvious-clauses x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (clause.remove-obvious-clauses-bldr x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-clause.remove-obvious-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.remove-obvious-clauses x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (clause.remove-obvious-clauses-bldr x proofs))
                   (clause.clause-list-formulas x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-clause.remove-obvious-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.remove-obvious-clauses x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-list-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.remove-obvious-clauses-bldr)))
            (equal (logic.proof-listp (clause.remove-obvious-clauses-bldr x proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable clause.remove-obvious-clauses-bldr)))))




(defund clause.complement-term (a)
  (declare (xargs :guard (logic.termp a)))
  (if (clause.simple-negativep a)
      (clause.simple-negative-guts a)
    (logic.function 'not (list a))))

(defthm logic.termp-of-clause.complement-term
  (implies (force (logic.termp a))
           (equal (logic.termp (clause.complement-term a))
                  t))
  :hints(("Goal" :in-theory (enable clause.complement-term))))

(defthm clause.complement-term-of-clause.complement-term
  (implies (and (force (logic.termp a))
                (or (not (clause.simple-negativep a))
                    (not (clause.simple-negativep (clause.simple-negative-guts a)))))
           (equal (clause.complement-term (clause.complement-term a))
                  a))
  :hints(("Goal" :in-theory (enable clause.complement-term))))



(defund clause.find-complementary-literal (x)
  ;; Returns nil on failure, or else returns a term a from x such that (not a)
  ;; is also in x.
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (memberp (clause.complement-term (car x)) (cdr x))
          (car x)
        (clause.find-complementary-literal (cdr x)))
    nil))

(defthm clause.find-complementary-literal-when-not-consp
  (implies (not (consp x))
           (equal (clause.find-complementary-literal x)
                  nil))
  :hints(("Goal" :in-theory (enable clause.find-complementary-literal))))

(defthm clause.find-complementary-literal-of-cons
  (equal (clause.find-complementary-literal (cons a x))
         (if (memberp (clause.complement-term a) x)
             a
           (clause.find-complementary-literal x)))
  :hints(("Goal" :in-theory (enable clause.find-complementary-literal))))

(defthm forcing-memberp-of-clause.find-complementary-literal
  (implies (clause.find-complementary-literal x)
           (equal (memberp (clause.find-complementary-literal x) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-memberp-of-not-of-clause.find-complementary-literal
  (implies (clause.find-complementary-literal x)
           (equal (memberp (clause.complement-term (clause.find-complementary-literal x)) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.find-complementary-literal-of-list-fix
  (equal (clause.find-complementary-literal (list-fix x))
         (clause.find-complementary-literal x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-clause.find-complementary-literal-of-app-one
  (implies (and (force (logic.term-listp x))
                (force (logic.term-listp y))
                (clause.find-complementary-literal x))
           (iff (clause.find-complementary-literal (app x y))
                t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd lemma-for-clause.find-complementary-literal-of-rev
  (implies (and (logic.term-listp x)
                (logic.termp a)
                (or (not (clause.simple-negativep a))
                    (not (clause.simple-negativep (clause.simple-negative-guts a))))
                (clause.double-negative-free-listp x))
           (iff (clause.find-complementary-literal (app x (list a)))
                (or (clause.find-complementary-literal x)
                    (memberp (clause.complement-term a) x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.find-complementary-literal-of-rev
  (implies (and (logic.term-listp x)
                (clause.double-negative-free-listp x)
                )
           (iff (clause.find-complementary-literal (rev x))
                (clause.find-complementary-literal x)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable lemma-for-clause.find-complementary-literal-of-rev))))




(defund clause.remove-complement-clauses (x)
  (declare (xargs :guard (logic.term-list-listp x)))
  (if (consp x)
      (if (clause.find-complementary-literal (car x))
          (clause.remove-complement-clauses (cdr x))
        (cons (car x) (clause.remove-complement-clauses (cdr x))))
    nil))

(defthm clause.remove-complement-clauses-when-not-consp
  (implies (not (consp x))
           (equal (clause.remove-complement-clauses x)
                  nil))
  :hints(("Goal" :in-theory (enable clause.remove-complement-clauses))))

(defthm clause.remove-complement-clauses-of-cons
  (equal (clause.remove-complement-clauses (cons a x))
         (if (clause.find-complementary-literal a)
             (clause.remove-complement-clauses x)
           (cons a (clause.remove-complement-clauses x))))
  :hints(("Goal" :in-theory (enable clause.remove-complement-clauses))))

(defthm forcing-logic.term-list-listp-of-clause.remove-complement-clauses
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (clause.remove-complement-clauses x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-clause.remove-complement-clauses
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.term-list-list-atblp (clause.remove-complement-clauses x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-clause.remove-complement-clauses
  (equal (cons-listp (clause.remove-complement-clauses x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm true-listp-of-clause.remove-complement-clauses
  (equal (true-listp (clause.remove-complement-clauses x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.remove-complement-clauses-of-list-fix
  (equal (clause.remove-complement-clauses (list-fix x))
         (clause.remove-complement-clauses x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.remove-complement-clauses-of-app
  (equal (clause.remove-complement-clauses (app x y))
         (app (clause.remove-complement-clauses x)
              (clause.remove-complement-clauses y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm rev-of-clause.remove-complement-clauses
  (equal (rev (clause.remove-complement-clauses x))
         (clause.remove-complement-clauses (rev x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthmd clause.remove-complement-clauses-of-rev
  (equal (clause.remove-complement-clauses (rev x))
         (rev (clause.remove-complement-clauses x))))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite rev-of-clause.remove-complement-clauses)
                                            (:rewrite clause.remove-complement-clauses-of-rev)))





(defund@ clause.complement-clause-bldr (a x)
  (declare (xargs :guard (and (logic.termp a)
                              (logic.term-listp x)
                              (memberp a x)
                              (memberp (clause.complement-term a) x))
                  :guard-hints (("Goal" :in-theory (enable theorem-not-when-nil
                                                           clause.complement-term)))))
  (let ((guts (if (clause.simple-negativep a)
                  (clause.simple-negative-guts a)
                a)))
    (@derive ((v (!= x nil) (= (not x) t))     (build.theorem (theorem-not-when-nil)))
             ((v (!= x nil) (!= (not x) nil))  (build.disjoined-not-nil-from-t @-))
             ((v (!= a nil) (!= (not a) nil))  (build.instantiation @- (list (cons 'x guts))))
             (goal                             (build.multi-or-expansion @- (logic.term-list-formulas x))))))

(defobligations clause.complement-clause-bldr
  (build.disjoined-not-nil-from-t build.instantiation build.multi-or-expansion)
  :extra-thms ((theorem-not-when-nil)))

(encapsulate
 ()
 (local (in-theory (enable clause.complement-clause-bldr
                           clause.complement-term
                           theorem-not-when-nil)))

 (defthm forcing-logic.appealp-of-clause.complement-clause-bldr
   (implies (force (and (logic.termp a)
                        (logic.term-listp x)
                        (memberp a x)
                        (memberp (clause.complement-term a) x)))
            (equal (logic.appealp (clause.complement-clause-bldr a x))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.complement-clause-bldr
   (implies (force (and (logic.termp a)
                        (logic.term-listp x)
                        (memberp a x)
                        (memberp (clause.complement-term a) x)))
            (equal (logic.conclusion (clause.complement-clause-bldr a x))
                   (clause.clause-formula x))))

 (defthm@ forcing-logic.proofp-of-clause.complement-clause-bldr
   (implies (force (and (logic.termp a)
                        (logic.term-listp x)
                        (memberp a x)
                        (memberp (clause.complement-term a) x)
                        ;; ---
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.term-list-atblp x atbl)
                        (@obligations clause.complement-clause-bldr)))
            (equal (logic.proofp (clause.complement-clause-bldr a x) axioms thms atbl)
                   t))))



(defund@ clause.remove-complement-clauses-bldr (x proofs)
  ;; Suppose x is a list of clauses and proofs establish every clause after
  ;; removing the complement clauses from x.  Then, we prove the clauses in x.
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (clause.remove-complement-clauses x))))))
  (if (consp x)
      (let* ((clause1 (car x))
             (literal (clause.find-complementary-literal clause1)))
        (if literal
            (cons
             (clause.complement-clause-bldr literal clause1)
             (clause.remove-complement-clauses-bldr (cdr x) proofs))
          ;; Else, we just reuse the proof.
          (cons (car proofs)
                (clause.remove-complement-clauses-bldr (cdr x) (cdr proofs)))))
    nil))

(defobligations clause.remove-complement-clauses-bldr
  (clause.complement-clause-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.remove-complement-clauses
                           clause.remove-complement-clauses-bldr)))

 (defthm forcing-logic.appeal-listp-of-clause.remove-complement-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.remove-complement-clauses x)))))
            (equal (logic.appeal-listp (clause.remove-complement-clauses-bldr x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-clause.remove-complement-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.remove-complement-clauses x)))))
            (equal (logic.strip-conclusions (clause.remove-complement-clauses-bldr x proofs))
                   (clause.clause-list-formulas x))))

 (defthm@ forcing-logic.proof-listp-of-clause.remove-complement-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.remove-complement-clauses x)))
                        ;; ---
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.term-list-list-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations clause.remove-complement-clauses-bldr)))
            (equal (logic.proof-listp (clause.remove-complement-clauses-bldr x proofs) axioms thms atbl)
                   t))))




(definlined clause.absurd-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (let ((guts (clause.negative-term-guts x)))
        (and (logic.constantp guts)
             (not (equal guts ''nil))))
    (equal x ''nil)))

(defthm booleanp-of-clause.absurd-termp
  (equal (booleanp (clause.absurd-termp x))
         t)
  :hints(("Goal" :in-theory (enable clause.absurd-termp))))



(defund clause.remove-absurd-terms-from-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (clause.absurd-termp (car x))
          (clause.remove-absurd-terms-from-list (cdr x))
        (cons (car x) (clause.remove-absurd-terms-from-list (cdr x))))
    nil))

(encapsulate
 ()
 (defthm clause.remove-absurd-terms-from-list-when-not-consp
   (implies (not (consp x))
            (equal (clause.remove-absurd-terms-from-list x)
                   nil))
   :hints(("Goal" :in-theory (enable clause.remove-absurd-terms-from-list))))

 (defthm clause.remove-absurd-terms-from-list-of-cons
   (equal (clause.remove-absurd-terms-from-list (cons a x))
          (if (clause.absurd-termp a)
              (clause.remove-absurd-terms-from-list x)
            (cons a (clause.remove-absurd-terms-from-list x))))
   :hints(("Goal" :in-theory (enable clause.remove-absurd-terms-from-list))))

 (defthm true-listp-of-clause.remove-absurd-terms-from-list
   (equal (true-listp (clause.remove-absurd-terms-from-list x))
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.remove-absurd-terms-from-list-of-list-fix
   (equal (clause.remove-absurd-terms-from-list (list-fix x))
          (clause.remove-absurd-terms-from-list x))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm clause.remove-absurd-terms-from-list-of-app
   (equal (clause.remove-absurd-terms-from-list (app x y))
          (app (clause.remove-absurd-terms-from-list x)
               (clause.remove-absurd-terms-from-list y)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm rev-of-clause.remove-absurd-terms-from-list
   (equal (rev (clause.remove-absurd-terms-from-list x))
          (clause.remove-absurd-terms-from-list (rev x)))
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm subsetp-of-clause.remove-absurd-terms-from-list
   (equal (subsetp (clause.remove-absurd-terms-from-list x) x)
          t)
   :hints(("Goal" :induct (cdr-induction x))))

 (defthm forcing-logic.term-listp-of-clause.remove-absurd-terms-from-list
   (implies (force (logic.term-listp x))
            (equal (logic.term-listp (clause.remove-absurd-terms-from-list x))
                   t))
   :hints(("Goal" :induct (cdr-induction x)))))






(defprojection :list (clause.remove-absurd-terms-from-clauses x)
               :element (clause.remove-absurd-terms-from-list x)
               :guard (logic.term-list-listp x)
               :nil-preservingp t)

(defthm all-superset-of-somep-of-clause.remove-absurd-terms-from-clauses
  (equal (all-superset-of-somep x (clause.remove-absurd-terms-from-clauses x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-subset-of-somep-of-clause.remove-absurd-terms-from-clauses
  (equal (all-subset-of-somep (clause.remove-absurd-terms-from-clauses x) x)
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-clause.remove-absurd-terms-from-clauses
   (implies (force (logic.term-list-listp x))
            (equal (logic.term-list-listp (clause.remove-absurd-terms-from-clauses x))
                   t))
   :hints(("Goal" :induct (cdr-induction x))))




(definlined disabled-equal (x y)
  (declare (xargs :guard t))
  (equal x y))



(defund clause.clean-clauses (x)
  ;; We produce the 3-tuple (unprovablep progressp x'), where:
  ;;
  ;;  - Unprovablep is set if some clause is discovered to be absurd,
  ;;  - Progressp is set if we have been able to improve some clause, and
  ;;  - X' are the new, cleaned clauses or a copy of x if no progress has
  ;;    been made.
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (let* ((pass1 (clause.normalize-nots-clauses x))
         (pass2 (clause.remove-obvious-clauses pass1))
         (pass3 (clause.remove-complement-clauses pass2))
         (pass4 (clause.remove-absurd-terms-from-clauses pass3)))
    (if (not (cons-listp pass4))
        ;; Some clause is absurd.
        (list t nil (list-fix x))
      (let* ((pass5 (remove-duplicates-list pass4))
             (pass6 (fast-remove-supersets pass5)))
        (list nil (not (disabled-equal x pass6)) pass6)))))

(encapsulate
 ()
 (local (in-theory (enable clause.clean-clauses disabled-equal)))

 (defthm booleanp-of-first-of-clause.clean-clauses
   (equal (booleanp (first (clause.clean-clauses x)))
          t))

 (defthm booleanp-of-second-of-clause.clean-clauses
   (equal (booleanp (second (clause.clean-clauses x)))
          t))

 (defthm logic.term-list-listp-of-third-of-clause.clean-clauses
   (implies (force (logic.term-list-listp x))
            (equal (logic.term-list-listp (third (clause.clean-clauses x)))
                   t)))

 (defthm logic.cons-listp-of-third-of-clause.clean-clauses
   (implies (force (cons-listp x))
            (equal (cons-listp (third (clause.clean-clauses x)))
                   t)))

 (local (defthm true-listp-of-remove-supersets-free
          (implies (equal (remove-supersets x) y)
                   (equal (true-listp y)
                          t))))

 (defthm true-listp-of-third-of-clause.clean-clauses
   (equal (true-listp (third (clause.clean-clauses x)))
          t)))



(defund clause.clean-clauses-bldr (x proofs)
  ;; Suppose that x is a list of clauses and we apply clean-clauses to
  ;; produce x', and suppose that we have proofs of each clause in x'.
  ;; Then, we can apply this function to prove each clause in x.
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (third (clause.clean-clauses x)))
                                     (logic.strip-conclusions proofs)))
                  :guard-hints (("Goal" :in-theory (enable clause.clean-clauses)))))
  (let* ((pass1 (clause.normalize-nots-clauses x))
         (pass2 (clause.remove-obvious-clauses pass1))
         (pass3 (clause.remove-complement-clauses pass2))
         (pass4 (clause.remove-absurd-terms-from-clauses pass3)))
    (if (not (cons-listp pass4))
        proofs
      (let* ((pass5 (remove-duplicates-list pass4))
             (pass6 (fast-remove-supersets pass5))
             ;; Proofs establish every clause in the final pass, but passes 4-6 only removed terms from existing clauses,
             ;; so every clause in pass 3 is a superset of some clause in the final pass.
             (pass3-proofs (build.all-superset-of-some (logic.term-list-list-formulas pass3) (logic.term-list-list-formulas pass6) proofs))
             ;; We fill in the complement proofs to get to pass 2
             (pass2-proofs (clause.remove-complement-clauses-bldr pass2 pass3-proofs))
             ;; We can fill in the obvious clauses to get to pass1.
             (pass1-proofs (clause.remove-obvious-clauses-bldr pass1 pass2-proofs))
             ;; We can undo the double negation to get to x.
             (x-proofs     (clause.normalize-nots-clauses-bldr x pass1-proofs)))
        (ACL2::prog2$
         (ACL2::cw! ";; Clean step: ~s0~|"
                    (STR::ncat "Inputs " (unbounded-rank proofs) "; "
                              "Redundant/absurd " (- (unbounded-rank pass3-proofs)
                                                     (unbounded-rank proofs)) "; "
                              "Complementary " (- (unbounded-rank pass2-proofs)
                                                  (unbounded-rank pass3-proofs)) "; "
                              "Obvious " (- (unbounded-rank pass1-proofs)
                                            (unbounded-rank pass2-proofs)) "; "
                              "Normalize " (- (unbounded-rank x-proofs)
                                              (unbounded-rank pass1-proofs)) "; "
                              "Outputs " (unbounded-rank x-proofs) "."))
         x-proofs)))))

(defobligations clause.clean-clauses-bldr
  (clause.normalize-nots-clauses-bldr
   clause.remove-obvious-clauses-bldr
   clause.remove-complement-clauses-bldr
   build.all-superset-of-some ))

(encapsulate
 ()
 (local (in-theory (enable clause.clean-clauses clause.clean-clauses-bldr)))

 (defthm forcing-logic.appeal-listp-of-clause.clean-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (third (clause.clean-clauses x)))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (clause.clean-clauses-bldr x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-clause.clean-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (third (clause.clean-clauses x)))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (clause.clean-clauses-bldr x proofs))
                   (clause.clause-list-formulas x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-clause.clean-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (third (clause.clean-clauses x)))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-list-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.clean-clauses-bldr)))
            (equal (logic.proof-listp (clause.clean-clauses-bldr x proofs) axioms thms atbl)
                   t))))








;; sweet!  now can we fold in the removing duplicates as well?  hrmn.  this seems
;; to create problems because remove-duplicates does not have nice reversibility
;; properties.  that is, the element order is left up to where the elements occur
;; in the cdr.  that's actually a pretty shitty order to choose.  we might want to
;; redesign remove-duplicates to keep the first one of each element instead


(defund clause.fast-remove-absurd-terms-from-list$ (x acc)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.term-listp acc)
                              (true-listp acc))))
  (if (consp x)
      (if (clause.absurd-termp (car x))
          (clause.fast-remove-absurd-terms-from-list$ (cdr x) acc)
        (clause.fast-remove-absurd-terms-from-list$ (cdr x) (cons (car x) acc)))
    acc))

(defthm clause.fast-remove-absurd-terms-from-list$-removal
  (implies (force (true-listp acc))
           (equal (clause.fast-remove-absurd-terms-from-list$ x acc)
                  (revappend (clause.remove-absurd-terms-from-list x) acc)))
  :hints(("Goal" :in-theory (enable clause.fast-remove-absurd-terms-from-list$))))




(defund clause.fast-clean-part1 (x acc)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (if (consp x)
      (let ((normalized-clause (clause.fast-normalize-nots-term-list$ (car x) nil)))
        (if (or (clause.find-obvious-term normalized-clause)
                (clause.find-complementary-literal normalized-clause))
            (clause.fast-clean-part1 (cdr x) acc)
          (clause.fast-clean-part1 (cdr x)
                                   (cons (clause.fast-remove-absurd-terms-from-list$ normalized-clause nil)
                                         acc))))
    acc))

(defthm clause.fast-clean-part1-removal
  (implies (force (and (true-listp acc)
                       (logic.term-list-listp x)))
           (equal (clause.fast-clean-part1 x acc)
                  (revappend (clause.remove-absurd-terms-from-clauses
                              (clause.remove-complement-clauses
                               (clause.remove-obvious-clauses
                                (clause.normalize-nots-clauses x))))
                             acc)))
  :hints(("Goal"
          :in-theory (e/d (clause.fast-clean-part1
                           clause.normalize-nots-term-list-of-rev)
                          (rev-of-clause.normalize-nots-term-list
                           )))))


(defund clause.fast-clean-clauses (x)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (let ((pass4 (clause.fast-clean-part1 x nil)))
    (if (not (cons-listp pass4))
        ;; Some clause is absurd.
        (list t nil (list-fix x))
      (let* ((pass5 (fast-remove-duplicates-list$ pass4 nil))
             (pass6 (fast-remove-supersets pass5)))
        (list nil (not (disabled-equal x pass6)) pass6)))))







(defthm clause.fast-clean-clauses-removal
  (implies (force (logic.term-list-listp x))
           (equal (clause.fast-clean-clauses x)
                  (clause.clean-clauses x)))
  :hints(("Goal" :in-theory (e/d (clause.clean-clauses
                                  clause.fast-clean-clauses
                                  clause.normalize-nots-clauses-of-rev
                                  clause.remove-obvious-clauses-of-rev
                                  clause.remove-complement-clauses-of-rev
                                  )
                                 (rev-of-clause.normalize-nots-clauses
                                  rev-of-clause.remove-obvious-clauses
                                  rev-of-clause.remove-complement-clauses
                                  )))))



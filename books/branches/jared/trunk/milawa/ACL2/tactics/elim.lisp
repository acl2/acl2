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
(include-book "colors")
(include-book "skeletonp")
(include-book "conditional-eqsubst")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; BOZO copied and pasted from crewrite-all.  Need to really move this where it belongs.

(local (defthm logic.strip-conclusions-of-restn
         ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
          ;; belongs and try using it globally.
         (equal (logic.strip-conclusions (restn n x))
                (restn n (logic.strip-conclusions x)))))

(local (in-theory (disable restn-of-logic.strip-conclusions)))

(local (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-restn)
                                                    (:rewrite restn-of-logic.strip-conclusions))))


(local (defthm logic.strip-conclusions-of-firstn
         ;; BOZO this seems to address some of the firstn/restn issues.  Move it where it
         ;; belongs and try using it globally.
         (equal (logic.strip-conclusions (firstn n x))
                (firstn n (logic.strip-conclusions x)))))

(local (in-theory (disable firstn-of-logic.strip-conclusions)))

(local (ACL2::theory-invariant (ACL2::incompatible (:rewrite logic.strip-conclusions-of-firstn)
                                                   (:rewrite firstn-of-logic.strip-conclusions))))





;; BOZO none of this stuff belongs here.

(defthm logic.substitute-formula-of-logic.disjoin-formulas-free
  (implies (equal free (logic.disjoin-formulas x))
           (equal (logic.substitute-formula free sigma)
                  (logic.disjoin-formulas (logic.substitute-formula-list x sigma)))))

(defthms-flag
  :thms ((term aggressive-forcing-logic.substitute-of-logic.replace-subterm
               (implies (and (force (disjointp (logic.term-vars x) (domain sigma)))
                             (force (logic.termp x))
                             (force (logic.sigmap sigma)))
                        (equal (logic.substitute (logic.replace-subterm x old new) sigma)
                               (logic.replace-subterm x old (logic.substitute new sigma)))))
         (t    aggressive-forcing-logic.substitute-list-of-logic.replace-subterm-list
               (implies (and (force (disjointp (logic.term-list-vars x) (domain sigma)))
                             (force (logic.term-listp x))
                             (force (logic.sigmap sigma)))
                        (equal (logic.substitute-list (logic.replace-subterm-list x old new) sigma)
                               (logic.replace-subterm-list x old (logic.substitute new sigma))))))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :expand ((logic.replace-subterm x old new)
                   (logic.replace-subterm x old (logic.substitute new sigma))))))

(defthms-flag
  :thms ((term equal-of-logic.replace-subterm-and-logic.replace-subterm-when-same-term-and-old
               (implies (force (and (logic.termp x)
                                    (logic.termp old)))
                        (equal (equal (logic.replace-subterm x old new1)
                                      (logic.replace-subterm x old new2))
                               (or (not (logic.subtermp old x))
                                   (equal new1 new2)))))
         (t    equal-of-logic.replace-subterm-list-and-logic.replace-subterm-list-when-same-term-and-old
               (implies (force (and (logic.term-listp x)
                                    (logic.termp old)))
                        (equal (equal (logic.replace-subterm-list x old new1)
                                      (logic.replace-subterm-list x old new2))
                               (or (not (logic.subterm-of-somep old x))
                                   (equal new1 new2))))))

  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :expand ((logic.replace-subterm x old new1)
                   (logic.replace-subterm x old new2))
          ;; BOZO this should be a :definition rule, but is in fact a :rewrite rule
          ;; instead.
          :in-theory (enable definition-of-logic.subtermp))))

(defthm forcing-logic.substitute-of-var-when-first-in-sigma
  (implies (force (logic.variablep var))
           (equal (logic.substitute var (cons (cons var val) sigma))
                  val))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm forcing-logic.substitute-of-var-when-second-in-sigma
  (implies (force (logic.variablep var))
           (equal (logic.substitute var (cons (cons var1 val1) (cons (cons var val2) sigma)))
                  (if (equal var1 var)
                      val1
                    val2)))
  :hints(("Goal" :in-theory (enable definition-of-logic.substitute))))

(defthm equal-of-first-and-second-when-uniquep
  (implies (and (uniquep x)
                (consp (cdr x)))
           (equal (equal (first x) (second x))
                  nil)))

(defthm equal-of-second-and-first-when-uniquep
  (implies (and (uniquep x)
                (consp (cdr x)))
           (equal (equal (second x) (first x))
                  nil)))

(defthm memberp-of-first-of-difference-in-removed
  (equal (memberp (first (difference x y)) y)
         (if (consp (difference x y))
             nil
           (memberp nil y)))
  :hints(("Goal"
          :in-theory (disable memberp-of-car)
          :use ((:instance memberp-of-car
                           (x (difference x y)))))))

(defthm memberp-of-second-of-difference-in-removed
  (equal (memberp (second (difference x y)) y)
         (if (consp (cdr (difference x y)))
             nil
           (memberp nil y)))
  :hints(("Goal"
          :in-theory (disable memberp-of-second)
          :use ((:instance memberp-of-second
                           (x (difference x y)))))))



;; Car-cdr-elim tactic
;;
;; This is a lot like the conditional-eqsubst tactic.  In fact, you can implement
;; a primitive version of car-cdr-elim using conditional-eqsubst; see the comments
;; in conditional-eqsubst.lisp for the details.  So what we are mostly interested
;; in here is writing the heuristics that choose WHEN to apply this approach.
;;
;; Our code is much simpler than ACL2's for many reasons:
;;
;;   - we only support car/cdr elim, rather than arbitrary elimination rules
;;   - we don't worry about equivalences other than equal
;;   - we don't worry about infinite loops due to opening recursive functions
;;   - we don't have any equivalent of :generalize rules
;;   - we don't try to do multiple elims in a single step
;;
;; On the other hand, ACL2 is allowed to just go and generate new variable names,
;; whereas




;; How do we pick the variable to eliminate?  At one point we tried to just
;; scan for the first occurrence of (car v) or (cdr v) and pick that v.  But
;; this failed to trigger elimination on goals when no destructor occurred,
;; such as
;;
;;  (implies (consp x)
;;           (foo x))
;;
;; We tried expanding our search to include occurrences of (consp v), but
;; this triggered inappropriately sometimes, e.g., on goals like this:
;;
;;  (implies (and (not (consp y))
;;                (consp x))
;;           (foo (car x) (cdr x)))
;;
;; We could see y being triggered for elimination instead of x.  So now we
;; implement a two-phase approach.  First we collect up all the variables which
;; have been car'd or cdr'd somewhere in the goal.  If there are any such
;; variables, we take the maximally-car/cdr'd variable and eliminate it.
;; Otherwise, we try to choose the first occuring (consp v) hypothesis.
;; Otherwise, we fail.

(defund elim.flag-collect-destructed-variables (flag x acc)
  ;; We scan through a term(-list) and try to find any subterms of the form
  ;; (car v) or (cdr v), where v is any variable symbol.  We accumulate all
  ;; such v into acc.
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (if (logic.functionp x)
          (let ((name (logic.function-name x))
                (args (logic.function-args x)))
            (if (and (or (equal name 'car)
                         (equal name 'cdr))
                     (equal (len args) 1)
                     (logic.variablep (first args)))
                (cons (first args) acc)
              (elim.flag-collect-destructed-variables 'list args acc)))
        acc)
    (if (consp x)
        (elim.flag-collect-destructed-variables 'term (car x)
                                                (elim.flag-collect-destructed-variables 'list (cdr x) acc))
      acc)))

(defund elim.flag-slow-collect-destructed-variables (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (logic.termp x)
                           (logic.term-listp x))))
  (if (equal flag 'term)
      (if (logic.functionp x)
          (let ((name (logic.function-name x))
                (args (logic.function-args x)))
            (if (and (or (equal name 'car)
                         (equal name 'cdr))
                     (equal (len args) 1)
                     (logic.variablep (first args)))
                (list (first args))
              (elim.flag-slow-collect-destructed-variables 'list args)))
        nil)
    (if (consp x)
        (app (elim.flag-slow-collect-destructed-variables 'term (car x))
             (elim.flag-slow-collect-destructed-variables 'list (cdr x)))
      nil)))

(definlined elim.collect-destructed-variables (x)
  (declare (xargs :guard (logic.termp x)))
  (elim.flag-collect-destructed-variables 'term x nil))

(definlined elim.collect-destructed-variables-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (elim.flag-collect-destructed-variables 'list x nil))

(defthm true-listp-of-elim.flag-collect-destructed-variables
  (implies (true-listp acc)
           (true-listp (elim.flag-collect-destructed-variables flag x acc)))
  :hints(("Goal"
          :induct (elim.flag-collect-destructed-variables flag x acc)
          :in-theory (enable (:induction elim.flag-collect-destructed-variables))
          :expand ((:free (flag) (elim.flag-collect-destructed-variables flag x acc))))))

(defthm elim.flag-slow-collect-destructed-variables-equiv
  (implies (true-listp acc)
           (equal (elim.flag-collect-destructed-variables flag x acc)
                  (app (elim.flag-slow-collect-destructed-variables flag x)
                       acc)))
  :hints(("Goal"
          :induct (elim.flag-collect-destructed-variables flag x acc)
          :in-theory (enable (:induction elim.flag-collect-destructed-variables))
          :expand ((:free (flag) (elim.flag-collect-destructed-variables flag x acc))
                   (:free (flag) (elim.flag-slow-collect-destructed-variables flag x))))))

(defthmd definition-of-elim.collect-destructed-variables
  (equal (elim.collect-destructed-variables x)
         (if (logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (or (equal name 'car)
                            (equal name 'cdr))
                        (equal (len args) 1)
                        (logic.variablep (first args)))
                   (list (first args))
                 (elim.collect-destructed-variables-list args)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :expand (elim.flag-slow-collect-destructed-variables 'term x)
          :in-theory (enable elim.collect-destructed-variables
                             elim.collect-destructed-variables-list))))

(defthmd definition-of-elim.collect-destructed-variables-list
  (equal (elim.collect-destructed-variables-list x)
         (if (consp x)
             (app (elim.collect-destructed-variables (car x))
                  (elim.collect-destructed-variables-list (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :expand (elim.flag-slow-collect-destructed-variables 'list x)
          :in-theory (enable elim.collect-destructed-variables
                             elim.collect-destructed-variables-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition elim.flag-collect-destructed-variables))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition elim.flag-slow-collect-destructed-variables))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition elim.collect-destructed-variables))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition elim.collect-destructed-variables-list))))

(defthms-flag
  :thms ((term logic.variable-listp-of-elim.collect-destructed-variables
               (equal (logic.variable-listp (elim.collect-destructed-variables x))
                      t))
         (t logic.variable-listp-of-elim.collect-destructed-variables-list
            (equal (logic.variable-listp (elim.collect-destructed-variables-list x))
                   t)))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :expand ((elim.collect-destructed-variables x)
                   (elim.collect-destructed-variables-list x)))))


(defsection count

  (defund fast-count (a x acc)
    (declare (xargs :guard (natp acc)))
    (if (consp x)
        (fast-count a (cdr x) (if (equal a (car x))
                                  (+ 1 acc)
                                acc))
      acc))

  (defund slow-count (a x)
    (declare (xargs :guard t))
    (if (consp x)
        (if (equal a (car x))
            (+ 1 (slow-count a (cdr x)))
          (slow-count a (cdr x)))
      0))

  (defund count (a x)
    (declare (xargs :guard t))
    (fast-count a x 0))

  (defthmd fast-count-as-slow-count
    (implies (natp acc)
             (equal (fast-count a x acc)
                    (+ acc (slow-count a x))))
    :hints(("Goal" :in-theory (enable fast-count slow-count))))

  (defthmd definition-of-count
    (equal (count a x)
           (if (consp x)
               (if (equal a (car x))
                   (+ 1 (count a (cdr x)))
                 (count a (cdr x)))
             0))
    :rule-classes :definition
    :hints(("Goal" :in-theory (enable count
                                      slow-count
                                      fast-count-as-slow-count))))

  (ACL2::theory-invariant (not (ACL2::active-runep '(:definition count))))

  (defthm count-when-not-consp
    (implies (not (consp x))
             (equal (count a x)
                    0))
    :hints(("Goal" :expand (count a x))))

  (defthm count-of-cons
    (equal (count a (cons b x))
           (if (equal a b)
               (+ 1 (count a x))
             (count a x)))
    :hints(("Goal" :expand (count a (cons b x)))))

  (defthm natp-of-count
    (equal (natp (count a x))
           t)
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm count-of-zero
    (equal (equal 0 (count a x))
           (not (memberp a x)))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm count-of-list-fix
    (equal (count a (list-fix x))
           (count a x))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm count-of-app
    (equal (count a (app x y))
           (+ (count a x)
              (count a y)))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm count-of-rev
    (equal (count a (rev x))
           (count a x))
    :hints(("Goal" :induct (cdr-induction x))))

  (defthm count-when-not-memberp
    (implies (not (memberp a x))
             (equal (count a x)
                    0))
    :hints(("Goal" :induct (cdr-induction x)))))



(defund aux-maximal-count (best best-count domain x)
  (declare (xargs :guard (and (natp best-count)
                              (equal (count best x) best-count))))
  (if (consp domain)
      (let ((car-count (count (car domain) x)))
        (if (< best-count car-count)
            (aux-maximal-count (car domain) car-count (cdr domain) x)
          (aux-maximal-count best best-count (cdr domain) x)))
    best))

(defthm memberp-of-aux-maximal-count
  (implies (memberp best x)
           (equal (memberp (aux-maximal-count best best-count domain x) x)
                  t))
  :hints(("Goal" :in-theory (enable aux-maximal-count))))

(defthm aux-maximal-count-when-not-consp-of-x
  (implies (not (consp x))
           (equal (aux-maximal-count best best-count domain x)
                  best))
  :hints(("Goal" :in-theory (enable aux-maximal-count))))

(defund maximal-count (x)
  (declare (xargs :guard (consp x)))
  (aux-maximal-count (car x)
                     (count (car x) x)
                     (cdr x)
                     x))

(defthm maximal-count-when-not-consp
  (implies (not (consp x))
           (equal (maximal-count x)
                  nil))
  :hints(("Goal" :in-theory (enable maximal-count))))

(defthm memberp-of-maximal-count
  (equal (memberp (maximal-count x) x)
         (consp x))
  :hints(("Goal" :in-theory (enable maximal-count))))





(defund elim.find-backup-var (x)
  ;; If this function is called, we have not found any destructed variables
  ;; anywhere in the clause.  But before we give up, we look for any literals
  ;; of the form (not (consp v)).  If such a literal exists, it corresponds
  ;; to the hypothesis that v is a consp, and we will try to eliminate v.
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (or (let ((term1 (car x)))
            (and (logic.functionp term1)
                 (equal 'not (logic.function-name term1))
                 (let ((not-args (logic.function-args term1)))
                   ;; (not ...)
                   (and (equal 1 (len not-args))
                        (logic.functionp (first not-args))
                        (equal 'consp (logic.function-name (first not-args)))
                        ;; (consp ...)
                        (let ((consp-args (logic.function-args (first not-args))))
                          (and (logic.variablep (first consp-args))
                               (first consp-args)))))))
          (elim.find-backup-var (cdr x)))
    nil))

(defthm logic.variablep-of-elim.find-backup-var
  (equal (logic.variablep (elim.find-backup-var x))
         (if (elim.find-backup-var x)
             t
           nil))
  :hints(("Goal" :in-theory (enable elim.find-backup-var))))



(defund elim.choose-var-to-eliminate (x)
  (declare (xargs :guard (logic.term-listp x)))
  (let ((destructed-vars (elim.collect-destructed-variables-list x)))
    (if (consp destructed-vars)
        (maximal-count destructed-vars)
      (elim.find-backup-var x))))

(defthmd lemma-for-logic.variablep-of-elim.choose-var-to-eliminate
  (implies (logic.variable-listp x)
           (equal (logic.variablep (maximal-count x))
                  (consp x)))
  :hints(("Goal"
          :in-theory (disable logic.variablep-when-memberp-of-logic.variable-listp)
          :use ((:instance logic.variablep-when-memberp-of-logic.variable-listp
                           (a (maximal-count x))
                           (x x))))))

(defthm logic.variablep-of-elim.choose-var-to-eliminate
  (equal (logic.variablep (elim.choose-var-to-eliminate x))
         (if (elim.choose-var-to-eliminate x)
             t
           nil))
  :hints(("Goal" :in-theory (enable elim.choose-var-to-eliminate
                                    lemma-for-logic.variablep-of-elim.choose-var-to-eliminate))))






(defsection elim.pick-fresh-vars

  ;; Because our logic provides no means by which to create a new variable, we
  ;; are left with some difficulty when it comes to generating variable names.
  ;; To address this, we come up with a clunky and somewhat elaborate scheme for
  ;; generating new variable names.
  ;;
  ;; An elim names structure is a mapping from variables to their "preferred
  ;; names."  When we want to apply destructor elimination to kill a variable,
  ;; var, we begin by seeing if there are any preferred names for this variable.
  ;; If so, we try to use them if we can (i.e., if they are not already in use
  ;; somewhere in the clause).
  ;;
  ;; But sometimes this will fail and there will not be any preferred names
  ;; available.  In this case, we try to assign from a list of unappealing names,
  ;; the "unpreferred-names."
  ;;
  ;; In our user interface, symmetry, we try to shield the user from ever having
  ;; to deal with this ugliness.  We use under-the-hood ACL2 calls to generate a
  ;; suitable elim.namesp structure that can be given to the elim tactic without
  ;; ever involving the user.  This is like any other part of skeleton
  ;; management, and is a purely user-interface issue which can be kept away from
  ;; the logic.

  (deflist logic.variable-list-listp (x)
    (logic.variable-listp x)
    :elementp-of-nil t)

  (defmap :map (elim.namesp x)
    :key (logic.variablep x)
    :val (logic.variable-listp x)
    :key-list (logic.variable-listp x)
    :val-list (logic.variable-list-listp x)
    :val-of-nil t)

  (defund elim.pick-fresh-vars (var forbidden names)
    (declare (xargs :guard (and (logic.variablep var)
                                (logic.variable-listp forbidden)
                                (elim.namesp names))))
    (or
     ;; First we try to find a preferred name.
     (let ((lookup (lookup var names)))
       (and lookup
            (let ((safe-names (remove-duplicates (difference (cdr lookup) forbidden))))
              (and (consp (cdr safe-names))
                   (list (first safe-names)
                         (second safe-names))))))
     ;; Next we try to use unpreferred names.
     (let ((lookup (lookup 'unpreferred names)))
       (and lookup
            (let ((safe-names (remove-duplicates (difference (cdr lookup) forbidden))))
              (and (consp (cdr safe-names))
                   (list (first safe-names)
                         (second safe-names))))))
     ;; Otherwise, we fail.
     (ACL2::prog2$ (ACL2::cw! "~s0Warning:~s1: no fresh variable names available for eliminating ~x2.~%"
                              *red* *black* var)
                   nil)))

  (local (in-theory (enable elim.pick-fresh-vars)))

  (defthm forcing-logic.variablep-of-first-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (logic.variablep (first (elim.pick-fresh-vars var forbidden names)))
                    t)))

  (defthm forcing-logic.variablep-of-second-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (logic.variablep (second (elim.pick-fresh-vars var forbidden names)))
                    t)))

  (defthm forcing-logic.memberp-of-first-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (memberp (first (elim.pick-fresh-vars var forbidden names)) forbidden)
                    nil)))

  (defthm forcing-logic.memberp-of-second-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (memberp (second (elim.pick-fresh-vars var forbidden names)) forbidden)
                    nil)))

  (defthm forcing-equal-of-first-and-second-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (equal (first (elim.pick-fresh-vars var forbidden names))
                           (second (elim.pick-fresh-vars var forbidden names)))
                    nil)))

  (defthm forcing-equal-of-second-and-first-of-elim.pick-fresh-vars
    (implies (and (elim.pick-fresh-vars var forbidden names)
                  (force (and (logic.variablep var)
                              (logic.variable-listp forbidden)
                              (elim.namesp names))))
             (equal (equal (second (elim.pick-fresh-vars var forbidden names))
                           (first (elim.pick-fresh-vars var forbidden names)))
                    nil))))



(defsection elim.elim-clause

  (defund elim.elim-clause (x names n)
    ;; X is a clause and unsafe-vars are a list of variables which hopefully do
    ;; not occur in the clause, but we are not sure of this.  We try to find a
    ;; destructor term to eliminate, apply the elimination, and return a new list
    ;; of clauses whose conjunction implies x.
    (declare (xargs :guard (and (consp x)
                                (logic.term-listp x)
                                (elim.namesp names))))
    (let ((var (elim.choose-var-to-eliminate x)))
      (if (not var)
          ;; There are no destructor terms in the clause, and hence nothing for
          ;; us to do.  Our only resulting clause is the input clause itself.
          (list x)
        ;; Otherwise, we have found a term to eliminate.  We need two fresh
        ;; variables, one for the car and one for the cdr.
        (let* ((fresh-vars  (elim.pick-fresh-vars var (logic.term-list-vars x) names)))
          (if (not fresh-vars)
              ;; No fresh vars available.  We won't try to eliminate.  A complaint
              ;; has already been printed by elim.pick-fresh-vars.
              (list x)
            (let* ((new-car (first fresh-vars))
                   (new-cdr (second fresh-vars))
                   (new-var (logic.function 'cons (list new-car new-cdr))))
              (ACL2::prog2$
               (or (not n)
                   (ACL2::cw! ";; Clause #~x0: elim transforms (CAR ~s1), (CDR ~s1) into ~x2, ~x3.~%"
                              n var new-car new-cdr))
               ;; We're going to produce two new subgoals.  The first is essentially:
               ;;
               ;;    (not (consp var)) --> x              i.e., (consp var) v x
               ;;
               ;; Hopefully this is trivial; in any event, it will allow the terms
               ;; (car var) and (cdr var) to be replaced by nil's, and perhaps some
               ;; progress will then be possible.
               ;;
               ;; The second goal is essentially:
               ;;
               ;;    x / { var <- (cons new-car new-cdr) }
               ;;
               ;; This is the goal you normally think of as destructor elimination.
               (let ((1st-clause (cons (logic.function 'consp (list var)) x))
                     (2nd-clause (logic.replace-subterm-list x var new-var)))
                 (list 1st-clause 2nd-clause)))))))))

  (defthm forcing-logic.term-list-listp-of-elim.elim-clause
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (elim.namesp names)))
             (equal (logic.term-list-listp (elim.elim-clause x names n))
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause))))

  (defthm forcing-cons-listp-of-elim.elim-clause
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (elim.namesp names)))
             (equal (cons-listp (elim.elim-clause x names n))
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause))))

  (defthm forcing-logic.term-list-list-atblp-of-elim.elim-clause
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (logic.term-list-atblp x atbl)
                         (elim.namesp names)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'cons atbl)) 2)
                         (equal (cdr (lookup 'consp atbl)) 1)))
             (equal (logic.term-list-list-atblp (elim.elim-clause x names n) atbl)
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause)))))





(defsection elim.elim-clause-bldr

  (local (in-theory (enable axiom-cons-of-car-and-cdr
                            elim.elim-clause
                            logic.term-formula
                            redefinition-of-logic.term-list-formulas)))

  (defund elim.elim-clause-bldr (x names proofs n)
    (declare (xargs :guard (and (consp x)
                                (logic.term-listp x)
                                (elim.namesp names)
                                (logic.appeal-listp proofs)
                                (equal (logic.strip-conclusions proofs)
                                       (clause.clause-list-formulas (elim.elim-clause x names n)))))
             (ignore n))
    (let ((var (elim.choose-var-to-eliminate x)))
      (if (not var)
          (first proofs)
        (let* ((fresh-vars (elim.pick-fresh-vars var (logic.term-list-vars x) names)))
          (if (not fresh-vars)
              (first proofs)
            (let ((new-car (first fresh-vars))
                  (new-cdr (second fresh-vars)))
              ;; This is like conditional-eqsubst with:
              ;;    hypterm = (consp var)
              ;;    lhs     = var
              ;;    rhs     = (cons (car var) (cdr var))
              (tactic.conditional-eqsubst-bldr
               (logic.pequal (logic.function 'consp (list var)) ''nil)
               x
               ;; Our first proof obligation is (consp var) = nil v var = (cons (car var) (cdr var)).
               ;; This is easy to prove using the car-cdr-elim axiom
               (build.instantiation (build.disjoined-commute-pequal (build.axiom (axiom-cons-of-car-and-cdr)))
                                    (list (cons 'x var)))
               ;; Our second obligation is the degenerate case, (consp var) v x
               ;; This is easy because it is our first output clause.
               (first proofs)
               ;; Our third obligation is  x/{ var <- (cons (car var) (cdr var)) }
               ;; But this is just an instance of our generalized second output clause.
               (build.instantiation (second proofs)
                                    (list (cons new-car (logic.function 'car (list var)))
                                          (cons new-cdr (logic.function 'cdr (list var)))))
               ;; Finally we need to provide the lhs and rhs.
               var
               (logic.function 'cons (list (logic.function 'car (list var))
                                           (logic.function 'cdr (list var)))))))))))

  (defobligations elim.elim-clause-bldr
    (tactic.conditional-eqsubst-bldr
     build.disjoined-commute-equal)
    :extra-axioms ((axiom-cons-of-car-and-cdr)))

  (local (in-theory (enable elim.elim-clause-bldr)))

  (defthm forcing-logic.appealp-of-elim.elim-clause-bldr
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause x names n)))))
             (equal (logic.appealp (elim.elim-clause-bldr x names proofs n))
                    t)))

  (defthm forcing-logic.conclusion-of-elim.elim-clause-bldr
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause x names n)))))
             (equal (logic.conclusion (elim.elim-clause-bldr x names proofs n))
                    (clause.clause-formula x))))

  (defthm@ forcing-logic.proofp-of-elim.elim-clause-bldr
    (implies (force (and (consp x)
                         (logic.term-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause x names n)))
                         ;; ---
                         (logic.term-list-atblp x atbl)
                         (logic.proof-listp proofs axioms thms atbl)
                         (@obligations elim.elim-clause-bldr)
                         (equal (cdr (lookup 'consp atbl)) 1)
                         (equal (cdr (lookup 'cons atbl)) 2)
                         (equal (cdr (lookup 'car atbl)) 1)
                         (equal (cdr (lookup 'cdr atbl)) 1)))
             (equal (logic.proofp (elim.elim-clause-bldr x names proofs n) axioms thms atbl)
                    t))))



(defsection elim.elim-clause-list

  (defund elim.elim-clause-list (x names)
    (declare (xargs :guard (and (cons-listp x)
                                (logic.term-list-listp x)
                                (elim.namesp names))))
    (if (consp x)
        (fast-app (elim.elim-clause (car x) names (fast-len x 0))
                  (elim.elim-clause-list (cdr x) names))
      nil))

  (defthm true-listp-of-elim.elim-clause-list
    (equal (true-listp (elim.elim-clause-list x names))
           t)
    :hints(("Goal" :in-theory (enable elim.elim-clause-list))))

  (defthm forcing-logic.term-list-listp-of-elim.elim-clause-list
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (elim.namesp names)))
             (equal (logic.term-list-listp (elim.elim-clause-list x names))
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause-list))))


  (defthm forcing-logic.term-list-list-atblp-of-elim.elim-clause-list
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (logic.term-list-list-atblp x atbl)
                         (elim.namesp names)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'consp atbl)) 1)
                         (equal (cdr (lookup 'cons atbl)) 2)))
             (equal (logic.term-list-list-atblp (elim.elim-clause-list x names) atbl)
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause-list))))

  (defthm forcing-cons-listp-of-elim.elim-clause-list
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (elim.namesp names)))
             (equal (cons-listp (elim.elim-clause-list x names))
                    t))
    :hints(("Goal" :in-theory (enable elim.elim-clause-list)))))




(defsection elim.elim-clause-list-bldr

  (local (in-theory (enable elim.elim-clause-list)))

  (defthmd dangerous-decomposition-of-app
    (equal (equal x (app a b))
           (and (true-listp x)
                (equal (firstn (len a) x) (list-fix a))
                (equal (restn (len a) x) (list-fix b))))
    :hints(("Goal"
            :induct (cdr-cdr-induction x a)
            :expand ((:free (x) (firstn (len a) x))
                     (:free (x) (restn (len a) x))))))

  (local (in-theory (enable dangerous-decomposition-of-app)))

  (defund elim.elim-clause-list-bldr (x names proofs)
    (declare (xargs :guard (and (cons-listp x)
                                (logic.term-list-listp x)
                                (elim.namesp names)
                                (logic.appeal-listp proofs)
                                (equal (logic.strip-conclusions proofs)
                                       (clause.clause-list-formulas (elim.elim-clause-list x names))))))
    (if (consp x)
        (let* ((clause-n             (fast-len x 0))
               (elim-first           (elim.elim-clause (car x) names clause-n))
               (num-proofs           (fast-len elim-first 0)))
          (cons (elim.elim-clause-bldr (car x) names (firstn num-proofs proofs) clause-n)
                (elim.elim-clause-list-bldr (cdr x) names (restn num-proofs proofs))))
      nil))

  (defobligations elim.elim-clause-list-bldr
    (elim.elim-clause-bldr))

  (local (in-theory (enable elim.elim-clause-list-bldr)))

  (defthm forcing-logic.appeal-listp-of-elim.elim-clause-list-bldr
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause-list x names)))))
             (equal (logic.appeal-listp (elim.elim-clause-list-bldr x names proofs))
                    t)))

  (defthm forcing-logic.strip-conclusions-of-elim.elim-clause-list-bldr
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause-list x names)))))
             (equal (logic.strip-conclusions (elim.elim-clause-list-bldr x names proofs))
                    (clause.clause-list-formulas x))))

  (defthm@ forcing-logic.proof-listp-of-elim.elim-clause-list-bldr
    (implies (force (and (cons-listp x)
                         (logic.term-list-listp x)
                         (elim.namesp names)
                         (logic.appeal-listp proofs)
                         (equal (logic.strip-conclusions proofs)
                                (clause.clause-list-formulas (elim.elim-clause-list x names)))
                         ;; ---
                         (logic.term-list-list-atblp x atbl)
                         (logic.proof-listp proofs axioms thms atbl)
                         (@obligations elim.elim-clause-list-bldr)
                         (equal (cdr (lookup 'consp atbl)) 1)
                         (equal (cdr (lookup 'cons atbl)) 2)
                         (equal (cdr (lookup 'car atbl)) 1)
                         (equal (cdr (lookup 'cdr atbl)) 1)
                         ))
             (equal (logic.proof-listp (elim.elim-clause-list-bldr x names proofs) axioms thms atbl)
                    t))))







(defund tactic.elim-first-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'elim-first)
         (elim.namesp extras)
         (let ((prev-goals (tactic.skeleton->goals history)))
           (and (consp prev-goals)
                (let ((elim-goals (elim.elim-clause (first prev-goals) extras nil)))
                  (and elim-goals
                       (equal goals
                              (fast-app elim-goals (cdr prev-goals))))))))))

(defthm booleanp-of-tactic.elim-first-okp
  (equal (booleanp (tactic.elim-first-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.elim-first-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.elim-first-tac (x names)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (elim.namesp names))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0elim-first-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let ((elim-goals (elim.elim-clause (first goals) names nil)))
        (if (not elim-goals)
            (ACL2::cw "~s0elim-first-tac failure~s1: no subterms of the form (CAR VAR) or (CDR VAR) were found.~%"
                      *red* *black*)
          (tactic.extend-skeleton (fast-app (elim.elim-clause (first goals) names nil)
                                            (cdr goals))
                                  'elim-first
                                  names
                                  x))))))

(defthm forcing-tactic.skeletonp-of-tactic.elim-first-tac
  (implies (and (tactic.elim-first-tac x names)
                (force (elim.namesp names))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.elim-first-tac x names))
                  t))
  :hints(("Goal" :in-theory (enable tactic.elim-first-tac))))

(defthm forcing-tactic.elim-first-okp-of-tactic.elim-first-tac
  (implies (and (tactic.elim-first-tac x names)
                (force (elim.namesp names))
                (force (tactic.skeletonp x)))
           (equal (tactic.elim-first-okp (tactic.elim-first-tac x names))
                  t))
  :hints(("Goal" :in-theory (enable tactic.elim-first-tac
                                    tactic.elim-first-okp))))





(defund tactic.elim-first-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.elim-first-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras       (tactic.skeleton->extras x))
         (history      (tactic.skeleton->history x))
         (orig-goal    (car (tactic.skeleton->goals history)))
         (elim-goals   (elim.elim-clause orig-goal extras nil))
         (elim-len     (fast-len elim-goals 0))
         (elim-proofs  (firstn elim-len proofs))
         (other-proofs (restn elim-len proofs)))
    (cons (elim.elim-clause-bldr orig-goal extras elim-proofs nil)
          other-proofs)))

(defobligations tactic.elim-first-compile
  (elim.elim-clause-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.elim-first-okp
                           tactic.elim-first-compile)))

 (local (in-theory (enable dangerous-decomposition-of-app)))

 (local (ACL2::allow-fertilize t))

 (verify-guards tactic.elim-first-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.elim-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.elim-first-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.elim-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.elim-first-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.elim-first-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-first-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.elim-first-compile)
                        (equal (cdr (lookup 'cdr atbl)) 1)
                        (equal (cdr (lookup 'car atbl)) 1)
                        (equal (cdr (lookup 'cons atbl)) 2)
                        (equal (cdr (lookup 'consp atbl)) 1)
                        ))
            (equal (logic.proof-listp (tactic.elim-first-compile x proofs) axioms thms atbl)
                   t))))












(defund tactic.elim-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'elim-all)
         (elim.namesp extras)
         (equal goals (elim.elim-clause-list (tactic.skeleton->goals history) extras)))))

(defthm booleanp-of-tactic.elim-all-okp
  (equal (booleanp (tactic.elim-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.elim-all-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.elim-all-tac (x names warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (elim.namesp names))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0elim-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let* ((elim-goals (elim.elim-clause-list goals names))
             (progressp  ;; Elim always produces two goals for every goal it
			 ;; encounters.  Hence, we don't have to check equality
			 ;; of the goals, we can just check same-lengthp.
                         (not (same-lengthp goals elim-goals))))
        (cond ((not progressp)
               (and warnp
                    (ACL2::cw "~s0elim-all-tac failure~s1: no progress was made.~%" *red* *black*)))
              (t
               (tactic.extend-skeleton elim-goals 'elim-all names x)))))))

(defthm forcing-tactic.skeletonp-of-tactic.elim-all-tac
  (implies (and (tactic.elim-all-tac x names warnp)
                (force (elim.namesp names))
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.elim-all-tac x names warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.elim-all-tac))))

(defthm forcing-tactic.elim-all-okp-of-tactic.elim-all-tac
  (implies (and (tactic.elim-all-tac x names warnp)
                (force (elim.namesp names))
                (force (tactic.skeletonp x)))
           (equal (tactic.elim-all-okp (tactic.elim-all-tac x names warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.elim-all-tac
                                    tactic.elim-all-okp))))



(defund tactic.elim-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.elim-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((extras       (tactic.skeleton->extras x))
         (history      (tactic.skeleton->history x)))
    (elim.elim-clause-list-bldr (tactic.skeleton->goals history) extras proofs)))

(defobligations tactic.elim-all-compile
  (elim.elim-clause-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.elim-all-okp
                           tactic.elim-all-compile)))

 (verify-guards tactic.elim-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.elim-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.elim-all-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.elim-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.elim-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.elim-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.elim-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations tactic.elim-all-compile)
                        (equal (cdr (lookup 'cdr atbl)) 1)
                        (equal (cdr (lookup 'car atbl)) 1)
                        (equal (cdr (lookup 'cons atbl)) 2)
                        (equal (cdr (lookup 'consp atbl)) 1)
                        ))
            (equal (logic.proof-listp (tactic.elim-all-compile x proofs) axioms thms atbl)
                   t))))



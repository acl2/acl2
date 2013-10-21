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
(include-book "core")


;; Simple tactics
;;
;; We now introduce some of the simple tactics which don't make use of any
;; theories.  All of our tactics make only local changes to the skeleton.  This
;; way, they are skipped when the already-certified books are being included.

(defun %tactic.skip-all-tac-wrapper (skelly)
  (declare (xargs :mode :program))
  (tactic.skip-all-tac skelly))

(defun %tactic.skip-first-tac-wrapper (skelly)
  (declare (xargs :mode :program))
  (tactic.skip-first-tac skelly))

(defmacro %skip (&rest args)
  ;; Pretend that you have proven some goals.
  ;;
  ;; Usage:
  ;;   (%skip)            Skip the current goal.
  ;;   (%skip all)        Skip all of the goals.
  ;;
  ;; Note: This is not a sound tactic to apply.  It relies upon the special and
  ;; "skipping" mechanism only available in the ACL2 version of proofp, which is
  ;; not available in the core Milawa proof checker.
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (new-skelly (if ',(memberp 'all args)
                                               (%tactic.skip-all-tac-wrapper skelly)
                                             (%tactic.skip-first-tac-wrapper skelly))))
                          (or new-skelly skelly))))
    (local (%print))))



(defun %tactic.cleanup-tac-wrapper (skelly warnp)
  (declare (xargs :mode :program))
  (tactic.cleanup-tac skelly warnp))

(defmacro %cleanup ()
  ;; Apply basic cleaning to all the goals.  We try to:
  ;;
  ;;   - Eliminate double negation from the tops of literals,
  ;;   - Standardize all not-variants to (not x),
  ;;   - Eliminate any clauses with "obvious" literals,
  ;;   - Eliminate any clauses with complementary literals,
  ;;   - Remove any "absurd" literals from each clause,
  ;;   - Remove any duplicate literals within each clause, and
  ;;   - Eliminate any "subsumed" clauses from the list.
  ;;
  ;; There are no configurable options.
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (warnp      (tactic.harness->warnp ACL2::world))
                               (new-skelly (%tactic.cleanup-tac-wrapper skelly warnp)))
                          (or new-skelly skelly))))
    (local (%print))))



(defun tactic.simple-world-change-wrapper (changes world)
  (declare (xargs :mode :program))
  (tactic.simple-world-change changes world))

(defun tactic.simple-change-world-tac-wrapper (skelly changes)
  (declare (xargs :mode :program))
  (tactic.simple-change-world-tac skelly changes))

(defun %simple-world-change-fn (changes)
  (declare (xargs :mode :program))
  `(ACL2::progn
    (ACL2::table tactic-harness 'world
                 (tactic.simple-world-change-wrapper ',changes
                                                     (tactic.harness->world acl2::world)))
    (ACL2::table tactic-harness 'skeleton
                 (let ((skelly (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.simple-change-world-tac-wrapper skelly ',changes))))))

(defmacro %liftlimit (&optional (limit '0))
  ;; Change the lift limit (used by %split).  Setting a low liftlimit may
  ;; help reduce case splitting by preventing "if" expressions from being
  ;; lifted out of other terms.  Normally, terms like (foo (if x y z)) are
  ;; first "lifted" to (if x (foo y) (foo z)), and then case-split on x.  A
  ;; liftlimit prevents this from happening after a certain depth.
  ;;
  ;; Usage:
  ;;   (%liftlimit)          Change the liftlimit to unlimited.
  ;;   (%liftlimit 10)       Change the liftlimit to 10.
  ;;
  ;; I have found that (%liftlimit 1) produces the smallest proofs during the
  ;; early stages of bootstrapping.  However, after the split tactic is
  ;; verified in Level 7, a higher limit is better.
  (%simple-world-change-fn (list (cons 'liftlimit limit))))

(defmacro %splitlimit (&optional (limit '0))
  ;; Change the split limit (used by %split).  Setting a low splitlimit may
  ;; help control case-splitting by not looking for "if" expressions in the
  ;; later parts of the clause.
  ;;
  ;; Usage:
  ;;   (%splitlimit)         Change the splitlimit to unlimitd.
  ;;   (%splitlimit 10)      Change the splitlimit to 10.
  (%simple-world-change-fn (list (cons 'splitlimit limit))))

(defun %tactic.split-first-tac-wrapper (liftp liftlimit splitlimit skelly)
  (declare (xargs :mode :program))
  (tactic.split-first-tac liftp liftlimit splitlimit skelly))

(defun %tactic.split-all-tac-wrapper (liftp liftlimit splitlimit skelly warnp)
  (declare (xargs :mode :program))
  (tactic.split-all-tac liftp liftlimit splitlimit skelly warnp))

(defmacro %split (&key (what 'all) liftlimit splitlimit (liftp 't))
  ;; Case-split goals which have terms of the form (if a b c).
  ;;
  ;; WHAT controls what gets split.  The default, :what all, means all the
  ;; clauses should be split.  Alternately, :what first can be used to limit
  ;; splitting to the first clause.
  ;;
  ;; LIFTP controls whether or not the clauses will be if-lifted.  Lifting is
  ;; permitted by default and is generally desirable, and typically produces
  ;; larger numbers of simpler clauses.  However, sometimes it can be too
  ;; expensive, so you can turn it off with :liftp nil, or limit it using the
  ;; :limit keyword (described below).
  ;;
  ;; The LIFTLIMIT and SPLITLIMITED are inherited from %liftlimit and
  ;; %splitlimit by default, but can be overridden using your own keys.
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (warnp      (tactic.harness->warnp ACL2::world))
                               (world      (tactic.harness->world ACL2::world))
                               (liftlimit  (if ,liftlimit
                                               ,liftlimit
                                             (tactic.world->liftlimit world)))
                               (splitlimit (if ,splitlimit
                                               ,splitlimit
                                             (tactic.world->splitlimit world)))
                               (new-skelly (if ,(equal what 'first)
                                               (%tactic.split-first-tac-wrapper ,liftp liftlimit splitlimit skelly)
                                             (%tactic.split-all-tac-wrapper ,liftp liftlimit splitlimit skelly warnp))))
                          (or new-skelly skelly))))
    (local (%print))))



(defun %tactic.generalize-first-tac-wrapper (skelly expr var)
  (declare (xargs :mode :program :guard (and (logic.termp expr) (logic.variablep var))))
  (tactic.generalize-first-tac skelly expr var))

(defun %tactic.generalize-all-tac-wrapper (skelly expr var)
  (declare (xargs :mode :program :guard (and (logic.termp expr) (logic.variablep var))))
  (tactic.generalize-all-tac skelly expr var))

(defmacro %generalize (&rest args)
  ;; Replace any occurrences of some expression with a new variable.
  ;;
  ;; Usage:
  ;;   (%generalize expr var)         Try to generalize every goal.
  ;;   (%generalize first expr var)   Only try to generalize the first goal.
  ;;
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((firstp     (memberp 'first ',args))
                               (others     (remove-all 'first ',args))
                               (skelly     (tactic.harness->skeleton ACL2::world))
                               (expr       (first others))
                               (var        (second others))
                               (new-skelly (if firstp
                                               (%tactic.generalize-first-tac-wrapper skelly expr var)
                                             (%tactic.generalize-all-tac-wrapper skelly expr var))))
                          (or new-skelly skelly))))
    (local (%print))))




(defun %tactic.conditional-eqsubst-tac-wrapper (skelly hyp old new)
  (declare (xargs :mode :program
                  :guard (and (logic.termp hyp)
                              (logic.termp old)
                              (logic.termp new))))
  (tactic.conditional-eqsubst-tac skelly hyp old new))

(defun %tactic.conditional-eqsubst-all-tac-wrapper (skelly hyp old new warnp)
  (declare (xargs :mode :program
                  :guard (and (logic.termp hyp)
                              (logic.termp old)
                              (logic.termp new))))
  (tactic.conditional-eqsubst-all-tac skelly hyp old new warnp))

(defmacro %eqsubst (hyp old new &rest args)
  ;; Use a conditional equality to simplify the goals.
  ;;
  ;; Suppose the first goal has the form (implies (and h1 ... hN) concl).
  ;; Then, we create three new subgoals:
  ;;
  ;;   (1) (implies hyp (equal old new))    "subst correctness"
  ;;
  ;;   (2) (implies (and (not hyp)          "subst applicability"
  ;;                     h1 ... hn)
  ;;                concl)
  ;;
  ;;   (3) (implies (and h1/[old<-new]      "post substitution"
  ;;                     ...
  ;;                     hn/[old<-new])
  ;;                concl/[old<-new])
  ;;
  ;; Usage:
  ;;   (%eqsubst hyp old new)        Perform the substitution on every goal.
  ;;   (%eqsubst hyp old new first)  Perform the substition on only the first goal.
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (new-skelly ,(if (memberp 'first args)
                                                `(%tactic.conditional-eqsubst-tac-wrapper skelly ',hyp ',old ',new)
                                              `(%tactic.conditional-eqsubst-all-tac-wrapper skelly ',hyp ',old ',new
                                                                                            (tactic.harness->warnp ACL2::world)))))
                          (or new-skelly skelly))))
    (local (%print))))



(defun %tactic.elim-first-tac-wrapper (x names)
  (declare (xargs :mode :program))
  (tactic.elim-first-tac x names))

(defun %tactic.elim-all-tac-wrapper (x names warnp)
  (declare (xargs :mode :program))
  (tactic.elim-all-tac x names warnp))

(defun tactic.harness->create-names (root n acc)
  (declare (xargs :mode :program))
  (if (zp n)
      acc
    (tactic.harness->create-names root
                                  (- n 1)
                                  (cons (ACL2::intern-in-package-of-symbol
                                         (STR::ncat root n)
                                         'foo)
                                        acc))))

(defconst *tactic.harness-unpreferred-names*
  (tactic.harness->create-names "ELIM" 100 nil))

(defun tactic.harness->infer-preferred-names (vars acc)
  (declare (xargs :mode :program))
  (if (consp vars)
      (tactic.harness->infer-preferred-names
       (cdr vars)
       (cons (cons (car vars) (tactic.harness->create-names (ACL2::symbol-name (car vars)) 2 nil))
             acc))
    acc))

(defun tactic.harness->create-elim-names (goals)
  (declare (xargs :mode :program))
  (let ((all-clause-vars (remove-duplicates (logic.fast-term-list-list-vars goals nil))))
    (tactic.harness->infer-preferred-names all-clause-vars
                                           (list (cons 'unpreferred *tactic.harness-unpreferred-names*)))))

(defun %tactic.harness->create-elim-names-wrapper (goals)
  (declare (xargs :mode :program))
  (tactic.harness->create-elim-names goals))

(defmacro %car-cdr-elim (&rest args)
  ;; Perform car/cdr elimination.
  ;;
  ;; Usage:
  ;;  (%car-cdr-elim)             Auto-eliminate in every goal.
  ;;  (%car-cdr-elim first)       Auto-eliminate in the first goal.
  ;;  (%car-cdr-elim x)           Manual-eliminate x in every goal.
  ;;  (%car-cdr-elim x first)     Manual-eliminate x in the first goal.
  (let* ((firstp     (memberp 'first args))
         (args-prime (remove-all 'first args)))
    (if (consp args-prime)
        ;; Manual elimination.
        (let ((var (first args-prime)))
          (if firstp
              `(%eqsubst (consp ,var) ,var (cons (car ,var) (cdr ,var)) first)
            `(%eqsubst (consp ,var) ,var (cons (car ,var) (cdr ,var)))))
      ;; Automatic elimination.
      `(ACL2::progn
        (local (ACL2::table tactic-harness 'skeleton
                            (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                                   (warnp      (tactic.harness->warnp ACL2::world))
                                   (names      (%tactic.harness->create-elim-names-wrapper (tactic.skeleton->goals skelly)))
                                   (new-skelly (if ,firstp
                                                   (%tactic.elim-first-tac-wrapper skelly names)
                                                 (%tactic.elim-all-tac-wrapper skelly names warnp))))
                              (or new-skelly skelly))))
        (local (%print))))))

(defun %tactic.distribute-all-tac-wrapper (skelly warnp)
  (declare (xargs :mode :program))
  (tactic.distribute-all-tac skelly warnp))

(defmacro %distribute ()
  ;; Distribute trivial equivalences throughout the clauses.  Eventually we should add a
  ;; single-clause version of this, but for now we only do all clauses.
  ;;
  ;; Usage:
  ;;  (%distribute)
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (warnp      (tactic.harness->warnp ACL2::world))
                               (new-skelly (%tactic.distribute-all-tac-wrapper skelly warnp)))
                          (or new-skelly skelly))))
    (local (%print))))



(defun %tactic.fertilize-tac-wrapper (skelly target replacement)
  (declare (xargs :mode :program
                  :guard (and (logic.termp target)
                              (logic.termp replacement))))
  (tactic.fertilize-tac skelly target replacement))

(defmacro %fertilize (target replacement)
  ;; Replace all instances of one term with an equal term.
  ;;
  ;; Usage:
  ;;  (%fertilize target replacement)     Replace target with replacement in the first goal
  ;;
  ;; Note:
  ;;   (equal target replacement) must be among the current hyps for this to be a valid
  ;;   transformation.  Equivalently, (not (equal target replacement)) can be the conclusion.
  ;;
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (new-skelly (%tactic.fertilize-tac-wrapper skelly ',target ',replacement)))
                          (or new-skelly skelly))))
    (local (%print))))



(defun %tactic.use-tac-wrapper (skelly proof)
  (declare (xargs :mode :program
                  :guard (logic.appealp proof)))
  (tactic.use-tac skelly proof))

(defmacro %use (proof)
  ;; Add a fact into the first goal.
  ;;
  ;; Proof is an arbitrary proof of any formula.  We compile the formula and
  ;; add its negation into the clause.  This is a useful way to bring some
  ;; relevant but perhaps disabled fact to the attention of the rewriter, etc.
  ;;
  ;; The argument to %use is evaluated and should result in a proof.  By far
  ;; the most common way to generate such proofs is with the %instance and
  ;; %thm macros below.  For example:
  ;;
  ;;  (%use (%instance (%thm {name-of-theorem})
  ;;                   ({var} {replacement})
  ;;                   ...
  ;;                   ({var} {replacement})))
  ;;
  ;; But advanced users can use explicit proof builders here, e.g.,
  ;;
  ;;  (%use (build.cut ...))
  ;;
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (new-skelly (%tactic.use-tac-wrapper skelly ,proof)))
                          (or new-skelly skelly))))
    (local (%print))))

(defmacro %thm (name)
  `(build.theorem
    (clause.clause-formula
     (rw.rule-clause (tactic.find-rule ',name (tactic.harness->world ACL2::world))))))

(defun %instance-fn (thm untranslated-sigma)
  (declare (xargs :mode :program))
  (let ((translated-sigma+ (logic.translate-sigma untranslated-sigma)))
    (and translated-sigma+
         `(build.instantiation ,thm ',(cdr translated-sigma+)))))

(defmacro %instance (thm &rest pairs)
  (%instance-fn thm pairs))





(defun tactic.induct-casep (x)
  (declare (xargs :mode :program))
  (and (tuplep 2 x)
       (logic.translate (first x))
       (logic.translate-sigma-list (second x))))

(defun tactic.induct-case-listp (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (and (tactic.induct-casep (car x))
           (tactic.induct-case-listp (cdr x)))
    t))

(defun %tactic.induct-tac-wrapper (skelly m qs all-sigmas)
  (declare (xargs :mode :program
                  :guard (and (logic.termp m)
                              (logic.term-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (same-lengthp qs all-sigmas))))
  (tactic.induct-tac skelly m qs all-sigmas))

(defmacro %induct (m &rest cases)
  ;; Low level manual induction.
  ;;
  ;; You have to give a measure and then a list of cases of the form
  ;; (<tests governing this case> <list of sigmas that form the inductive hypotheses>)
  ;;
  ;;   (%induct (rank x)
  ;;      ((not (consp x))
  ;;       nil)                           ;; no inductions for the base case
  ;;      ((consp x)
  ;;       (((x (cdr x)) (y (cdr x)))     ;; IH1:  P( cdr(x), cdr(y) )
  ;;        ((x (cdr x)) (y (car x))))    ;; IH2:  P( cdr(x), car(y) )
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (cases      (if (tactic.induct-case-listp ',cases)
                                               ',cases
                                             (ACL2::er hard '%induct "The proposed cases are invalid.~%")))
                               (m          (if (logic.termp ',m)
                                               ',m
                                             (ACL2::er hard '%induct "The proposed measure is invalid.~%")))
                               (qs         (cdr (logic.translate-list (strip-firsts cases))))
                               (sigmas     (cdr (logic.translate-sigma-list-list (strip-seconds cases))))
                               (new-skelly (%tactic.induct-tac-wrapper skelly m qs sigmas)))
                          (or new-skelly skelly))))
    (local (%print))))

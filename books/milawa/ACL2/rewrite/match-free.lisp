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
(include-book "assms/top")
(include-book "rulep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm submap-of-eachp-when-submapp
  ;; BOZO find me a home
  (implies (and (submapp a b)
                (submap-of-eachp b x))
           (equal (submap-of-eachp a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm submap-of-eachp-when-submapp-alt
  ;; BOZO find me a home
  (implies (and (submap-of-eachp b x)
                (submapp a b))
           (equal (submap-of-eachp a x)
                  t)))



;; Free-variable matching
;;
;; The FREE VARIABLES of the rewrite rule hyps ==> (equiv lhs rhs) are all the
;; variables which occur in hyps but not in lhs.  The classic example of a
;; rule with free variables is a transitivity rule, e.g.,
;;
;;    [| subsetp x y; subsetp y z |] ==> (subsetp x z) = true
;;
;; Here, x and z are bound because they are mentioned in lhs, but y is free.
;;
;; If a rule does not contain any free variables, it is fairly straightforward
;; to apply it.  We match its lhs against our goal term, then use the resulting
;; sigma to instantiate all the hyps.  If all the hyps can be relieved, then we
;; replace the goal (which was lhs/sigma) with rhs/sigma.
;;
;; This strategy breaks down with free variables.  For example, suppose we know
;; (subsetp a b) and (subsetp b c), and we want to rewrite (subsetp a c).  We
;; match the pattern (subsetp x z) against our goal term, (subsetp a c),
;; producing the substitution { x <- a, z <- c }.  But this substitution does
;; not give us a sensible binding for y, so we are left with the unprovable
;; hyps (subsetp a y) and (subsetp y c).  Since we can't relieve these hyps, we
;; fail to rewrite (subsetp a c).
;;
;; What we need to do, of course, is to somehow also bind y <- b.  Identifying
;; this binding is the job of our free-variable matching code.  More generally,
;; imagine we have a rule, with free variables, whose left-hand side matches a
;; goal term to rewrite.  Our free-variable code is responsible for suggesting
;; some appropriate bindings for the free variables in our rule.
;;
;; Now we run into some tension in our design.
;;
;;   - Every sigma we suggest is more work for the rewriter (because it needs
;;     to try to relieve each hyp/sigma), so we want to suggest relatively few
;;     sigmas for efficiency.
;;
;;   - On the other hand, if there is a working sigma we fail to suggest, the
;;     rule will not be applied and we may stupidly fail to make progress just
;;     because we are too dumb to see the right sigma.
;;
;; We want to make the useful and obvious suggestions, but in general we are
;; happier to err on the side of stupidity than slow our rewriter to a crawl
;; trying probably-useless sigmas.  Our strategy is intended to be similar in
;; spirit to ACL2's approach, although it is not implemented in the same way.
;;
;; Suppose there are k free variables, v1 through vk.  Let crit(vi) refer to
;; the first hypothesis which mentions vi.  Call the set of all such hyps the
;; CRICTICAL HYPS.  Our strategy is to suggest only sigmas which, in a fairly
;; trivial way, can be sure to satisfy all the critical hyps.  We accomplish
;; this by consulting our assms.  The assms structure stores all of the things
;; we can assume while performing the rewrite.  We can ask the assumptions
;; system for a list of the terms which are known to be true, and try to see if
;; any of these terms can match our critical hyp.

(defund rw.collect-critical-hyps (freevars hyps)
  ;; Freevars are a list of variables, and hyps are terms.  We keep the "first"
  ;; hyp for each free variable.
  (declare (xargs :guard (and (logic.variable-listp freevars)
                              (logic.term-listp hyps))))
  (if (and (consp hyps)
           (consp freevars))
      (let ((hypvars (logic.term-vars (car hyps))))
        (if (disjointp hypvars freevars)
            ;; None of the freevars are in this hyp; this hyp is not critical.
            (rw.collect-critical-hyps freevars (cdr hyps))
          ;; Some of the freevars are here; this hyp is critical.
          (cons (car hyps) (rw.collect-critical-hyps (fast-difference$ freevars hypvars nil) (cdr hyps)))))
    ;; Otherwise, if we have run out of hyps or freevars, so nothing else can be
    ;; critical.
    nil))

(defthm subsetp-of-rw.collect-critical-hyps
  (subsetp (rw.collect-critical-hyps freevars hyps) hyps)
  :hints(("Goal" :in-theory (enable rw.collect-critical-hyps))))



(defund rw.critical-hyps (lhs hyps)
  ;; Given the lhs and hyps from a rule, we construct the list of crithyps.
  ;; This should be used when creating rewrite rules as the value for the
  ;; crithyps parameter.
  (declare (xargs :guard (and (logic.termp lhs)
                              (rw.hyp-listp hyps))))
  (let* ((hypterms (rw.hyp-list-terms hyps))
         (hypvars  (logic.term-list-vars hypterms))
         (lhsvars  (logic.term-vars lhs))
         (freevars (fast-difference$ hypvars lhsvars nil)))
    (rw.collect-critical-hyps freevars hypterms)))

(defthm subsetp-of-rw.critical-hyps
  (subsetp (rw.critical-hyps lhs hyps) (rw.hyp-list-terms hyps))
  :hints(("Goal" :in-theory (enable rw.critical-hyps))))

(defthm logic.term-listp-of-rw.critical-hyps
  (implies (rw.hyp-listp hyps)
           (logic.term-listp (rw.critical-hyps lhs hyps)))
  :hints(("Goal"
          :in-theory (disable subsetp-of-rw.critical-hyps)
          :use ((:instance subsetp-of-rw.critical-hyps)))))




(defund rw.limit-hyps-aux (freevars hyps)
  ;; Freevars are a list of variables and hyps are the hypp structures from the
  ;; rule.  We add a blimit of 0 to every critical hyp.
  (declare (xargs :guard (and (logic.variable-listp freevars)
                              (rw.hyp-listp hyps))))
  (if (consp hyps)
      (let ((hypvars (logic.term-vars (rw.hyp->term (car hyps)))))
        (if (disjointp hypvars freevars)
            ;; This hyp is not critical.
            (cons (car hyps) (rw.limit-hyps-aux freevars (cdr hyps)))
          ;; Some of the freevars are here; this hyp is critical.
          (cons (rw.hyp (rw.hyp->term (car hyps))
                        (rw.hyp->fmode (car hyps))
                        t ;; limitp
                        0 ;; limit
                        )
                (rw.limit-hyps-aux (fast-difference$ freevars hypvars nil) (cdr hyps)))))
    nil))

(defund rw.limit-hyps (lhs hyps)
  ;; Given the lhs and the hyps from a rule, we construct a new list of hyps
  ;; where each crithyp has been backchain-limited to 0.  This seems to make
  ;; our free-variable rules cheaper.
  ;;
  ;; BOZO why is this necessary?  Shouldn't the rules get rewritten to true
  ;; by virtue of our find-extensions code?
  (declare (xargs :guard (and (logic.termp lhs)
                              (rw.hyp-listp hyps))))
  (let* ((hypterms (rw.hyp-list-terms hyps))
         (hypvars  (logic.term-list-vars hypterms))
         (lhsvars  (logic.term-vars lhs))
         (freevars (fast-difference$ hypvars lhsvars nil)))
    (rw.limit-hyps-aux freevars hyps)))




(defund rw.find-extensions-for-sigma-aux (hyp trueterms sigma acc)
  ;; - Hyp is a hypothesis from our rule (one of the critical hyps) which
  ;;   does not have one of the special "equal" or "iff" forms.
  ;; - Trueterms are the list of all the terms we "know" are true, and
  ;; - Sigma is a substitution list which probably binds some of the
  ;;   variables in hyp, but probably does not bind them all.
  ;;
  ;; We try to match our hyp against each trueterm under sigma.  A successful
  ;; match will result in a new sigma that gives bindings to the other
  ;; variables in hyp.  We return the a list of all these extended sigmas.
  (declare (xargs :guard (and (logic.termp hyp)
                              (logic.term-listp trueterms)
                              (logic.sigmap sigma)
                              (logic.sigma-listp acc))))
  (if (consp trueterms)
      (let ((match-result (logic.patmatch hyp (car trueterms) sigma)))
        (rw.find-extensions-for-sigma-aux hyp (cdr trueterms) sigma
                                          (if (and (not (equal 'fail match-result))
                                                   (not (memberp match-result acc)))
                                              (cons match-result acc)
                                            acc)))
    acc))

(defthm forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-aux
  (implies (force (and (logic.termp hyp)
                       (logic.term-listp trueterms)
                       (logic.sigmap sigma)
                       (logic.sigma-listp acc)))
           (equal (logic.sigma-listp (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-aux))))

(defthm forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-aux
  (implies (force (and (logic.term-atblp hyp atbl)
                       (logic.term-list-atblp trueterms atbl)
                       (logic.sigma-atblp sigma atbl)
                       (logic.sigma-list-atblp acc atbl)))
           (equal (logic.sigma-list-atblp (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-aux))))

(defthm submap-of-eachp-of-rw.find-extensions-for-sigma-aux
  (implies (submap-of-eachp sigma acc)
           (submap-of-eachp sigma (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc)))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-aux))))

(defthm submap-of-eachp-of-rw.find-extensions-for-sigma-aux-free
  (implies (and (submapp sig sigma)
                (submap-of-eachp sig acc))
           (equal (submap-of-eachp sig (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-aux))))



(defund rw.find-extensions-for-sigma (hyp trueterms sigma acc)
  ;; - Hyp is a hypothesis from our rule (one of the critical hyps) which
  ;;   does not have one of the special "equal" or "iff" forms.
  ;; - Trueterms are the list of all the terms we "know" are true, and
  ;; - Sigma is a substitution list which probably binds some of the
  ;;   variables in hyp, but probably does not bind them all.
  (declare (xargs :guard (and (logic.termp hyp)
                              (logic.term-listp trueterms)
                              (logic.sigmap sigma)
                              (logic.sigma-listp acc))))
  (if (and (logic.functionp hyp)
           (memberp (logic.function-name hyp) '(equal iff))
           (tuplep 2 (logic.function-args hyp)))
      ;; As a special consideration for (equal x y) and (iff x y), we try to also
      ;; find matches for (equal y x) and (iff y x).
      (let ((commuted-hyp (logic.function (logic.function-name hyp)
                                          (list (second (logic.function-args hyp))
                                                (first  (logic.function-args hyp))))))
        (rw.find-extensions-for-sigma-aux commuted-hyp trueterms sigma
         (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc)))
    ;; All other functions we just search for normally.
    (rw.find-extensions-for-sigma-aux hyp trueterms sigma acc)))

(defthm forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma
  (implies (force (and (logic.termp hyp)
                       (logic.term-listp trueterms)
                       (logic.sigmap sigma)
                       (logic.sigma-listp acc)))
           (equal (logic.sigma-listp (rw.find-extensions-for-sigma hyp trueterms sigma acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma))))

(defthm forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma
  (implies (force (and (logic.termp hyp)
                       (logic.term-atblp hyp atbl)
                       (logic.term-list-atblp trueterms atbl)
                       (logic.sigma-atblp sigma atbl)
                       (logic.sigma-list-atblp acc atbl)))
           (equal (logic.sigma-list-atblp (rw.find-extensions-for-sigma hyp trueterms sigma acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma))))

(defthm submap-of-eachp-of-rw.find-extensions-for-sigma
  (implies (submap-of-eachp sigma acc)
           (submap-of-eachp sigma (rw.find-extensions-for-sigma hyp trueterms sigma acc)))
  :hints(("Goal" :in-theory (e/d (rw.find-extensions-for-sigma)
                                 ((:executable-counterpart ACL2::force))))))

(defthm submap-of-eachp-of-rw.find-extensions-for-sigma-free
  (implies (and (submapp sig sigma)
                (submap-of-eachp sig acc))
           (equal (submap-of-eachp sig (rw.find-extensions-for-sigma hyp trueterms sigma acc))
                  t))
  :hints(("Goal" :in-theory (e/d (rw.find-extensions-for-sigma)
                                 ((:executable-counterpart ACL2::force))))))





(defund rw.find-extensions-for-sigma-list (hyp trueterms sigmas acc)
  ;; - Hyp is a hypothesis from our rule (one of the critical hyps),
  ;; - Trueterms are the list of all the terms we "know" are true, and
  ;; - Sigmas are the a list of sigmas that work so far.
  ;;
  ;; We try to match our hyp against each trueterm under each sigma.  Each
  ;; successful match results in a new sigma that binds all the variables
  ;; in hyp.  We return the list of all these extended sigmas.
  (declare (xargs :guard (and (logic.termp hyp)
                              (logic.term-listp trueterms)
                              (logic.sigma-listp sigmas)
                              (logic.sigma-listp acc))))
  (if (consp sigmas)
      (rw.find-extensions-for-sigma-list hyp trueterms (cdr sigmas)
                                         (rw.find-extensions-for-sigma hyp trueterms (car sigmas) acc))
    acc))

(defthm forcing-logic.sigma-listp-of-rw.find-extensions-for-sigma-list
  (implies (force (and (logic.termp hyp)
                       (logic.term-listp trueterms)
                       (logic.sigma-listp sigmas)
                       (logic.sigma-listp acc)))
           (equal (logic.sigma-listp (rw.find-extensions-for-sigma-list hyp trueterms sigmas acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-list))))

(defthm forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-sigma-list
  (implies (force (and (logic.termp hyp)
                       (logic.term-atblp hyp atbl)
                       (logic.term-list-atblp trueterms atbl)
                       (logic.sigma-list-atblp sigmas atbl)
                       (logic.sigma-list-atblp acc atbl)))
           (equal (logic.sigma-list-atblp (rw.find-extensions-for-sigma-list hyp trueterms sigmas acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-list))))

(defthm submap-of-eachp-of-rw.find-extensions-for-sigma-list
  (implies (and (submap-of-eachp sig sigmas)
                (submap-of-eachp sig acc))
           (equal (submap-of-eachp sig (rw.find-extensions-for-sigma-list hyp trueterms sigmas acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-sigma-list))))




(defund rw.find-extensions-for-crit-hyps (hyps trueterms sigmas)
  ;; - Hyps are the critical hyps we have not yet dealt with
  ;; - Trueterms are the list of all the terms we "know" are true, and
  ;; - Sigmas are a list of all the sigmas that work so far
  ;;
  ;; We try to find all the extensions of our sigmas which satisfy all these
  ;; hyps.
  (declare (xargs :guard (and (logic.term-listp hyps)
                              (logic.term-listp trueterms)
                              (logic.sigma-listp sigmas))))
  (if (consp hyps)
      (let ((new-sigmas (rw.find-extensions-for-sigma-list (car hyps) trueterms sigmas nil)))
        (if new-sigmas
            (rw.find-extensions-for-crit-hyps (cdr hyps) trueterms new-sigmas)
          ;; None of the sigmas could be extended to satisfy the first hyp.
          ;; Well then, certainly none of them will satisfy all of our hyps.
          nil))
    sigmas))

(defthm forcing-logic.sigma-listp-of-rw.find-extensions-for-crit-hyps
  (implies (force (and (logic.term-listp hyps)
                       (logic.term-listp trueterms)
                       (logic.sigma-listp sigmas)))
           (equal (logic.sigma-listp (rw.find-extensions-for-crit-hyps hyps trueterms sigmas))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-crit-hyps))))

(defthm forcing-logic.sigma-list-atblp-of-rw.find-extensions-for-crit-hyps
  (implies (force (and (logic.term-listp hyps)
                       (logic.term-list-atblp hyps atbl)
                       (logic.term-list-atblp trueterms atbl)
                       (logic.sigma-list-atblp sigmas atbl)))
           (equal (logic.sigma-list-atblp (rw.find-extensions-for-crit-hyps hyps trueterms sigmas) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-crit-hyps))))

(defthm submap-of-eachp-of-rw.find-extensions-for-crit-hyps
  (implies (submap-of-eachp sig sigmas)
           (equal (submap-of-eachp sig (rw.find-extensions-for-crit-hyps hyps trueterms sigmas))
                  t))
  :hints(("Goal" :in-theory (enable rw.find-extensions-for-crit-hyps))))




(defund rw.create-sigmas-to-try (rule sigma trueterms)
  ;; - Rule is the rewrite rule we are using.
  ;; - Sigma is the partial substitution which unifies the target term with our rule's lhs.
  ;; - Assms are the current assumptions.
  ;;
  ;; We create a list of all the sigmas we want to try matching with.
  (declare (xargs :guard (and (rw.rulep rule)
                              (logic.sigmap sigma)
                              (logic.term-listp trueterms))))
  (let ((crithyps (rw.rule->crithyps rule)))
    (if crithyps
        ;; There are crithyps so there are free variables to match.  Try to fill them in
        ;; using the assms structure to make our guesses.
        (rw.find-extensions-for-crit-hyps crithyps
                                          trueterms
                                          (list sigma))
      ;; There are no crithyps so there are no freevars to match; we just try the
      ;; sigma that matches the whole lhs.
      (list sigma))))

(defthm forcing-logic.sigma-listp-of-rw.create-sigmas-to-try
  (implies (force (and (rw.rulep rule)
                       (logic.sigmap sigma)
                       (logic.term-listp trueterms)))
           (equal (logic.sigma-listp (rw.create-sigmas-to-try rule sigma trueterms))
                  t))
  :hints(("Goal" :in-theory (enable rw.create-sigmas-to-try))))

(defthm forcing-logic.sigma-list-atblp-of-rw.create-sigmas-to-try
  (implies (force (and (rw.rulep rule)
                       (rw.rule-atblp rule atbl)
                       (logic.sigma-atblp sigma atbl)
                       (logic.term-listp trueterms)
                       (logic.term-list-atblp trueterms atbl)))
           (equal (logic.sigma-list-atblp (rw.create-sigmas-to-try rule sigma trueterms) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.create-sigmas-to-try))))

(defthm submap-of-eachp-of-rw.create-sigmas-to-try
  (equal (submap-of-eachp sigma (rw.create-sigmas-to-try rule sigma trueterms))
         t)
  :hints(("Goal" :in-theory (enable rw.create-sigmas-to-try))))


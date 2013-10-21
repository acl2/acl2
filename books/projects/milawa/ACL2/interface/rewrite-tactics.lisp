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
(include-book "simple-tactics")


;; Rewriting control variables
;;
;; Our rewriting tactics have several parameters.  We use more variables to
;; hold these parameters and provide some functions for setting them.


;; UFASTP is the flag for using the fast unconditional rewriter.  This is kind
;; of subtle.
;;
;;   - At low levels, it will improve proof-finding times, but slow down
;;     overall proof time (because the slow urewrite has to be used during the
;;     build.)
;;
;;   - At high levels, it will improve proof-finding and building times, and
;;     result in much smaller proofs (urewriting is one step).  It's not clear
;;     whether the generated proofs would take longer to check or not; it's a
;;     question of whether looking up the rules and doing the pattern matching
;;     is more expensive than checking many steps in a trace.
;;
;; CFASTP is the same, for the fast conditional rewriter.

(ACL2::table tactic-harness 'ufastp nil)
(ACL2::table tactic-harness 'cfastp nil)

(defun tactic.harness->ufastp (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'ufastp (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->cfastp (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'cfastp (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->noexec (acl2-world)
  (declare (xargs :mode :program))
  (tactic.world->noexec (tactic.harness->world acl2-world)))

(defun tactic.update-noexec-wrapper (add rem world)
  (declare (xargs :mode :program))
  (tactic.update-noexec add rem world))

(defun tactic.update-noexec-tac-wrapper (skelly add rem)
  (declare (xargs :mode :program))
  (tactic.update-noexec-tac skelly add rem))

(defmacro %noexec (&rest names)
  ;; %noexec instructs the rewriter not to try to evaluate terms whose leading
  ;; function symbol is name.
  `(ACL2::progn
    ;; Step 1: Update the global world.
    (ACL2::table tactic-harness 'world
                 (let* ((add        ',names)
                        (rem        nil)
                        (world      (tactic.harness->world ACL2::world)))
                   (tactic.update-noexec-wrapper add rem world)))
    ;; Step 2: Update the skeleton, if there currently is one.
    (ACL2::table tactic-harness 'skeleton
                 (let* ((add        ',names)
                        (rem        nil)
                        (skelly     (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.update-noexec-tac-wrapper skelly add rem))))))

(defmacro %exec (&rest names)
  ;; %exec permits the rewriter not to try to evaluate terms whose leading
  ;; function symbol is name.
  `(ACL2::progn
    ;; Step 1: Update the global world.
    (ACL2::table tactic-harness 'world
                 (let* ((add        nil)
                        (rem        ',names)
                        (world      (tactic.harness->world ACL2::world)))
                   (tactic.update-noexec-wrapper add rem world)))
    ;; Step 2: Update the skeleton, if there currently is one.
    (ACL2::table tactic-harness 'skeleton
                 (let* ((add        nil)
                        (rem        ',names)
                        (skelly     (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.update-noexec-tac-wrapper skelly add rem))))))



(defmacro %betamode (&optional (betamode 'once))
  ;; %betamode can be used to change the current beta-reduction mode
  ;;
  ;; This might be useful if you have a lambda expression with a complex
  ;; actual, and the corresponding formal occurs several times in the body.
  ;; You could first rewrite without beta reduction to simplify the actual, and
  ;; only later enable beta reduction so that the already-simplified actual is
  ;; substituted into the body.  This may help avoid rewriting the same actual
  ;; over and over.
  ;;
  ;; Usage:
  ;;   (%betamode 'once)   Enable a single beta-reduction (the default)
  ;;   (%betamode t)       Enable recursive beta-reduction
  ;;   (%betamode nil)     Disable beta-reduction
  ;;
  (%simple-world-change-fn (list (cons 'betamode betamode))))

(defmacro %forcingp (&optional (forcingp 't))
  ;; %forcingp can be used to enable or disable forcing by crewrite.
  ;;
  ;; Usage:
  ;;   (%forcingp)      Enable forcing (the default)
  ;;   (%forcingp nil)  Disable forcing
  ;;
  (%simple-world-change-fn (list (cons 'forcingp (if forcingp t nil)))))

(defmacro %blimit (&optional (n '50))
  ;; %blimit can be used to change the backchain limit for our rewriters.
  ;;
  ;; Each time we try to apply a rule with hypotheses, we must show the hyps
  ;; are true.  We do this by recursively rewriting each hyp.  To ensure this
  ;; type of recursion terminates, we decrease the blimit each time we enter
  ;; the rewriter to relieve a hyp, and we are not allowed to recur if the
  ;; blimit reaches zero.
  ;;
  ;; Each hypothesis of a rewrite rule can also specify its own limit.  When
  ;; this occurs, we use the minimum of the current backchain limit and the
  ;; hyp's limit.  The intended effect is to allow rules to say, "This hyp
  ;; might be expensive, so only try to prove it if you can do so cheaply."
  ;;
  ;; Usage:
  ;;   (%blimit)      Revert to the default backchain limit
  ;;   (%blimit n)    Change the backchain limit to n
  ;;
  (%simple-world-change-fn (list (cons 'blimit (nfix n)))))

(defmacro %rlimit (&optional (n '100))
  ;; %rlimit can be used to change the rewrite limit for our rewriters.
  ;;
  ;; Whenever we successfully rewrite a term to term', we immediately try to
  ;; rewrite term' again.  To prevent an infinite recursion, we only do this
  ;; if the rlimit has not been reached.
  ;;
  ;; Why not just rewrite it in the next pass?  As one example, suppose we are
  ;; trying to relieve a hypothesis like (subsetp (rev a) a).  We might apply
  ;; the rule (subsetp (rev x) x) = (subsetp x x) to obtain (subsetp a a), but
  ;; now unless we also try to rewrite this result we will not notice that it
  ;; is t.  By rewriting it again, we can relieve the hyp and make more
  ;; progress.
  ;;
  ;; Hitting the rlimit should be very rare, so we print a warning if you
  ;; manage to do it.
  ;;
  ;; Usage:
  ;;   (%rlimit)      Revert to the default backchain limit
  ;;   (%rlimit n)    Change the backchain limit to n
  ;;
  (%simple-world-change-fn (list (cons 'rlimit (nfix n)))))


(defmacro %depth (&optional (n '500))
  ;; %depth can be used to change the stack depth for evaulation.
  ;;
  ;; A message is printed if you hit the depth.
  ;;
  ;; Usage:
  ;;   (%depth)      Revert to the default stack depth
  ;;   (%depth n)    Change the backchain limit to n
  ;;
  (%simple-world-change-fn (list (cons 'depth (nfix n)))))

(defmacro %rwn (&optional (n '20))
  ;; %rwn can be used to change the number of rewriting passes which will be
  ;; attempted by crewrite.
  ;;
  ;; A warning will be printed if you run out of steps.  If you see such a
  ;; warning, you can decide if you want to apply additional passes.
  ;;
  ;; Usage:
  ;;   (%rwn)      Revert to the default number of passes
  ;;   (%rwn n)    Change to number of passes to n
  ;;
  (%simple-world-change-fn (list (cons 'rwn (nfix n)))))

(defmacro %urwn (&optional (n '20))
  ;; %urwn can be used to change the number of rewriting passes which will be
  ;; attempted by urewrite.
  ;;
  ;; A warning will be printed if you run out of steps.  If you see such a
  ;; warning, you can decide if you want to apply additional passes.
  ;;
  ;; Usage:
  ;;   (%urwn)      Revert to the default number of passes
  ;;   (%urwn n)    Change to number of passes to n
  ;;
  (%simple-world-change-fn (list (cons 'urwn (nfix n)))))


(defmacro %assmctrl (&key (primaryp 't)
                          (secondaryp 't)
                          (directp 't)
                          (negativep 't))
  ;; %assmctrl can be used to configure the kinds of inference the assumptions
  ;; system makes.  Turning off some of these may make it faster to construct
  ;; the initial assumptions.  On the other hand, it may result in a weaker
  ;; assumptions system which may be less useful, or which will require the
  ;; rewriter to do more on its own.
  ;;
  ;; Usage:
  ;;   (%assmctrl)  -- use the default (all on)
  ;;   (%assmctrl :primaryp nil :secondaryp nil :directp nil :negativep nil)
  ;;      -- turn them all off, or pick and choose
  ;;
  (%simple-world-change-fn (list (cons 'assm-primaryp   (if primaryp t nil))
                                 (cons 'assm-secondaryp (if secondaryp t nil))
                                 (cons 'assm-directp    (if directp t nil))
                                 (cons 'assm-negativep  (if negativep t nil)))))






;; The rewriting tactics

(defun %tactic.urewrite-first-tac-wrapper (x theoryname fastp world warnp)
  (declare (xargs :mode :program))
  (tactic.urewrite-first-tac x theoryname fastp world warnp))

(defun %tactic.urewrite-all-tac-wrapper (x theoryname fastp world warnp)
  (declare (xargs :mode :program))
  (tactic.urewrite-all-tac x theoryname fastp world warnp))

(defmacro %urewrite (theoryname &rest args)
  ;; Rewrite some goals using only unconditional rules.
  ;;
  ;; Usage:
  ;;   (%urewrite <theoryname>)             Rewrite all of the goals
  ;;   (%urewrite <theoryname> first)       Rewrite only the first goal
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (world      (tactic.harness->world    ACL2::world))
                               (fastp      (tactic.harness->ufastp   ACL2::world))
                               (theoryname ',theoryname)
                               (warnp      (tactic.harness->warnp    ACL2::world))
                               (new-skelly (if (memberp 'first ',args)
                                               (%tactic.urewrite-first-tac-wrapper skelly theoryname fastp world warnp)
                                             (%tactic.urewrite-all-tac-wrapper skelly theoryname fastp world warnp))))
                          (or new-skelly skelly))))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))
    (local (%print))))



;; I did not find much worth memoizing, though I looked a fair amount.
;; Anything you add here should also be added to %unmemoize-for-crewrite.
;;
;; At various points I tried to memoize these functions with negative
;; results.  I take away two lessons from this.  One, it's not good to
;; memoize the following functions.  Two, if other functions seem like they
;; might be worth memoizing, be sure to run actual tests to make sure there
;; is an improvement.
;;
;;   logic.flag-patmatch :condition '(ACL2::eq flag 'term)
;;   logic.flag-substitute :condition '(ACL2::eq flag 'term)
;;   rw.theory-lookup
;;   rw.rule-syntax-okp
;;   rw.worse-than-or-equal-termp
;;   rw.create-sigmas-to-try
;;   rw.assumptions-trace (even with clearing its table after each rewrite)
;;
;; These following give almost no advantage in the tests I've done, but
;; maybe they'll help in other proofs that make more use of term-<.  And in
;; any event, they leave this convenient hook for memoizing crewrite.  BOZO
;; try to do some big proofs without these, later on.

;(ACL2::memoize 'logic.flag-count-function-occurrences :condition '(ACL2::eq flag 'term))
;(ACL2::memoize 'logic.flag-count-variable-occurrences :condition '(ACL2::eq flag 'term))
;(ACL2::memoize 'logic.flag-count-constant-sizes :condition '(ACL2::eq flag 'term))

(ACL2::memoize 'logic.count-term-sizes)

(defun %tactic.crewrite-first-tac-wrapper (x theoryname fastp world warnp)
  (declare (xargs :mode :program))
  (tactic.crewrite-first-tac x theoryname fastp world warnp))

(defun %tactic.crewrite-all-tac-wrapper (x theoryname fastp world warnp)
  (declare (xargs :mode :program))
  (tactic.crewrite-all-tac x theoryname fastp world warnp))

(defmacro %crewrite (theoryname &rest args)
  ;; Rewrite some goals using conditional and unconditional rules.
  ;;
  ;; Usage:
  ;;   (%crewrite <theoryname>)             Rewrite all of the goals
  ;;   (%crewrite <theoryname> first)       Rewrite only the first goal
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (world      (tactic.harness->world    ACL2::world))
                               (theoryname ',theoryname)
                               (warnp      (tactic.harness->warnp    ACL2::world))
                               (cfastp     (tactic.harness->cfastp   ACL2::world))
                               (new-skelly (if (memberp 'first ',args)
                                               (%tactic.crewrite-first-tac-wrapper skelly theoryname cfastp world warnp)
                                             (%tactic.crewrite-all-tac-wrapper skelly theoryname cfastp world warnp))))
                          (or new-skelly skelly))))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))
    (local (%print))))


(defun %tactic.waterfall-tac-wrapper (x strategy maxdepth theoryname cfastp ufastp world warnp)
  (declare (xargs :mode :program))
  (tactic.waterfall-tac x strategy maxdepth theoryname cfastp ufastp world warnp))

(defmacro %waterfall (theoryname maxdepth &key (strategy '(urewrite crewrite-once nolift-split split crewrite)))
  `(ACL2::progn
    (local (ACL2::table tactic-harness 'skeleton
                        (let* ((skelly     (tactic.harness->skeleton ACL2::world))
                               (world      (tactic.harness->world    ACL2::world))
                               (ufastp     (tactic.harness->ufastp   ACL2::world))
                               (cfastp     (tactic.harness->cfastp   ACL2::world))
                               (theoryname ',theoryname)
                               (strategy   ',strategy)
                               (maxdepth   ',maxdepth)
                               (warnp      (tactic.harness->warnp    ACL2::world))
                               (new-skelly (%tactic.waterfall-tac-wrapper skelly strategy maxdepth theoryname
                                                                          cfastp ufastp world warnp)))
                          (or new-skelly skelly))))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))
    (local (%print))))






(ACL2::defttag rw.crewrite-mods)

;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)
;;  (ACL2::defun rw.crewrite-clause-list (x blimit rlimit control n)
;;               (if (consp x)
;;                   (let* ((start-time (ACL2::get-internal-run-time))
;;                          (rewritten  (rw.crewrite-clause (car x) blimit rlimit control n))
;;                          (end-time   (ACL2::get-internal-run-time)))
;;                     (ACL2::prog2$
;;                      (ACL2::format t "; Rewrote clause #~a in ~a seconds. (~a)~%"
;;                                    (ACL2::length x)
;;                                    (COMMON-LISP::/
;;                                     (COMMON-LISP::coerce (ACL2::- end-time start-time) 'COMMON-LISP::float)
;;                                     ACL2::internal-time-units-per-second)
;;                                    ;; rewritten is an rw.ccstep-listp
;;                                    (cond ((rw.ccstep->provedp (first rewritten))
;;                                           "proved")
;;                                          ((equal (rw.ccstep->t1prime (first rewritten))
;;                                                  (first (first rewritten)))
;;                                           "failed")
;;                                          (t
;;                                           "progress")))
;;                      (cons rewritten
;;                            (rw.crewrite-clause-list (cdr x) blimit rlimit control n))))
;;                 nil)))

(ACL2::progn!
 (ACL2::set-raw-mode t)


 ;; Step timing.
 ;; Regular crewrite step.

 (ACL2::defparameter *assms-acc* 0)
 (ACL2::defparameter *rw-acc* 0)

 (ACL2::declaim (ACL2::inline rw.crewrite-take-step))
 (ACL2::defun rw.crewrite-take-step (todo done blimit rlimit control n)
              (let* ((astart-time (ACL2::get-internal-run-time))
                     (assms (rw.empty-assms (rw.control->assmctrl control)))
                     (assms (rw.assume-left-list (cdr todo) assms))
                     (assms (rw.assume-right-list done assms))
                     (contr (rw.assms->contradiction assms))
                     (aend-time (ACL2::get-internal-run-time))
                     (up        (ACL2::incf *assms-acc* (ACL2::- aend-time astart-time))))
                (declare (ignore up))
                (rw.ccstep (car todo)
                           (rw.assms->hypbox assms)
                           contr
                           (if (not contr)
                               (let* ((start-time (ACL2::get-internal-run-time))
                                      (val (rw.crewrite assms (car todo) t blimit rlimit control n))
                                      (end-time (ACL2::get-internal-run-time))
                                      (up (ACL2::incf *rw-acc* (ACL2::- end-time start-time))))
                                 (declare (ignore up))
                                 val)
                              nil))))

 (ACL2::defun rw.crewrite-clause-aux (todo done blimit rlimit control n acc)
              (if (consp todo)
                  (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
                    (if (rw.ccstep->provedp step1)
                        (cons step1 acc)
                      (rw.crewrite-clause-aux (cdr todo)
                                              (cons (rw.ccstep->t1prime step1) done)
                                              blimit rlimit control n
                                              (cons step1 acc))))
                acc))

 (ACL2::defun rw.crewrite-clause (clause blimit rlimit control n)
              (rw.crewrite-clause-aux clause nil blimit rlimit control n nil))

 ;; Fast crewrite steps.

 (ACL2::declaim (ACL2::inline rw.fast-crewrite-take-step))
 (ACL2::defun rw.fast-crewrite-take-step (todo done blimit rlimit control n)
              (let* ((astart-time (ACL2::get-internal-run-time))
                     (assms (rw.empty-fast-assms (rw.control->assmctrl control)))
                     (assms (rw.fast-assume-left-list (cdr todo) assms))
                     (assms (rw.fast-assume-right-list done assms))
                     (contr (rw.fast-assms->contradiction assms))
                     (aend-time (ACL2::get-internal-run-time))
                     (up        (ACL2::incf *assms-acc* (ACL2::- aend-time astart-time))))
                (declare (ignore up))
                (rw.fast-ccstep contr
                                (if contr
                                    nil
                                  (let* ((start-time (ACL2::get-internal-run-time))
                                         (val        (rw.fast-crewrite assms (car todo) t blimit
                                                                       rlimit control n))
                                         (end-time (ACL2::get-internal-run-time))
                                         (up (ACL2::incf *rw-acc* (ACL2::- end-time start-time))))
                                    (declare (ignore up))
                                    val)))))

 (acl2::defun rw.fast-crewrite-clause-aux (todo done blimit rlimit control n fgacc)
              (if (consp todo)
                  (let* ((step1          (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                         (step1-contr    (rw.fast-ccstep->contradictionp step1))
                         (step1-provedp  (rw.fast-ccstep->provedp step1))
                         (step1-ftrace   (rw.fast-ccstep->ftrace step1))
                         (step1-fgoals   (and (not step1-contr)
                                              (rw.ftrace->fgoals step1-ftrace))))
                    (if step1-provedp
                        (list t nil (fast-app step1-fgoals fgacc))
                      (rw.fast-crewrite-clause-aux (cdr todo)
                                                   (cons (rw.fast-ccstep->t1prime step1) done)
                                                   blimit rlimit control n
                                                   (fast-app step1-fgoals fgacc))))
                (list nil done fgacc)))

 (acl2::defun rw.fast-crewrite-clause (clause blimit rlimit control n)
              (rw.fast-crewrite-clause-aux clause nil blimit rlimit control n nil))



 (acl2::defun rw.make-crewrite-clause-plan-list (x fastp theoryname world)
              (if (consp x)
                  (let* ((reset1     (COMMON-LISP::setf *assms-acc* 0))
                         (reset2     (COMMON-LISP::setf *rw-acc* 0))
                         (start-time (ACL2::get-internal-run-time))
                         (plan1      (rw.make-crewrite-clause-plan (car x) fastp theoryname world))
                         (end-time   (ACL2::get-internal-run-time))
                         (elapsed    (ACL2::- end-time start-time)))
                    (declare (ignore reset1 reset2))
                    (ACL2::prog2$
                     (let* ((total    (common-lisp::coerce (ACL2::+ *assms-acc* *rw-acc*) 'COMMON-LISP::float))
                            (total    (if (common-lisp::= total 0) 1 total))
                            (assmspct (common-lisp::* (common-lisp::/ *assms-acc* total) 100))
                            (rwpct    (common-lisp::* (common-lisp::/ *rw-acc* total) 100))
                            (wall     (COMMON-LISP::/
                                       (COMMON-LISP::coerce elapsed 'COMMON-LISP::float)
                                       ACL2::internal-time-units-per-second)))
                       (ACL2::format t
                                     "; Rewrote clause #~a in ~a seconds (~a), ~4,2f% assm ~4,2f% rw~%"
                                     (ACL2::length x)
                                     wall
                                     (cond ((rw.crewrite-clause-plan->provedp plan1)
                                            "proved")
                                           ((rw.crewrite-clause-plan->progressp plan1)
                                            "progress")
                                           (t
                                            "failed"))
                                     assmspct
                                     rwpct))
                     (cons plan1
                           (rw.make-crewrite-clause-plan-list (cdr x) fastp theoryname world))))
                nil)))



(defund rw.stop-loop-debugging ()
  (declare (xargs :guard t))
  (ACL2::cw "rw.stop-loop-debugging has not yet been redefined.~%"))

(defun rw.disable-loop-debugging ()
  (declare (xargs :guard t))
  ;; This may be useful if you want to do tricks with rlimit.
  (ACL2::cw "rw.disable-loop-debugging not yet redefined!~%"))

(defun rw.enable-loop-debugging ()
  (declare (xargs :guard t))
  ;; This may be useful if you want to do tricks with rlimit.
  (ACL2::cw "rw.enable-loop-debugging not yet redefined!~%"))

(defmacro %disable-loop-debugging ()
  `(ACL2::value-triple (rw.disable-loop-debugging)))

(defmacro %enable-loop-debugging ()
  `(ACL2::value-triple (rw.enable-loop-debugging)))


(ACL2::progn!
 (ACL2::set-raw-mode t)

 (ACL2::defparameter *rw.loop-debugging-enabled* t)
 (ACL2::defparameter *rw.rlimit-was-reached* nil)

 (ACL2::defun rw.disable-loop-debugging ()
              (ACL2::setf *rw.loop-debugging-enabled* nil)
              (ACL2::setf *rw.rlimit-was-reached* nil)
              (ACL2::cw "Disabling loop debugging altogether.~%"))

 (ACL2::defun rw.enable-loop-debugging ()
              (ACL2::setf *rw.loop-debugging-enabled* t)
              (ACL2::cw "Enabling loop debugging.~%"))

 (ACL2::defun rw.stop-loop-debugging ()
              (ACL2::setf *rw.rlimit-was-reached* nil)
              (ACL2::cw "Stopping loop debugging.~%"))

 ;; When we reach the rlimit we set the flag, and print a message to the user.
 (ACL2::defun rw.rlimit-warn ()
              (if *rw.loop-debugging-enabled*
                  (ACL2::progn
                    (ACL2::cw "WARNING: rlimit exhausted -- the rewriter may be looping!~%")
                    (ACL2::cw "Be sure to run (rw.stop-loop-debugging) if you interrupt!~%")
                    (ACL2::setf *rw.rlimit-was-reached* t)
                    nil)
                nil))

 ;; If the rlimit has been reached, we print a quick summary of each rule we use.
 (ACL2::defun rw.crewrite-rule-trace (hypbox lhs rule sigma iffp traces)
              (ACL2::progn
               (or (not *rw.rlimit-was-reached*)
                   (ACL2::cw "~x0: ~x1~%"
                             (rw.rule->name rule)
                             (logic.substitute (rw.rule->rhs rule) sigma)))
               ;; Keep in sync with rw.crewrite-rule-trace
               (rw.trace 'crewrite-rule hypbox lhs
                         (logic.substitute (rw.rule->rhs rule) sigma)
                         iffp traces (list rule sigma))))

 ;; We stop printing when we get back to an rlimit of five.
 (ACL2::defun rw.rlimit-exit (rlimit trace)
              (declare (ignore trace))
              (if (and *rw.rlimit-was-reached* (ACL2::= rlimit 5))
                  (rw.stop-loop-debugging)
                nil)))





#||

;; Testing out the loop debugger (after loading utilities):

(defsection app-of-app-alt
  (%prove (%rule app-of-app-alt
                 :lhs (app x (app y z))
                 :rhs (app (app x y) z)))
  (%auto)
  (%qed)
  (%enable default app-of-app-alt))

(%prove (%rule demo
               :lhs (app a (app b (app c d)))
               :rhs (app a (app (app b c) d))))
(%crewrite default)

||#



;; We have sometimes wanted to investigate the performance benefits of using
;; caching.  It is tricky to properly redefine the caching functions (we found
;; that just using :redef didn't always seem to work), so we provide these
;; events for enabling and disabling the cache.

(defun rw.disable-caching-fn ()
  (declare (xargs :guard t))
  (ACL2::cw "Error: rw.disable-caching-fn has not been redefined ``under the hood.''~%"))

(defun rw.enable-caching-fn ()
  (declare (xargs :guard t))
  (ACL2::cw "Error: rw.enable-caching-fn has not been redefined ``under the hood.''~%"))

(ACL2::progn!
 (ACL2::set-raw-mode t)
 (ACL2::defun rw.disable-caching-fn ()
              (ACL2::cw "Note: disabling the cache.  This cannot be undone with :u -- ~
                         use (rw.enable-caching) instead.~%")
              (ACL2::cw "Note: ACL2 proofs about rw.cache-update and rw.cache-lookup ~
                         can no longer be trusted!~%")
              (ACL2::eval '(ACL2::defun rw.cache-update (term trace cache)
                                        (declare (ignore term trace))
                                        cache))
              (ACL2::eval '(ACL2::defun rw.cache-lookup (term iffp cache)
                                        (declare (ignore term iffp cache))
                                        nil))
              nil)
 (ACL2::defun rw.enable-caching-fn ()
              (ACL2::cw "Note: restoring the original definitions of rw.cache-update ~
                         and rw.cache-lookup.~%")
              (ACL2::eval '(ACL2::defun rw.cache-update (term trace cache)
                                        (let ((blockp (rw.cache->blockp cache))
                                              (data   (rw.cache->data cache)))
                                          (if (and blockp
                                                   (not (logic.constantp (rw.trace->rhs trace))))
                                              cache
                                            (let* ((entry          (hons-lookup term data))
                                                   (new-cache-line (if (rw.trace->iffp trace)
                                                                       (rw.cacheline (and entry (rw.cacheline->eqltrace (cdr entry))) trace)
                                                                     (rw.cacheline trace (and entry (rw.cacheline->ifftrace (cdr entry))))))
                                                   (new-data       (hons-update term new-cache-line data)))
                                              (rw.cache blockp new-data))))))
              (ACL2::eval '(ACL2::defun rw.cache-lookup (term iffp cache)
                                        (let ((entry (hons-lookup term (rw.cache->data cache))))
                                          (and entry
                                               (if iffp
                                                   (rw.cacheline->ifftrace (cdr entry))
                                                 (rw.cacheline->eqltrace (cdr entry)))))))
              nil))

(defmacro rw.disable-caching ()
  `(ACL2::value-triple (rw.disable-caching-fn)))

(defmacro rw.enable-caching ()
  `(ACL2::value-triple (rw.enable-caching-fn)))



; provide waterfall timing info

(ACL2::progn!
 (ACL2::set-raw-mode t)

 (ACL2::defun rw.waterfall-list-wrapper (x theoryname cfastp ufastp world steps strategy n)
              (if (consp x)
                  (let* ((start-time (ACL2::get-internal-run-time))
                         (result     (rw.waterfall (car x) theoryname cfastp ufastp world steps strategy n))
                         (end-time   (ACL2::get-internal-run-time))
                         (elapsed    (ACL2::- end-time start-time))
                         (wall       (COMMON-LISP::/
                                      (COMMON-LISP::coerce elapsed 'COMMON-LISP::float)
                                      ACL2::internal-time-units-per-second)))
                    (ACL2::prog2$
                     (ACL2::format t
                                   ";; Waterfall: clause #~a took ~a seconds, producing ~a subgoals~%"
                                   (ACL2::length x)
                                   wall
                                   (ACL2::length (rw.waterfall-subgoals result)))
                     (cons result
                           (rw.waterfall-list-wrapper (cdr x) theoryname cfastp ufastp world steps strategy n))))
                nil)))


; urewrite timing


(ACL2::progn!
 (ACL2::set-raw-mode t)

 (ACL2::defun rw.world-urewrite-list-list (X THEORYNAME WORLD)
              (if (consp x)
                  (let* ((start-time (ACL2::get-internal-run-time))
                         (result     (rw.world-urewrite-list (car x) theoryname world))
                         (end-time   (ACL2::get-internal-run-time))
                         (elapsed    (ACL2::- end-time start-time))
                         (wall       (COMMON-LISP::/
                                      (COMMON-LISP::coerce elapsed 'COMMON-LISP::float)
                                      ACL2::internal-time-units-per-second)))
                    (ACL2::prog2$
                     (ACL2::format t
                                   ";; Urewrite #~a: ~a seconds.~%"
                                   (ACL2::length x)
                                   wall)
                     (cons result
                           (rw.world-urewrite-list-list (cdr x) theoryname world))))
                nil))

 (ACL2::DEFUN RW.FAST-WORLD-UREWRITE-LIST-LIST (X THEORYNAME WORLD)
              (IF (CONSP X)
                  (let* ((start-time (ACL2::get-internal-run-time))
                         (result     (rw.fast-world-urewrite-list (car x) theoryname world))
                         (end-time   (ACL2::get-internal-run-time))
                         (elapsed    (ACL2::- end-time start-time))
                         (wall       (COMMON-LISP::/
                                      (COMMON-LISP::coerce elapsed 'COMMON-LISP::float)
                                      ACL2::internal-time-units-per-second)))
                    (ACL2::prog2$
                     (ACL2::format t
                                   ";; Fast urewrite #~a: ~a seconds.~%"
                                   (ACL2::length x)
                                   wall)
                     (cons result
                           (rw.fast-world-urewrite-list-list (cdr x) theoryname world))))
                  nil)))


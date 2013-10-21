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
(include-book "traces/basic-builders")
(include-book "traces/urewrite-builders")
(include-book "traces/crewrite-builders")
(include-book "assms/fast")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defthm lookup-of-rev-when-uniquep-of-domain
  (implies (uniquep (domain x))
           (equal (lookup a (rev x))
                  (lookup a x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :shared-hyp (uniquep (domain sigma))
  :thms ((term logic.substitute-of-rev-when-unique
               (implies (subsetp (logic.term-vars x) (domain sigma))
                        (equal (logic.substitute x (rev sigma))
                               (logic.substitute x sigma))))
         (t logic.substitute-list-of-rev-when-unique
            (implies (subsetp (logic.term-list-vars x) (domain sigma))
                     (equal (logic.substitute-list x (rev sigma))
                            (logic.substitute-list x sigma)))))
  :hints(("Goal"
          :induct (logic.term-induction flag x)
          :expand ((logic.substitute x (rev sigma))
                   (logic.substitute x sigma)))))



;; FAST TRACES.
;;
;; The fast crewriter uses "fast traces" in place of the regular traces that
;; are constructed by crewrite.
;;
;; Whereas a regular trace includes everything we need to prove that the
;; rewrite was conducted correctly, fast traces contain almost nothing --
;; just the resulting "right hand side" and any goals that were forced along
;; the way.
;;
;; Compared to regular traces, they are:
;;
;;   - Much smaller in terms of memory usage (because there is nothing recursive
;;     about a fast trace, so previous work can be thrown away immediately),
;;
;;   - Faster to construct (because there is much less consing), and
;;
;;   - Less useful during bootstrapping (because we have no method of compiling
;;     a fast trace into a proof, so we can't make use of the fast crewriter
;;     until we verify it.)

(defaggregate rw.ftrace
  ;; An FTRACE ("fast trace") records the rhs resulting from taking a crewrite
  ;; step and a list of all the forced goals we need to prove in order to have
  ;; gotten this far.
  (rhs fgoals)
  :require ((logic.termp-of-rw.ftrace->rhs            (logic.termp rhs))
            (logic.formula-listp-of-rw.ftrace->fgoals (logic.formula-listp fgoals))
            (true-listp-of-rw.ftrace->fgoals          (true-listp fgoals)))
  :legiblep nil)

(defaggregate rw.ftraces
  ;; Originally, we just used a deflist to introduce fast-trace-listp.  But
  ;; then we realized that all we ever wanted to do with such a list was look
  ;; at its list of rhses and its list of fgoals.  This was inefficient, since
  ;; to inspect these lists we had to cons them up each time.
  ;;
  ;; An FTRACES ("fast traces") is a more efficient version of fast-trace-listp.
  ;; It keeps all of the rhses together in a list so they can be accessed with
  ;; no consing.  It also merges together the fgoals from all of the traces.
  (rhses fgoals)
  :require ((logic.term-listp-of-rw.ftraces->rhses     (logic.term-listp rhses))
            (true-listp-of-rw.ftraces->rhses           (true-listp rhses))
            (logic.formula-listp-of-rw.ftraces->fgoals (logic.formula-listp fgoals))
            (true-listp-of-rw.ftraces->fgoals          (true-listp fgoals)))
  :legiblep nil)

(defthm equal-of-rw.ftraces-and-rw.ftraces
  (equal (equal (rw.ftraces rhses fgoals)
                (rw.ftraces rhses2 fgoals2))
         (and (equal rhses rhses2)
              (equal fgoals fgoals2)))
  :hints(("Goal" :in-theory (enable rw.ftraces))))




(defsection rw.trace-fast-image

  (defund rw.trace-fast-image (x)
    (declare (xargs :guard (rw.tracep x)))
    (rw.ftrace (rw.trace->rhs x)
               (rw.collect-forced-goals x)))

  (local (in-theory (enable rw.trace-fast-image)))

  (defthm rw.trace-fast-image-under-iff
    (iff (rw.trace-fast-image x)
         t))

  (defthm rw.ftracep-of-rw.trace-fast-image
    (implies (force (rw.tracep x))
             (equal (rw.ftracep (rw.trace-fast-image x))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.trace-fast-image
    (equal (rw.ftrace->rhs (rw.trace-fast-image trace))
           (rw.trace->rhs trace)))

  (defthm rw.ftrace->rhs-of-rw.trace-fast-image-free
    (implies (equal (rw.trace-fast-image trace) ftrace)
             (equal (rw.ftrace->rhs ftrace)
                    (rw.trace->rhs trace))))

  (defthm rw.ftrace->fgoals-of-rw.trace-fast-image
    (equal (rw.ftrace->fgoals (rw.trace-fast-image trace))
           (rw.collect-forced-goals trace)))

  (defthm rw.ftrace->fgoals-of-rw.trace-fast-image-free
    (implies (equal (rw.trace-fast-image trace) ftrace)
             (equal (rw.ftrace->fgoals ftrace)
                    (rw.collect-forced-goals trace)))))



(defsection rw.trace-list-fast-image

  (defund rw.trace-list-fast-image (x)
    (declare (xargs :guard (rw.trace-listp x)))
    (rw.ftraces (rw.trace-list-rhses x)
                (rw.collect-forced-goals-list x)))

  (local (in-theory (enable rw.trace-list-fast-image)))

  (defthm rw.ftracesp-of-rw.trace-list-fast-image
    (implies (force (rw.trace-listp x))
             (equal (rw.ftracesp (rw.trace-list-fast-image x))
                    t)))

  (defthm rw.ftraces->rhses-of-rw.trace-list-fast-image
    (equal (rw.ftraces->rhses (rw.trace-list-fast-image traces))
           (rw.trace-list-rhses traces)))

  (defthm rw.ftraces->fgoals-of-rw.trace-list-fast-image
    (equal (rw.ftraces->fgoals (rw.trace-list-fast-image traces))
           (rw.collect-forced-goals-list traces)))

  (defthm rw.ftraces->rhses-of-rw.trace-list-fast-image-free
    (implies (equal (rw.trace-list-fast-image traces) ftraces)
             (equal (rw.ftraces->rhses ftraces)
                    (rw.trace-list-rhses traces))))

  (defthm rw.ftraces->fgoals-of-rw.trace-list-fast-image-free
    (implies (equal (rw.trace-list-fast-image traces) ftraces)
             (equal (rw.ftraces->fgoals ftraces)
                    (rw.collect-forced-goals-list traces))))

  (defthm rw.trace-list-fast-image-of-cons
    (equal (rw.trace-list-fast-image (cons a x))
           (rw.ftraces (cons (rw.trace->rhs a)
                             (rw.trace-list-rhses x))
                       (fast-merge (rw.collect-forced-goals a)
                                   (rw.collect-forced-goals-list x))))))





(defsection rw.fast-fail-trace

  (definlined rw.fast-fail-trace (term)
    (declare (xargs :guard (logic.termp term)))
    (rw.ftrace term nil))

  (local (in-theory (e/d (rw.fast-fail-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-fail-trace-under-iff
    (iff (rw.fast-fail-trace x)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-fail-trace
    (implies (force (logic.termp x))
             (equal (rw.ftracep (rw.fast-fail-trace x))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-fail-trace
    (equal (rw.ftrace->rhs (rw.fast-fail-trace x))
           x))

  (defthm rw.ftrace->fgoals-of-rw.fast-fail-trace
    (equal (rw.ftrace->fgoals (rw.fast-fail-trace x))
           nil))

  (defthm rw.trace-fast-image-of-rw.fail-trace
    (equal (rw.trace-fast-image (rw.fail-trace hypbox x iffp))
           (rw.fast-fail-trace x))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))



(defsection rw.fast-transitivity-trace

  (definlined rw.fast-transitivity-trace (x y)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y))))
    (rw.ftrace (rw.ftrace->rhs y)
               (fast-merge (rw.ftrace->fgoals x)
                           (rw.ftrace->fgoals y))))

  (local (in-theory (e/d (rw.fast-transitivity-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-transitivity-trace-under-iff
    (iff (rw.fast-transitivity-trace x y)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-transitivity-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)))
             (equal (rw.ftracep (rw.fast-transitivity-trace x y))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-transitivity-trace
    (equal (rw.ftrace->rhs (rw.fast-transitivity-trace x y))
           (rw.ftrace->rhs y)))

  (defthm rw.ftrace->fgoals-of-rw.fast-transitivity-trace
    (equal (rw.ftrace->fgoals (rw.fast-transitivity-trace x y))
           (fast-merge (rw.ftrace->fgoals x)
                      (rw.ftrace->fgoals y))))

  (defthm rw.trace-fast-image-of-rw.transitivity-trace
    (equal (rw.trace-fast-image (rw.transitivity-trace x y))
           (rw.fast-transitivity-trace (rw.trace-fast-image x)
                                       (rw.trace-fast-image y)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(defsection rw.fast-equiv-by-args-trace

  (definlined rw.fast-equiv-by-args-trace (f traces)
    (declare (xargs :guard (and (logic.function-namep f)
                                (rw.ftracesp traces))))
    (rw.ftrace (logic.function f (rw.ftraces->rhses traces))
               (rw.ftraces->fgoals traces)))

  (local (in-theory (e/d (rw.fast-equiv-by-args-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-equiv-by-args-trace-under-iff
    (iff (rw.fast-equiv-by-args-trace f traces)
         t))

  (defthm forcing-rw.ftracep-of-rw.equiv-by-args-trace
    (implies (force (and (logic.function-namep f)
                         (rw.ftracesp traces)))
             (equal (rw.ftracep (rw.fast-equiv-by-args-trace f traces))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-equiv-by-args-trace
    (equal (rw.ftrace->rhs (rw.fast-equiv-by-args-trace f traces))
           (logic.function f (rw.ftraces->rhses traces))))

  (defthm rw.ftrace->fgoals-of-rw.fast-equiv-by-args-trace
    (equal (rw.ftrace->fgoals (rw.fast-equiv-by-args-trace f traces))
           (rw.ftraces->fgoals traces)))

  (defthm rw.trace-fast-image-of-rw.equiv-by-args-trace
    (equal (rw.trace-fast-image (rw.equiv-by-args-trace hypbox f iffp traces))
           (rw.fast-equiv-by-args-trace f (rw.trace-list-fast-image traces)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image rw.trace-list-fast-image)))))




(defsection rw.fast-lambda-equiv-by-args-trace

  (definlined rw.fast-lambda-equiv-by-args-trace (formals body traces)
    (declare (xargs :guard (and (true-listp formals)
                                (logic.variable-listp formals)
                                (uniquep formals)
                                (logic.termp body)
                                (subsetp (logic.term-vars body) formals)
                                (rw.ftracesp traces)
                                (equal (len (rw.ftraces->rhses traces)) (len formals)))))
    (rw.ftrace (logic.lambda formals body (rw.ftraces->rhses traces))
               (rw.ftraces->fgoals traces)))

  (local (in-theory (e/d (rw.fast-lambda-equiv-by-args-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-lambda-equiv-by-args-trace-under-iff
    (iff (rw.fast-lambda-equiv-by-args-trace formals body traces)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-lambda-equiv-by-args-trace
    (implies (force (and (true-listp formals)
                         (logic.variable-listp formals)
                         (uniquep formals)
                         (logic.termp body)
                         (subsetp (logic.term-vars body) formals)
                         (rw.ftracesp traces)
                         (equal (len (rw.ftraces->rhses traces))
                                (len formals))))
             (equal (rw.ftracep (rw.fast-lambda-equiv-by-args-trace formals body traces))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-lambda-equiv-by-args-trace
    (equal (rw.ftrace->rhs (rw.fast-lambda-equiv-by-args-trace formals body traces))
           (logic.lambda formals body (rw.ftraces->rhses traces))))

  (defthm rw.ftrace->fgoals-of-rw.fast-lambda-equiv-by-args-trace
    (equal (rw.ftrace->fgoals (rw.fast-lambda-equiv-by-args-trace formals body traces))
           (rw.ftraces->fgoals traces)))

  (defthm rw.trace-fast-image-of-rw.lambda-equiv-by-args-trace
    (equal (rw.trace-fast-image (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
           (rw.fast-lambda-equiv-by-args-trace formals body (rw.trace-list-fast-image traces)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image rw.trace-list-fast-image)))))




(defsection rw.fast-beta-reduction-trace

  (definlined rw.fast-beta-reduction-trace (term)
    (declare (xargs :guard (and (logic.termp term)
                                (logic.lambdap term))))
    (rw.ftrace (logic.substitute (logic.lambda-body term)
                                 (fast-pair-lists$ (logic.lambda-formals term)
                                                   (logic.lambda-actuals term)
                                                   nil))
               nil))

  (local (in-theory (e/d (rw.fast-beta-reduction-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-beta-reduction-trace-under-iff
    (iff (rw.fast-beta-reduction-trace term)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-beta-reduction-trace
    (implies (force (and (logic.termp term)
                         (logic.lambdap term)))
             (equal (rw.ftracep (rw.fast-beta-reduction-trace term))
                    t)))

  (defthm forcing-rw.ftrace->rhs-of-rw.fast-beta-reduction-trace
    (implies (force (and (logic.termp term)
                         (logic.lambdap term)))
             (equal (rw.ftrace->rhs (rw.fast-beta-reduction-trace term))
                    (logic.substitute (logic.lambda-body term)
                                      (pair-lists (logic.lambda-formals term)
                                                  (logic.lambda-actuals term))))))

  (defthm rw.ftrace->fgoals-of-rw.fast-beta-reduction-trace
    (equal (rw.ftrace->fgoals (rw.fast-beta-reduction-trace term))
           nil))

  (defthm rw.trace-fast-image-of-rw.beta-reduction-trace
    (implies (force (and (logic.termp term)
                         (logic.lambdap term)))
             (equal (rw.trace-fast-image (rw.beta-reduction-trace hypbox term iffp))
                    (rw.fast-beta-reduction-trace term)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))





(defsection rw.fast-try-ground-simplify

  (definlined rw.fast-try-ground-simplify (x iffp control)
    (declare (xargs :guard (and (logic.termp x)
                                (logic.groundp x)
                                (booleanp iffp)
                                (rw.controlp control))))
    (if (and (logic.functionp x)
             (memberp (logic.function-name x) (rw.control->noexec control)))
        nil
      (let* ((defs   (rw.control->defs control))
             (depth  (rw.control->depth control))
             (result (generic-evaluator x defs depth)))
        (and result
             (let ((real-result (if (and iffp (not (equal (logic.unquote result) nil)))
                                    ''t
                                  result)))
               (and (not (equal real-result x))
                    (rw.ftrace real-result nil)))))))

  (local (in-theory (enable rw.fast-try-ground-simplify)))

  (defthm rw.ftracep-of-rw.fast-try-ground-simplify
    (implies (force (and (logic.termp x)
                         (logic.groundp x)
                         (rw.controlp control)))
             (equal (rw.ftracep (rw.fast-try-ground-simplify x iffp control))
                    (if (rw.fast-try-ground-simplify x iffp control)
                        t
                      nil))))

  (defthm rw.ftrace->fgoals-of-rw.fast-try-ground-simplify
    (equal (rw.ftrace->fgoals (rw.fast-try-ground-simplify x iffp control))
           nil))

  (defthm rw.trace-fast-image-of-rw.try-ground-simplify
    (implies (force (rw.try-ground-simplify hypbox x iffp control))
             (equal (rw.trace-fast-image (rw.try-ground-simplify hypbox x iffp control))
                    (rw.fast-try-ground-simplify x iffp control)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image
                                      rw.try-ground-simplify
                                      definition-of-rw.collect-forced-goals)))))




(defsection rw.fast-if-specialcase-nil-trace

  (definlined rw.fast-if-specialcase-nil-trace (x y)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y))))
    (rw.ftrace (rw.ftrace->rhs y)
               (fast-merge (rw.ftrace->fgoals x)
                           (rw.ftrace->fgoals y))))

  (local (in-theory (e/d (rw.fast-if-specialcase-nil-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-if-specialcase-nil-trace-under-iff
    (iff (rw.fast-if-specialcase-nil-trace x y)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-if-specialcase-nil-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)))
             (equal (rw.ftracep (rw.fast-if-specialcase-nil-trace x y))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-if-specialcase-nil-trace
    (equal (rw.ftrace->rhs (rw.fast-if-specialcase-nil-trace x y))
           (rw.ftrace->rhs y)))

  (defthm rw.ftrace->fgoals-of-rw.fast-if-specialcase-nil-trace
    (equal (rw.ftrace->fgoals (rw.fast-if-specialcase-nil-trace x y))
           (fast-merge (rw.ftrace->fgoals x)
                       (rw.ftrace->fgoals y))))

  (defthm rw.trace-fast-image-of-rw.if-specialcase-nil-trace
    (equal (rw.trace-fast-image (rw.if-specialcase-nil-trace x y b1))
           (rw.fast-if-specialcase-nil-trace (rw.trace-fast-image x)
                                             (rw.trace-fast-image y)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(defsection rw.fast-if-specialcase-t-trace

  (definlined rw.fast-if-specialcase-t-trace (x y)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y))))
    (rw.ftrace (rw.ftrace->rhs y)
               (fast-merge (rw.ftrace->fgoals x)
                           (rw.ftrace->fgoals y))))

  (local (in-theory (e/d (rw.fast-if-specialcase-t-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-if-specialcase-t-trace-under-iff
    (iff (rw.fast-if-specialcase-t-trace x y)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-if-specialcase-t-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)))
             (equal (rw.ftracep (rw.fast-if-specialcase-t-trace x y))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-if-specialcase-t-trace
    (equal (rw.ftrace->rhs (rw.fast-if-specialcase-t-trace x y))
           (rw.ftrace->rhs y)))

  (defthm rw.ftrace->fgoals-of-rw.fast-if-specialcase-t-trace
    (equal (rw.ftrace->fgoals (rw.fast-if-specialcase-t-trace x y))
           (fast-merge (rw.ftrace->fgoals x)
                       (rw.ftrace->fgoals y))))

  (defthm rw.trace-fast-image-of-rw.if-specialcase-t-trace
    (equal (rw.trace-fast-image (rw.if-specialcase-t-trace x y c1))
           (rw.fast-if-specialcase-t-trace (rw.trace-fast-image x)
                                           (rw.trace-fast-image y)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))





(defsection rw.fast-not-trace

  (definlined rw.fast-not-trace (x)
    (declare (xargs :guard (rw.ftracep x)))
    (rw.ftrace (let ((rhs (rw.ftrace->rhs x)))
                 (cond ((equal rhs ''nil) ''t)
                       ((equal rhs ''t)   ''nil)
                       (t                 (logic.function 'not (list rhs)))))
               (rw.ftrace->fgoals x)))

  (local (in-theory (e/d (rw.fast-not-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-not-trace-under-iff
    (iff (rw.fast-not-trace x)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-not-trace
    (implies (force (rw.ftracep x))
             (equal (rw.ftracep (rw.fast-not-trace x))
                    t)))

  (defthm rw.ftrace->fgoals-of-rw.fast-not-trace
    (equal (rw.ftrace->fgoals (rw.fast-not-trace x))
           (rw.ftrace->fgoals x)))

  (defthm rw.trace-fast-image-of-rw.not-trace
    (equal (rw.trace-fast-image (rw.not-trace x iffp))
           (rw.fast-not-trace (rw.trace-fast-image x)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image
                                      rw.not-trace
                                      definition-of-rw.collect-forced-goals
                                      rw.fast-fail-trace)))))





(defsection rw.fast-negative-if-trace

  (definlined rw.fast-negative-if-trace (x)
    (declare (xargs :guard (logic.termp x)))
    (rw.ftrace (logic.function 'not (list x))
               nil))

  (local (in-theory (e/d (rw.fast-negative-if-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-negative-if-trace-under-iff
    (iff (rw.fast-negative-if-trace x)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-negative-if-trace
    (implies (force (logic.termp x))
             (equal (rw.ftracep (rw.fast-negative-if-trace x))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-negative-if-trace
    (equal (rw.ftrace->rhs (rw.fast-negative-if-trace x))
           (logic.function 'not (list x))))

  (defthm rw.ftrace->fgoals-of-rw.fast-negative-if-trace
    (equal (rw.ftrace->fgoals (rw.fast-negative-if-trace x))
           nil))

  (defthm rw.trace-fast-image-of-rw.negative-if-trace
    (equal (rw.trace-fast-image (rw.negative-if-trace x iffp hypbox))
           (rw.fast-negative-if-trace x))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(defsection rw.fast-crewrite-if-specialcase-same-trace

  (definlined rw.fast-crewrite-if-specialcase-same-trace (x y z)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y)
                                (rw.ftracep z))))
    (rw.ftrace (rw.ftrace->rhs y)
               (fast-merge (rw.ftrace->fgoals x)
                           (fast-merge (rw.ftrace->fgoals y)
                                       (rw.ftrace->fgoals z)))))

  (local (in-theory (e/d (rw.fast-crewrite-if-specialcase-same-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-crewrite-if-specialcase-same-trace-under-iff
    (iff (rw.fast-crewrite-if-specialcase-same-trace x y z)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-crewrite-if-specialcase-same-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)
                         (rw.ftracep z)))
             (equal (rw.ftracep (rw.fast-crewrite-if-specialcase-same-trace x y z))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-crewrite-if-specialcase-same-trace
    (equal (rw.ftrace->rhs (rw.fast-crewrite-if-specialcase-same-trace x y z))
           (rw.ftrace->rhs y)))

  (defthm rw.ftrace->fgoals-of-rw.fast-crewrite-if-specialcase-same-trace
    (equal (rw.ftrace->fgoals (rw.fast-crewrite-if-specialcase-same-trace x y z))
           (fast-merge (rw.ftrace->fgoals x)
                       (fast-merge (rw.ftrace->fgoals y)
                                   (rw.ftrace->fgoals z)))))

  (defthm rw.trace-fast-image-of-rw.crewrite-if-specialcase-same-trace
    (equal (rw.trace-fast-image (rw.crewrite-if-specialcase-same-trace x y z))
           (rw.fast-crewrite-if-specialcase-same-trace (rw.trace-fast-image x)
                                                       (rw.trace-fast-image y)
                                                       (rw.trace-fast-image z)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))





(defsection rw.fast-crewrite-if-generalcase-trace

  (definlined rw.fast-crewrite-if-generalcase-trace (x y z)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y)
                                (rw.ftracep z))))
    (rw.ftrace (logic.function 'if (list (rw.ftrace->rhs x)
                                         (rw.ftrace->rhs y)
                                         (rw.ftrace->rhs z)))
               (fast-merge (rw.ftrace->fgoals x)
                           (fast-merge (rw.ftrace->fgoals y)
                                       (rw.ftrace->fgoals z)))))

  (local (in-theory (e/d (rw.fast-crewrite-if-generalcase-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-crewrite-if-generalcase-trace-under-iff
    (iff (rw.fast-crewrite-if-generalcase-trace x y z)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-crewrite-if-generalcase-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)
                         (rw.ftracep z)))
             (equal (rw.ftracep (rw.fast-crewrite-if-generalcase-trace x y z))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-crewrite-if-generalcase-trace
    (equal (rw.ftrace->rhs (rw.fast-crewrite-if-generalcase-trace x y z))
           (logic.function 'if (list (rw.ftrace->rhs x)
                                     (rw.ftrace->rhs y)
                                     (rw.ftrace->rhs z)))))

  (defthm rw.ftrace->fgoals-of-rw.fast-crewrite-if-generalcase-trace
    (equal (rw.ftrace->fgoals (rw.fast-crewrite-if-generalcase-trace x y z))
           (fast-merge (rw.ftrace->fgoals x)
                       (fast-merge (rw.ftrace->fgoals y)
                                   (rw.ftrace->fgoals z)))))

  (defthm rw.trace-fast-image-of-rw.crewrite-if-generalcase-trace
    (equal (rw.trace-fast-image (rw.crewrite-if-generalcase-trace x y z))
           (rw.fast-crewrite-if-generalcase-trace (rw.trace-fast-image x)
                                                       (rw.trace-fast-image y)
                                                       (rw.trace-fast-image z)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(defsection rw.fast-assumptions-trace

  (definlined rw.fast-assumptions-trace (assms lhs iffp)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp lhs)
                                (booleanp iffp))))
    (let ((result (rw.fast-try-equiv-database lhs (rw.fast-assms->eqdatabase assms) iffp)))
      (and result
           (rw.ftrace result nil))))

  (local (in-theory (e/d (rw.fast-assumptions-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm forcing-rw.ftracep-of-rw.fast-assumptions-trace
    (implies (force (rw.fast-assmsp assms))
             (equal (rw.ftracep (rw.fast-assumptions-trace assms lhs iffp))
                    (if (rw.fast-assumptions-trace assms lhs iffp)
                        t
                      nil))))

  (defthm rw.ftrace->fgoals-of-rw.fast-assumptions-trace
    (equal (rw.ftrace->fgoals (rw.fast-assumptions-trace assms lhs iffp))
           nil))

  (defthm rw.trace-fast-image-of-rw.assumptions-trace
    (implies (force (and (rw.assumptions-trace assms lhs iffp)
                         (rw.assmsp assms)))
             (equal (rw.trace-fast-image (rw.assumptions-trace assms lhs iffp))
                    (rw.fast-assumptions-trace (rw.assms-fast-image assms) lhs iffp)))
    :hints(("Goal"
            ;; Stupid hack to see that it's non-nil.
            :use ((:instance forcing-logic.termp-of-rw.eqtrace->lhs
                             (x (RW.TRY-EQUIV-DATABASE LHS (RW.ASSMS->EQDATABASE ASSMS) IFFP))))
            ;; Gah, ugly.  Oh well.
            :in-theory (e/d (rw.trace-fast-image
                             rw.assms-fast-image
                             rw.assumptions-trace
                             definition-of-rw.collect-forced-goals)
                            (forcing-logic.termp-of-rw.eqtrace->lhs)))))

  ;; We want the theorem below instead for the connection proof.  I'm not sure why.

  (defthmd lemma-for-rw.fast-assumptions-trace-of-rw.assms-fast-image
    (implies (rw.eqtracep x)
             (iff (rw.eqtrace->lhs x)
                  t))
    :hints(("Goal" :in-theory (enable definition-of-rw.eqtracep rw.eqtrace->lhs))))

  (defthm rw.fast-assumptions-trace-of-rw.assms-fast-image
    (implies (and (rw.assmsp assms)
                  (logic.termp x)
                  (booleanp iffp))
             (equal (rw.fast-assumptions-trace (rw.assms-fast-image assms) x iffp)
                    (if (rw.assumptions-trace assms x iffp)
                        (rw.trace-fast-image (rw.assumptions-trace assms x iffp))
                      nil)))
    :hints(("Goal" :in-theory (enable rw.assumptions-trace
                                      rw.fast-assumptions-trace
                                      rw.assms-fast-image
                                      rw.trace-fast-image
                                      definition-of-rw.collect-forced-goals
                                      lemma-for-rw.fast-assumptions-trace-of-rw.assms-fast-image
                                      ))))

  ;; This loops with the above, now.
  (in-theory (disable rw.trace-fast-image-of-rw.assumptions-trace)))




(defsection rw.fast-crewrite-rule-trace

  (definlined rw.fast-crewrite-rule-trace (rule sigma traces)
    (declare (xargs :guard (and (rw.rulep rule)
                                (logic.sigmap sigma)
                                (rw.ftracesp traces))))
    (rw.ftrace (logic.substitute (rw.rule->rhs rule) sigma)
               (rw.ftraces->fgoals traces)))

  (local (in-theory (e/d (rw.fast-crewrite-rule-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-crewrite-rule-trace-under-iff
    (iff (rw.fast-crewrite-rule-trace rule sigma traces)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-crewrite-rule-trace
    (implies (force (and (rw.rulep rule)
                         (logic.sigmap sigma)
                         (rw.ftracesp traces)))
             (equal (rw.ftracep (rw.fast-crewrite-rule-trace rule sigma traces))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-crewrite-rule-trace
    (equal (rw.ftrace->rhs (rw.fast-crewrite-rule-trace rule sigma traces))
           (logic.substitute (rw.rule->rhs rule) sigma)))

  (defthm rw.ftrace->fgoals-of-rw.fast-crewrite-rule-trace
    (equal (rw.ftrace->fgoals (rw.fast-crewrite-rule-trace rule sigma traces))
           (rw.ftraces->fgoals traces)))

  (defthm rw.trace-fast-image-of-rw.crewrite-rule-trace
    (equal (rw.trace-fast-image (rw.crewrite-rule-trace hypbox lhs rule sigma iffp traces))
           (rw.fast-crewrite-rule-trace rule sigma
                                        (rw.trace-list-fast-image traces)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image
                                      rw.trace-list-fast-image)))))




(defsection rw.fast-force-trace

  (definlined rw.fast-force-trace (hypbox lhs)
    (declare (xargs :guard (and (rw.hypboxp hypbox)
                                (logic.termp lhs))))
    (rw.ftrace ''t
               (list (let ((main (logic.pequal (logic.function 'iff (list lhs ''t)) ''t)))
                       (if (or (rw.hypbox->left hypbox)
                               (rw.hypbox->right hypbox))
                           (logic.por (rw.hypbox-formula hypbox) main)
                         main)))))

  (local (in-theory (e/d (rw.fast-force-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-force-trace-under-iff
    (iff (rw.fast-force-trace hypbox lhs)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-force-trace
    (implies (force (and (rw.hypboxp hypbox)
                         (logic.termp lhs)))
             (equal (rw.ftracep (rw.fast-force-trace hypbox lhs))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-force-trace
    (equal (rw.ftrace->rhs (rw.fast-force-trace hypbox lhs))
           ''t))

  (defthm rw.trace-fast-image-of-rw.force-trace
    (equal (rw.trace-fast-image (rw.force-trace hypbox lhs))
           (rw.fast-force-trace hypbox lhs))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image
                                      rw.trace-formula
                                      rw.trace-conclusion-formula)))))



(defsection rw.fast-weakening-trace

  (definlined rw.fast-weakening-trace (trace)
    (declare (xargs :guard (rw.ftracep trace)))
    trace)

  (local (in-theory (e/d (rw.fast-weakening-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-weakening-trace-under-iff
    (iff (rw.fast-weakening-trace x)
         x))

  (defthm forcing-rw.ftracep-of-rw.fast-weakening-trace
    (implies (force (rw.ftracep x))
             (equal (rw.ftracep (rw.fast-weakening-trace x))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-weakening-trace
      (equal (rw.ftrace->rhs (rw.fast-weakening-trace x))
             (rw.ftrace->rhs x)))

  (defthm rw.ftrace->fgoals-of-rw.fast-weakening-trace
      (equal (rw.ftrace->fgoals (rw.fast-weakening-trace x))
             (rw.ftrace->fgoals x)))

  (defthm rw.trace-fast-image-of-rw.weakening-trace
    (equal (rw.trace-fast-image (rw.weakening-trace hypbox x))
           (rw.trace-fast-image x))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(defsection rw.fast-urewrite-if-specialcase-same-trace

  (definlined rw.fast-urewrite-if-specialcase-same-trace (x y)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y))))
    (rw.ftrace (rw.ftrace->rhs x)
               (fast-merge (rw.ftrace->fgoals x)
                           (rw.ftrace->fgoals y))))

  (local (in-theory (e/d (rw.fast-urewrite-if-specialcase-same-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-urewrite-if-specialcase-same-trace-under-iff
    (iff (rw.fast-urewrite-if-specialcase-same-trace x y)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-urewrite-if-specialcase-same-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)))
             (equal (rw.ftracep (rw.fast-urewrite-if-specialcase-same-trace x y))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-urewrite-if-specialcase-same-trace
    (equal (rw.ftrace->rhs (rw.fast-urewrite-if-specialcase-same-trace x y))
           (rw.ftrace->rhs x)))

  (defthm rw.ftrace->fgoals-of-rw.fast-urewrite-if-specialcase-same-trace
    (equal (rw.ftrace->fgoals (rw.fast-urewrite-if-specialcase-same-trace x y))
           (fast-merge (rw.ftrace->fgoals x)
                       (rw.ftrace->fgoals y))))

  (defthm rw.trace-fast-image-of-rw.urewrite-if-specialcase-same-trace
    (equal (rw.trace-fast-image (rw.urewrite-if-specialcase-same-trace x y a))
           (rw.fast-urewrite-if-specialcase-same-trace (rw.trace-fast-image x)
                                                       (rw.trace-fast-image y)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))






(defsection rw.fast-urewrite-if-generalcase-trace

  (definlined rw.fast-urewrite-if-generalcase-trace (x y z)
    (declare (xargs :guard (and (rw.ftracep x)
                                (rw.ftracep y)
                                (rw.ftracep z))))
    (rw.ftrace (logic.function 'if (list (rw.ftrace->rhs x)
                                         (rw.ftrace->rhs y)
                                         (rw.ftrace->rhs z)))
               (fast-merge (rw.ftrace->fgoals x)
                           (fast-merge (rw.ftrace->fgoals y)
                                       (rw.ftrace->fgoals z)))))

  (local (in-theory (e/d (rw.fast-urewrite-if-generalcase-trace)
                         ((:executable-counterpart ACL2::force)))))

  (defthm rw.fast-urewrite-if-generalcase-trace-under-iff
    (iff (rw.fast-urewrite-if-generalcase-trace x y z)
         t))

  (defthm forcing-rw.ftracep-of-rw.fast-urewrite-if-generalcase-trace
    (implies (force (and (rw.ftracep x)
                         (rw.ftracep y)
                         (rw.ftracep z)))
             (equal (rw.ftracep (rw.fast-urewrite-if-generalcase-trace x y z))
                    t)))

  (defthm rw.ftrace->rhs-of-rw.fast-urewrite-if-generalcase-trace
    (equal (rw.ftrace->rhs (rw.fast-urewrite-if-generalcase-trace x y z))
           (logic.function 'if (list (rw.ftrace->rhs x)
                                     (rw.ftrace->rhs y)
                                     (rw.ftrace->rhs z)))))

  (defthm rw.ftrace->fgoals-of-rw.fast-urewrite-if-generalcase-trace
    (equal (rw.ftrace->fgoals (rw.fast-urewrite-if-generalcase-trace x y z))
           (fast-merge (rw.ftrace->fgoals x)
                       (fast-merge (rw.ftrace->fgoals y)
                                   (rw.ftrace->fgoals z)))))

  (defthm rw.trace-fast-image-of-rw.urewrite-if-generalcase-trace
    (equal (rw.trace-fast-image (rw.urewrite-if-generalcase-trace x y z))
           (rw.fast-urewrite-if-generalcase-trace (rw.trace-fast-image x)
                                                  (rw.trace-fast-image y)
                                                  (rw.trace-fast-image z)))
    :hints(("Goal" :in-theory (enable rw.trace-fast-image)))))




(definlined rw.fast-try-urewrite-rule (term rule iffp control)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.rulep rule)
                              (booleanp iffp)
                              (rw.controlp control))))
  (and (not (rw.rule->hyps rule))
       (let ((equiv (rw.rule->equiv rule)))
         (or (equal equiv 'equal)
             (and (equal equiv 'iff) iffp)))
       (let ((match-result (logic.patmatch (rw.rule->lhs rule) term nil)))
         (and (not (equal 'fail match-result))
              (rw.rule-syntax-okp rule match-result control)
              (rw.ftrace (logic.substitute (rw.rule->rhs rule) match-result)
                         nil)))))

(defthm forcing-rw.ftracep-of-rw.fast-try-urewrite-rule
  (implies (force (and (logic.termp term)
                       (rw.rulep rule)))
           (equal (rw.ftracep (rw.fast-try-urewrite-rule term rule iffp control))
                  (if (rw.fast-try-urewrite-rule term rule iffp control)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-try-urewrite-rule))))

(defthm rw.ftrace->fgoals-of-rw.fast-try-urewrite-rule
  (equal (rw.ftrace->fgoals (rw.fast-try-urewrite-rule term rule iffp control))
         nil)
  :hints(("Goal" :in-theory (enable rw.fast-try-urewrite-rule))))

(defthm rw.trace-fast-image-of-rw.try-urewrite-rule
  (implies (rw.try-urewrite-rule hypbox term rule iffp control)
           (equal (rw.trace-fast-image (rw.try-urewrite-rule hypbox term rule iffp control))
                  (rw.fast-try-urewrite-rule term rule iffp control)))
  :hints(("Goal" :in-theory (enable rw.trace-fast-image
                                    rw.fast-try-urewrite-rule
                                    rw.try-urewrite-rule
                                    definition-of-rw.collect-forced-goals))))



(defund rw.fast-try-urewrite-rule-list (term rules iffp control)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.rule-listp rules)
                              (booleanp iffp)
                              (rw.controlp control))))
  (if (consp rules)
      (or (rw.fast-try-urewrite-rule term (car rules) iffp control)
          (rw.fast-try-urewrite-rule-list term (cdr rules) iffp control))
    nil))

(defthm forcing-rw.ftracep-of-rw.fast-try-urewrite-rule-list
  (implies (force (and (logic.termp term)
                       (rw.rule-listp rules)))
           (equal (rw.ftracep (rw.fast-try-urewrite-rule-list term rules iffp control))
                  (if (rw.fast-try-urewrite-rule-list term rules iffp control)
                      t
                    nil)))
  :hints(("Goal"
          :expand (rw.fast-try-urewrite-rule-list term rules iffp control)
          :induct (cdr-induction rules))))

(defthm rw.ftrace->fgoals-of-rw.fast-try-urewrite-rule-list
  (equal (rw.ftrace->fgoals (rw.fast-try-urewrite-rule-list term rule iffp control))
         nil)
  :hints(("Goal" :in-theory (enable rw.fast-try-urewrite-rule-list))))

(defthm rw.trace-fast-image-of-rw.try-urewrite-rule-list
  (implies (rw.try-urewrite-rule-list hypbox term rules iffp control)
           (equal (rw.trace-fast-image (rw.try-urewrite-rule-list hypbox term rules iffp control))
                  (rw.fast-try-urewrite-rule-list term rules iffp control)))
  :hints(("Goal"
          :in-theory (enable rw.fast-try-urewrite-rule-list
                             rw.try-urewrite-rule-list
                             rw.try-urewrite-rule
                             rw.fast-try-urewrite-rule
                             rw.trace-fast-image))))






(defund rw.fast-try-urewrite-rules (term type iffp control)
  (declare (xargs :guard (and (logic.termp term)
                              (or (equal type 'inside)
                                  (equal type 'outside))
                              (booleanp iffp)
                              (rw.controlp control))))
  (let* ((rulemap (rw.theory-lookup term (rw.control->theory control)))
         (rules (cdr (lookup type rulemap))))
    (rw.fast-try-urewrite-rule-list term rules iffp control)))

(defthm forcing-rw.ftracep-of-rw.fast-try-urewrite-rules
  (implies (force (and (logic.termp term)
                       (rw.controlp control)))
           (equal (rw.ftracep (rw.fast-try-urewrite-rules term type iffp control))
                  (if (rw.fast-try-urewrite-rules term type iffp control)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-try-urewrite-rules))))

(defthm rw.ftrace->fgoals-of-rw.fast-try-urewrite-rules
  (equal (rw.ftrace->fgoals (rw.fast-try-urewrite-rules term type iffp control))
         nil)
  :hints(("Goal" :in-theory (enable rw.fast-try-urewrite-rules))))

(defthm rw.trace-fast-image-of-rw.try-urewrite-rules
  (implies (force (rw.try-urewrite-rules hypbox term type iffp control))
           (equal (rw.trace-fast-image (rw.try-urewrite-rules hypbox term type iffp control))
                  (rw.fast-try-urewrite-rules term type iffp control)))
  :hints(("Goal" :in-theory (enable rw.try-urewrite-rules
                                    rw.fast-try-urewrite-rules))))





(defund rw.maybe-extend-fast-trace (original extension)
  (declare (xargs :guard (and (rw.ftracep original)
                              (or (not extension)
                                  (rw.ftracep extension)))))
  (if extension
      (rw.fast-transitivity-trace original extension)
    original))

(defthm rw.ftracep-of-rw.maybe-extend-fast-trace
  (implies (and (rw.ftracep original)
                (or (not extension)
                    (rw.ftracep extension)))
           (equal (rw.ftracep (rw.maybe-extend-fast-trace original extension))
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-extend-fast-trace))))

(defthm rw.trace-fast-image-of-rw.maybe-extend-trace
  (equal (rw.trace-fast-image (rw.maybe-extend-trace original extension))
         (rw.maybe-extend-fast-trace (rw.trace-fast-image original)
                                     (and extension
                                          (rw.trace-fast-image extension))))
  :hints(("Goal" :in-theory (enable rw.maybe-extend-fast-trace
                                    rw.maybe-extend-trace))))





(defconst *rw.fast-traces-sigma*
  ;; Substitutions used to switch from regular traces to fast traces.
  (list (cons '(rw.trace->rhs ?x)
              '(rw.ftrace->rhs ?x))
        (cons '(rw.fail-trace ?hypbox ?x ?iffp)
              '(rw.fast-fail-trace ?x))
        (cons '(rw.transitivity-trace ?x ?y)
              '(rw.fast-transitivity-trace ?x ?y))
        (cons '(rw.equiv-by-args-trace ?hypbox ?f ?iffp ?traces)
              '(rw.fast-equiv-by-args-trace ?f ?traces))
        (cons '(rw.lambda-equiv-by-args-trace ?hypbox ?formals ?body ?iffp ?traces)
              '(rw.fast-lambda-equiv-by-args-trace ?formals ?body ?traces))
        (cons '(rw.beta-reduction-trace ?hypbox ?x ?iffp)
              '(rw.fast-beta-reduction-trace ?x))
        (cons '(rw.try-ground-simplify ?hypbox ?x ?iffp ?control)
              '(rw.fast-try-ground-simplify ?x ?iffp ?control))
        (cons '(rw.if-specialcase-nil-trace ?x ?y ?b1)
              '(rw.fast-if-specialcase-nil-trace ?x ?y))
        (cons '(rw.if-specialcase-t-trace ?x ?y ?c1)
              '(rw.fast-if-specialcase-t-trace ?x ?y))
        (cons '(rw.not-trace ?x ?iffp)
              '(rw.fast-not-trace ?x))
        (cons '(rw.negative-if-trace ?x ?iffp ?hypbox)
              '(rw.fast-negative-if-trace ?x))
        (cons '(rw.crewrite-if-specialcase-same-trace ?x ?y ?z)
              '(rw.fast-crewrite-if-specialcase-same-trace ?x ?y ?z))
        (cons '(rw.crewrite-if-generalcase-trace ?x ?y ?z)
              '(rw.fast-crewrite-if-generalcase-trace ?x ?y ?z))
        (cons '(rw.assumptions-trace ?assms ?lhs ?iffp)
              '(rw.fast-assumptions-trace ?assms ?lhs ?iffp))
        (cons '(rw.crewrite-rule-trace ?hypbox ?lhs ?rule ?sigma ?iffp ?traces)
              '(rw.fast-crewrite-rule-trace ?rule ?sigma ?traces))
        (cons '(rw.force-trace ?hypbox ?lhs)
              '(rw.fast-force-trace ?hypbox ?lhs))
        (cons '(rw.weakening-trace ?hypbox ?trace)
              '(rw.fast-weakening-trace ?trace))
        (cons '(rw.urewrite-if-specialcase-same-trace ?x ?y ?a)
              '(rw.fast-urewrite-if-specialcase-same-trace ?x ?y))
        (cons '(rw.urewrite-if-generalcase-trace ?x ?y ?z)
              '(rw.fast-urewrite-if-generalcase-trace ?x ?y ?z))
        (cons '(rw.try-urewrite-rule ?hypbox ?term ?rule ?iffp ?control)
              '(rw.fast-try-urewrite-rule ?x ?rule ?iffp ?control))
        (cons '(rw.try-urewrite-rule-list ?hypbox ?x ?rules ?iffp ?control)
              '(rw.fast-try-urewrite-rule-list ?x ?rules ?iffp ?control))
        (cons '(rw.try-urewrite-rules ?hypbox ?term ?type ?iffp ?control)
              '(rw.fast-try-urewrite-rules ?term ?type ?iffp ?control))
        (cons '(rw.maybe-extend-trace ?original ?extension)
              '(rw.maybe-extend-fast-trace ?original ?extension))))



(defsection rw.trace-fast-image-equivalence-lemmas

  (defthmd equiv-lemma-rw.try-ground-simplify-under-iff
    (iff (rw.try-ground-simplify hypbox x iffp control)
         (rw.fast-try-ground-simplify x iffp control))
    :hints(("Goal" :in-theory (enable rw.try-ground-simplify
                                      rw.fast-try-ground-simplify))))

  (defthmd equiv-lemma-rw.trace->rhs-of-rw.try-ground-simplify
    (equal (rw.trace->rhs (rw.try-ground-simplify hypbox x iffp control))
           (rw.ftrace->rhs (rw.fast-try-ground-simplify x iffp control)))
    :hints(("Goal" :in-theory (enable rw.try-ground-simplify
                                      rw.fast-try-ground-simplify))))


  (defthmd equiv-lemma-rw.try-urewrite-rule-list-under-iff
    (iff (rw.try-urewrite-rule-list hypbox term rules iffp control)
         (rw.fast-try-urewrite-rule-list term rules iffp control))
    :hints(("Goal" :in-theory (enable rw.try-urewrite-rule-list
                                      rw.fast-try-urewrite-rule-list
                                      rw.try-urewrite-rule
                                      rw.fast-try-urewrite-rule))))

  (defthmd equiv-lemma-rw.try-urewrite-rules-under-iff
    (iff (rw.try-urewrite-rules hypbox term type iffp control)
         (rw.fast-try-urewrite-rules term type iffp control))
    :hints(("Goal" :in-theory (enable equiv-lemma-rw.try-urewrite-rule-list-under-iff
                                      rw.try-urewrite-rules
                                      rw.fast-try-urewrite-rules))))

  (defthmd equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
    (equal (rw.trace->rhs (rw.try-urewrite-rule-list hypbox term rules iffp control))
           (rw.ftrace->rhs (rw.fast-try-urewrite-rule-list term rules iffp control)))
    :hints(("Goal" :in-theory (enable rw.try-urewrite-rule-list
                                      rw.fast-try-urewrite-rule-list
                                      rw.try-urewrite-rule
                                      rw.fast-try-urewrite-rule))))

  (defthmd equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rules
    (equal (rw.trace->rhs (rw.try-urewrite-rules hypbox term type iffp control))
           (rw.ftrace->rhs (rw.fast-try-urewrite-rules term type iffp control)))
    :hints(("Goal" :in-theory (enable equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
                                      rw.try-urewrite-rules
                                      rw.fast-try-urewrite-rules))))



  (defthmd equiv-lemma-rw.trace->rhs-of-rw.not-trace
    (equal (rw.trace->rhs (rw.not-trace x iffp))
           (rw.ftrace->rhs (rw.fast-not-trace (rw.trace-fast-image x))))
    :hints(("Goal" :in-theory (enable rw.not-trace
                                      rw.fast-not-trace))))



  (defthmd equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace
    ;; Can we avoid this case split somehow?
    (equal (rw.ftrace->rhs (rw.maybe-extend-fast-trace x y))
           (if y
               (rw.ftrace->rhs y)
             (rw.ftrace->rhs x)))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace
                                      rw.maybe-extend-fast-trace))))

  (defthmd equiv-lemma-rw.trace->rhs-of-rw.maybe-extend-trace
    ;; Can we avoid this case split somehow?
    (equal (rw.trace->rhs (rw.maybe-extend-trace x y))
           (if y
               (rw.trace->rhs y)
             (rw.trace->rhs x)))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthmd equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace-of-rw.trace-fast-image
    (equal (rw.ftrace->rhs (rw.maybe-extend-fast-trace x (rw.trace-fast-image y)))
           (rw.trace->rhs y))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace
                                      rw.maybe-extend-fast-trace))))

  (deftheory rw.trace-fast-image-equivalence-lemmas
    '(equiv-lemma-rw.try-ground-simplify-under-iff
      equiv-lemma-rw.trace->rhs-of-rw.try-ground-simplify
      equiv-lemma-rw.try-urewrite-rule-list-under-iff
      equiv-lemma-rw.try-urewrite-rules-under-iff
      equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rule-list
      equiv-lemma-rw.trace->rhs-of-rw.try-urewrite-rules
      equiv-lemma-rw.trace->rhs-of-rw.not-trace
      equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace
      equiv-lemma-rw.trace->rhs-of-rw.maybe-extend-trace
      equiv-lemma-rw.ftrace->rhs-of-rw.maybe-extend-fast-trace-of-rw.trace-fast-image)))

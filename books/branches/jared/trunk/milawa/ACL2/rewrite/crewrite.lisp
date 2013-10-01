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
(include-book "traces/crewrite-builders")
(include-book "urewrite")
(include-book "ancestors")
(include-book "match-free")
(include-book "cachep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund four-nats-measure (a b c d)
  ;; We create the ordinal w^3(1+a) + w^2(1+b) + w*(1+c) + d.  When ord< is
  ;; applied to such ordinals, the lexiographic ordering of <a, b, c, d> is
  ;; induced.
  (declare (xargs :guard t))
  (cons (cons 3 (+ 1 (nfix a)))
        (cons (cons 2 (+ 1 (nfix b)))
              (cons (cons 1 (+ 1 (nfix c)))
                    (nfix d)))))

(defthm ordp-of-four-nats-measure
  (equal (ordp (four-nats-measure a b c d))
         t)
  :hints(("Goal" :in-theory (enable four-nats-measure ordp))))

(defthm ord<-of-four-nats-measure
  (equal (ord< (four-nats-measure a1 b1 c1 d1)
               (four-nats-measure a2 b2 c2 d2))
         (or (< a1 a2)
             (and (equal (nfix a1) (nfix a2))
                  (or (< b1 b2)
                      (and (equal (nfix b1) (nfix b2))
                           (or (< c1 c2)
                               (and (equal (nfix c1) (nfix c2))
                                    (< d1 d2))))))))
  :hints(("Goal" :in-theory (enable four-nats-measure ord<))))






(defsection rw.cresult

  (definlined rw.cresult (data cache alimitedp)
    (declare (xargs :guard t))
    (cons data (cons cache alimitedp)))

  (definlined rw.cresult->data (x)
    (declare (xargs :guard t))
    (car x))

  (definlined rw.cresult->cache (x)
    (declare (xargs :guard t))
    (car (cdr x)))

  (definlined rw.cresult->alimitedp (x)
    (declare (xargs :guard t))
    (cdr (cdr x)))

  (local (in-theory (enable rw.cresult
                            rw.cresult->data
                            rw.cresult->cache
                            rw.cresult->alimitedp)))

  (defthm rw.cresult-under-iff
          (iff (rw.cresult data cache alimitedp)
               t))

  (defthm rw.cresult->data-of-rw.cresult
          (equal (rw.cresult->data (rw.cresult data cache alimitedp))
                 data))

  (defthm rw.cresult->cache-of-rw.cresult
          (equal (rw.cresult->cache (rw.cresult data cache alimitedp))
                 cache))

  (defthm rw.cresult->alimitedp-of-rw.cresult
    (equal (rw.cresult->alimitedp (rw.cresult data cache alimitedp))
           alimitedp)))


(defsection rw.hypresult

  (definlined rw.hypresult (successp traces cache alimitedp)
    (declare (xargs :guard t))
    (cons (cons successp traces)
          (cons cache alimitedp)))

  (definlined rw.hypresult->successp (x)
    (declare (xargs :guard t))
    (car (car x)))

  (definlined rw.hypresult->traces (x)
    (declare (xargs :guard t))
    (cdr (car x)))

  (definlined rw.hypresult->cache (x)
    (declare (xargs :guard t))
    (car (cdr x)))

  (definlined rw.hypresult->alimitedp (x)
    (declare (xargs :guard t))
    (cdr (cdr x)))

  (local (in-theory (enable rw.hypresult
                            rw.hypresult->successp
                            rw.hypresult->traces
                            rw.hypresult->cache
                            rw.hypresult->alimitedp)))

  (defthm rw.hypresult-under-iff
    (iff (rw.hypresult successp traces cache alimitedp)
         t))

  (defthm rw.hypresult->successp-of-rw.hypresult
    (equal (rw.hypresult->successp (rw.hypresult successp traces cache alimitedp))
           successp))

  (defthm rw.hypresult->traces-of-rw.hypresult
    (equal (rw.hypresult->traces (rw.hypresult successp traces cache alimitedp))
           traces))

  (defthm rw.hypresult->cache-of-rw.hypresult
    (equal (rw.hypresult->cache (rw.hypresult successp traces cache alimitedp))
           cache))

  (defthm rw.hypresult->alimitedp-of-rw.hypresult
    (equal (rw.hypresult->alimitedp (rw.hypresult successp traces cache alimitedp))
           alimitedp)))





(defsection invoke-macros

  ;; Our Conditional Rewriter
  ;;
  ;; We introduce our rewriter as a clique of mutually recursive functions.  As
  ;; usual, we begin with a "flag" function encompassing the entire clique, then
  ;; introduce the individual functions as wrappers for this flag function.
  ;;
  ;; We have often wanted to expand our rewriter with new functionality, and
  ;; sometimes this has required changing its arguments.  For example, in order
  ;; to support ancestors checking and memoization for free-variable hyps, we
  ;; needed to add the anstack and memhyps arguments.  Because of the large
  ;; number of function calls and arguments, we've introduced the following
  ;; macros which allow us to more easily perform these updates.

  (defmacro rw.crewrite-core$ (term &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'term ,assms ,term nil nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-core ,assms ,term ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-core-list$ (term-list &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'list ,assms ,term-list nil nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-core-list ,assms ,term-list ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-try-rule$ (term rule &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'rule ,assms ,term ,rule nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-try-rule ,assms ,term ,rule ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-try-rules$ (term rules &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'rules ,assms ,term ,rules nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-try-rules ,assms ,term ,rules ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-try-match$ (term rule sigma &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'match ,assms ,term ,rule ,sigma ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-try-match ,assms ,term ,rule ,sigma ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-try-matches$ (term rule sigmas &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'matches ,assms ,term ,rule ,sigmas ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-try-matches ,assms ,term ,rule ,sigmas ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-relieve-hyp$ (hyp rule sigma &key flagp (assms 'assms) (cache 'cache) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'hyp ,assms ,hyp ,rule ,sigma ,cache t ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-relieve-hyp ,assms ,hyp ,rule ,sigma ,cache ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.crewrite-relieve-hyps$ (hyps rule sigma &key flagp (assms 'assms) (cache 'cache) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.flag-crewrite 'hyps ,assms ,hyps ,rule ,sigma ,cache t ,blimit ,rlimit ,anstack ,control)
      `(rw.crewrite-relieve-hyps ,assms ,hyps ,rule ,sigma ,cache ,blimit ,rlimit ,anstack ,control))))



;; We use ACL2::defun below so that the functions are not exported.

(ACL2::defun rw.rlimit-warn ()
  (declare (xargs :guard t))
  (ACL2::cw ";;; rw.rlimit-warn has not been redefined!!"))

(ACL2::defun rw.rlimit-exit (rlimit trace)
  (declare (xargs :guard t)
           (ignore rlimit trace))
  nil)



;; See also at the end of this file for alternate versions of the core, etc.
(defconst *rw.crewrite-core*
  ;; Rewrite a term; returns (list trace new-cache limitedp)
  '(cond ((logic.constantp x)
          ;; We don't consult/modify the cache since this is cheap.
          (let* ((hypbox    (rw.assms->hypbox assms))
                 (ret-trace (or (and iffp
                                     (rw.try-ground-simplify hypbox x iffp control))
                                (rw.fail-trace hypbox x iffp))))
            (rw.cresult ret-trace cache nil)))
         ((logic.variablep x)
          ;; We don't consult/modify the cache since this is cheap.
          (let* ((ret-trace (or (rw.assumptions-trace assms x iffp)
                                (rw.fail-trace (rw.assms->hypbox assms) x iffp))))
            (rw.cresult ret-trace cache nil)))
         ((and (logic.functionp x)
               (equal (logic.function-name x) 'if)
               (equal (len (logic.function-args x)) 3))
          ;; We don't cache "if" expressions, so there's no need to consult the cache
          (let* ((args         (logic.function-args x))
                 (arg1         (first args))
                 (arg2         (second args))
                 (arg3         (third args))
                 (arg1-rw      (rw.crewrite-core$ arg1 :iffp t))
                 (arg1-trace   (rw.cresult->data arg1-rw))
                 (arg1-cache   (rw.cresult->cache arg1-rw))
                 (arg1-limited (rw.cresult->alimitedp arg1-rw))
                 (arg1-prime   (rw.trace->rhs arg1-trace)))
            (if (logic.constantp arg1-prime)
                ;; Here we don't have to use a new cache, because we don't make a new assm
                ;; We say we are limited if arg2/3 is limited.
                (if (logic.unquote arg1-prime)
                    (let* ((arg2-rw      (rw.crewrite-core$ arg2 :cache arg1-cache))
                           (arg2-trace   (rw.cresult->data arg2-rw))
                           (arg2-cache   (rw.cresult->cache arg2-rw))
                           (arg2-limited (rw.cresult->alimitedp arg2-rw))
                           (ret-trace    (rw.if-specialcase-t-trace arg1-trace arg2-trace arg3)))
                      (rw.cresult ret-trace arg2-cache arg2-limited))
                  (let* ((arg3-rw      (rw.crewrite-core$ arg3 :cache arg1-cache))
                         (arg3-trace   (rw.cresult->data arg3-rw))
                         (arg3-cache   (rw.cresult->cache arg3-rw))
                         (arg3-limited (rw.cresult->alimitedp arg3-rw))
                         (ret-trace    (rw.if-specialcase-nil-trace arg1-trace arg3-trace arg2)))
                    (rw.cresult ret-trace arg3-cache arg3-limited)))
              ;; Here we have to start new caches because we make new assumptions.
              (let* ((arg2-rw      (rw.crewrite-core$ arg2 :cache (rw.empty-cache) :assms (rw.assume-left (logic.function 'not (list arg1-prime)) assms)))
                     (arg2-trace   (rw.cresult->data arg2-rw))
                     (arg2-limited (rw.cresult->alimitedp arg2-rw))
                     (arg3-rw      (rw.crewrite-core$ arg3 :cache (rw.empty-cache) :assms (rw.assume-left arg1-prime assms)))
                     (arg3-trace   (rw.cresult->data arg3-rw))
                     (arg3-limited (rw.cresult->alimitedp arg3-rw)))
                (ACL2::prog2$
                 ;; free the temp caches we made for the arg rewrites
                 (ACL2::prog2$ (ACL2::flush-hons-get-hash-table-link (rw.cresult->cache arg2-rw))
                               (ACL2::flush-hons-get-hash-table-link (rw.cresult->cache arg3-rw)))
                 (if (equal (rw.trace->rhs arg2-trace) (rw.trace->rhs arg3-trace))
                     ;; Produced (if x y y); canonicalize to y
                     (let ((ret-trace (rw.crewrite-if-specialcase-same-trace arg1-trace arg2-trace arg3-trace)))
                       (rw.cresult ret-trace arg1-cache (and arg2-limited arg3-limited)))
                   (let* ((general-trace (rw.crewrite-if-generalcase-trace arg1-trace arg2-trace arg3-trace))
                          (gt-args       (logic.function-args (rw.trace->rhs general-trace))))
                     (if (and (equal (second gt-args) ''nil)
                              (equal (third gt-args) ''t))
                         ;; Produced (if x nil t); canonicalize to (not x)
                         (let* ((can-trace (rw.negative-if-trace (first gt-args) iffp (rw.assms->hypbox assms)))
                                (ret-trace (rw.transitivity-trace general-trace can-trace)))
                           (rw.cresult ret-trace arg1-cache arg1-limited))
                       ;; Produced (if x' y' z')
                       (rw.cresult general-trace arg1-cache (or arg1-limited arg2-limited arg3-limited))))))))))
         ((and (logic.functionp x)
               (equal (logic.function-name x) 'not)
               (equal (len (logic.function-args x)) 1))
          ;; We don't cache "not" expressions, so there's no need to consult the cache
          (let* ((args          (logic.function-args x))
                 (arg1          (first args))
                 (arg1-rw       (rw.crewrite-core$ arg1 :iffp t))
                 (arg1-trace    (rw.cresult->data arg1-rw))
                 (arg1-cache    (rw.cresult->cache arg1-rw))
                 (arg1-limitedp (rw.cresult->alimitedp arg1-rw))
                 (main-trace    (rw.not-trace arg1-trace iffp))
                 ;; -- We don't try rules; you shouldn't target "not" with a rewrite rule
                 ;; -- We don't try evaluation; rw.not-trace already evaluates (not t) and (not nil)
                 (main-rhs      (rw.trace->rhs main-trace))
                 ;; I'm not sure if we should use assms here or not, but "why not?"
                 (assm-trace    (and (not (logic.constantp main-rhs))
                                     (rw.assumptions-trace assms main-rhs iffp)))
                 (ret-trace     (rw.maybe-extend-trace main-trace assm-trace))
                 (ret-limitedp  (if assm-trace
                                    (and arg1-limitedp (not (logic.constantp (rw.trace->rhs assm-trace))))
                                  arg1-limitedp)))
            (rw.cresult ret-trace arg1-cache ret-limitedp)))
         ((logic.functionp x)
          ;; Generic handling for other functions than "if".
          (let* ((name       (logic.function-name x))
                 (args       (logic.function-args x))
                 (hypbox     (rw.assms->hypbox assms))
                 ;; We immediately try evaluation.  Without this, "constant-gathering" rules that
                 ;; break normal forms can get into loops with outside-in rules.
                 (eval-trace (and (logic.constant-listp args)
                                  (rw.try-ground-simplify hypbox x iffp control))))
            (if eval-trace
                ;; The term was evaluated.  We know the result is a constant and is canonical under iffp.
                ;; No more work can be done, so just return it.
                (rw.cresult eval-trace cache nil)
              ;; Now we try to use outside-in rewrite rules.
              (let* ((theory       (rw.control->theory control))
                     (rulemap      (rw.theory-lookup x theory))
                     (out-rules    (cdr (lookup 'outside rulemap)))
                     (out-rw       (rw.crewrite-try-rules$ x out-rules))
                     (out-trace    (rw.cresult->data out-rw))
                     (out-cache    (rw.cresult->cache out-rw))
                     (out-limitedp (rw.cresult->alimitedp out-rw)))
                (if out-trace
                    ;; An outside-in rule worked.  We don't have any idea what the result looks like, so
                    ;; we recur if we're allowed to.
                    (if (zp rlimit)
                        (ACL2::prog2$ (rw.rlimit-warn)
                                      (rw.cresult out-trace out-cache out-limitedp))
                      (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs out-trace) :rlimit (- rlimit 1) :cache out-cache))
                             (next-trace    (rw.cresult->data next-rw))
                             (next-cache    (rw.cresult->cache next-rw))
                             (next-limitedp (rw.cresult->alimitedp next-rw))
                             (ret-trace     (rw.transitivity-trace out-trace next-trace)))
                        (rw.cresult ret-trace next-cache next-limitedp)))
                  ;; Otherwise, no outside-in rules applied.  Rewrite the arguments.
                  (let* ((args-rw       (rw.crewrite-core-list$ args :iffp nil))
                         (args-traces   (rw.cresult->data args-rw))
                         (args-cache    (rw.cresult->cache args-rw))
                         (args-limited  (rw.cresult->alimitedp args-rw))
                         (part1-trace   (rw.equiv-by-args-trace hypbox name iffp args-traces)) ;; (f args) == (f args')
                         (term-prime    (rw.trace->rhs part1-trace))
                         (args-prime    (logic.function-args term-prime))
                         (cache-trace   (rw.cache-lookup term-prime iffp args-cache)))
                    (if cache-trace
                        ;; (f args') is cached; we assume the result is fully rewritten
                        (let ((final-trace (rw.transitivity-trace part1-trace cache-trace)))
                          (rw.cresult final-trace args-cache nil))
                      (let ((eval-trace (and (logic.constant-listp args-prime)
                                             (rw.try-ground-simplify hypbox term-prime iffp control))))
                        (if eval-trace
                            ;; (f args') can be evaluated; we cache the result
                            (let ((final-trace (rw.transitivity-trace part1-trace eval-trace))
                                  (new-cache   (rw.cache-update term-prime eval-trace iffp args-cache)))
                              (rw.cresult final-trace new-cache nil))
                          ;; We still might be able to use rules or assms.
                          (let* ((in-rules       (cdr (lookup 'inside rulemap)))
                                 ;; The "part2 trace" is the rewrite from (f args') to the result
                                 ;; Initially it's just a failure trace.  We extend it with rules,
                                 ;; assumptions, and more rewriting if applicable.
                                 (part2-trace    (rw.fail-trace hypbox term-prime iffp))
                                 ;; Maybe we can use some rules to make more progress.
                                 (in-rw          (rw.crewrite-try-rules$ term-prime in-rules :cache args-cache))
                                 (in-trace       (rw.cresult->data in-rw))
                                 (in-cache       (rw.cresult->cache in-rw))
                                 (in-limitedp    (rw.cresult->alimitedp in-rw))
                                 (part2-trace    (rw.maybe-extend-trace part2-trace in-trace))
                                 ;; Maybe we can use an assumption to make more progress.
                                 (assm-trace     (rw.assumptions-trace assms (rw.trace->rhs part2-trace) iffp))
                                 (part2-trace    (rw.maybe-extend-trace part2-trace assm-trace))
                                 ;; Maybe we're allowed to take another pass?
                                 ;; BOZO -- reconsider how this decision is made.  We may be able to avoid loops in
                                 ;; some cases by checking for looping rules here somehow.
                                 (another-passp  (and (or in-trace assm-trace) (not (zp rlimit)))))
                            (if (not another-passp)
                                (let* ((final-trace (rw.transitivity-trace part1-trace part2-trace))
                                       (limitedp    (or args-limited in-limitedp))
                                       (new-cache   (rw.maybe-update-cache (not limitedp) term-prime part2-trace iffp in-cache)))
                                  (ACL2::prog2$
                                   (if (or in-trace assm-trace)
                                       ;; We call a separate function to print the rlimit warning.  This function
                                       ;; gets modified with "advise" when we want to debug loops.
                                       (rw.rlimit-warn)
                                     nil)
                                   (rw.cresult final-trace new-cache limitedp)))
                              (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs part2-trace) :rlimit (- rlimit 1) :cache in-cache))
                                     (next-trace    (rw.cresult->data next-rw))
                                     (next-cache    (rw.cresult->cache next-rw))
                                     (next-limitedp (rw.cresult->alimitedp next-rw))
                                     (part2-trace   (rw.transitivity-trace part2-trace next-trace))
                                     (final-trace   (rw.transitivity-trace part1-trace part2-trace))
                                     (new-cache     (ACL2::prog2$ (rw.rlimit-exit rlimit final-trace)
                                                                  ;; The result is limited only if the next-rw is limited
                                                                  (rw.maybe-update-cache (not next-limitedp) term-prime part2-trace iffp next-cache))))
                                (rw.cresult final-trace new-cache next-limitedp)))))))))))))
         ((logic.lambdap x)
          (let* ((formals       (logic.lambda-formals x))
                 (body          (logic.lambda-body x))
                 (actuals       (logic.lambda-actuals x))
                 (betamode      (rw.control->betamode control))
                 (args-rw       (rw.crewrite-core-list$ actuals :iffp nil))
                 (args-traces   (rw.cresult->data args-rw))
                 (args-cache    (rw.cresult->cache args-rw))
                 (args-limitedp (rw.cresult->alimitedp args-rw))
                 ;; We'll return the best "ret trace" we can come up with.
                 (hypbox        (rw.assms->hypbox assms))
                 (ret-trace1    (rw.lambda-equiv-by-args-trace hypbox formals body iffp args-traces))
                 (term-prime    (rw.trace->rhs ret-trace1))
                 (args-prime    (logic.lambda-actuals term-prime))
                 ;; First try evaluation if all the actuals are constants.
                 (eval-trace    (and (logic.constant-listp args-prime)
                                     (rw.try-ground-simplify hypbox term-prime iffp control))))
            (cond (eval-trace
                   ;; We evaluated the term successfully so it's a constant; nothing more to do.
                   (let ((final-trace (rw.transitivity-trace ret-trace1 eval-trace)))
                     (rw.cresult final-trace args-cache nil)))
                  ((not betamode)
                   ;; Failed to evaluate and beta-reduction is not allowed.  This typically means we are in a
                   ;; huge proof and don't want to spend the time to look at lambdas yet.  Don't try anything
                   ;; else, just return the lambda with its updated actuals.
                   (rw.cresult ret-trace1 args-cache args-limitedp))
                  (t
                   ;; Time to beta-reduce.
                   (let* ((beta-trace  (rw.beta-reduction-trace hypbox term-prime iffp))
                          (part1-trace (rw.transitivity-trace ret-trace1 beta-trace)))
                     ;; We try to recursively rewrite, if we haven't hit the rlimit.  This can be too expensive
                     ;; in some proofs, so betamode can be set to once to only beta reduction without recursive
                     ;; rewriting.
                     (if (or (zp rlimit)
                             (equal betamode 'once))
                         (rw.cresult part1-trace args-cache args-limitedp)
                       (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs beta-trace) :rlimit (- rlimit 1) :cache args-cache))
                              (next-trace    (rw.cresult->data next-rw))
                              (next-cache    (rw.cresult->cache next-rw))
                              (next-limitedp (rw.cresult->alimitedp next-rw))
                              (final-trace   (rw.transitivity-trace part1-trace next-trace)))
                         (rw.cresult final-trace next-cache next-limitedp))))))))
         (t nil)))

(defconst *rw.crewrite-list*
  ;; Rewrite a term list.  Return (list trace-list new-cache limitedp)
  '(if (consp x)
       (let* ((term1-rw       (rw.crewrite-core$ (car x)))
              (term1-trace    (rw.cresult->data term1-rw))
              (term1-cache    (rw.cresult->cache term1-rw))
              (term1-limited  (rw.cresult->alimitedp term1-rw))
              (others-rw      (rw.crewrite-core-list$ (cdr x) :cache term1-cache))
              (others-traces  (rw.cresult->data others-rw))
              (others-cache   (rw.cresult->cache others-rw))
              (others-limited (rw.cresult->alimitedp others-rw)))
         (rw.cresult (cons term1-trace others-traces)
                     others-cache
                     ;; A list of terms is limited when any of them is limited.
                     (or term1-limited others-limited)))
     (rw.cresult nil cache nil)))

(defconst *rw.crewrite-rule*
  ;; Try to use a rule.  Return (list trace/nil new-cache limitedp)
  '(let ((equiv (rw.rule->equiv rule[s])))
     (if (not (or (equal equiv 'equal)
                  (and (equal equiv 'iff) iffp)))
         (rw.cresult nil cache nil)
       (let ((match-result (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
         (if (equal 'fail match-result)
             (rw.cresult nil cache nil)
           (let ((sigmas (rw.create-sigmas-to-try rule[s] match-result
                                                  (rw.assms->trueterms assms))))
             ;; A rule is limited when its matches are limited.
             (rw.crewrite-try-matches$ x rule[s] sigmas)))))))

(defconst *rw.crewrite-rules*
  ;; Try to use a list of rules.  Return (list trace/nil new-cache limitedp)
  '(if (consp rule[s])
       (let* ((rule1-rw      (rw.crewrite-try-rule$ x (car rule[s])))
              (rule1-trace   (rw.cresult->data rule1-rw))
              (rule1-cache   (rw.cresult->cache rule1-rw))
              (rule1-limited (rw.cresult->alimitedp rule1-rw)))
         (if rule1-trace
             rule1-rw
           (let* ((others-rw      (rw.crewrite-try-rules$ x (cdr rule[s]) :cache rule1-cache))
                  (others-trace   (rw.cresult->data others-rw))
                  (others-cache   (rw.cresult->cache others-rw))
                  (others-limited (rw.cresult->alimitedp others-rw)))
             (if others-trace
                 others-rw
               ;; No rules worked.  The rules are limited if any of them is limited
               (rw.cresult nil others-cache (or rule1-limited others-limited))))))
     (rw.cresult nil cache nil)))

(defconst *rw.crewrite-match*
  ;; Try to use a rule and sigma.  Returns (list trace/nil new-cache limitedp)
  '(if (not (rw.rule-syntax-okp rule[s] sigma[s] control))
       (rw.cresult nil cache nil)
     (let* ((hyps          (rw.rule->hyps rule[s]))
            (hyps-rw       (rw.crewrite-relieve-hyps$ hyps rule[s] sigma[s]))
            (hyps-successp (rw.hypresult->successp hyps-rw))
            (hyps-traces   (rw.hypresult->traces hyps-rw))
            (hyps-cache    (rw.hypresult->cache hyps-rw))
            (hyps-limited  (rw.hypresult->alimitedp hyps-rw)))
       (if hyps-successp
           (let ((trace (rw.crewrite-rule-trace (rw.assms->hypbox assms) x rule[s] sigma[s] iffp hyps-traces)))
             (rw.cresult trace hyps-cache nil))
         (rw.cresult nil hyps-cache hyps-limited)))))

(defconst *rw.crewrite-matches*
  ;; Try to use a rule and sigma list.  Returns (list trace/nil new-cache limitedp)
  '(if (consp sigma[s])
       (let* ((match1-rw      (rw.crewrite-try-match$ x rule[s] (car sigma[s])))
              (match1-trace   (rw.cresult->data match1-rw))
              (match1-cache   (rw.cresult->cache match1-rw))
              (match1-limited (rw.cresult->alimitedp match1-rw)))
         (if match1-trace
             match1-rw
           (let* ((others-rw      (rw.crewrite-try-matches$ x rule[s] (cdr sigma[s]) :cache match1-cache))
                  (others-trace   (rw.cresult->data others-rw))
                  (others-cache   (rw.cresult->cache others-rw))
                  (others-limited (rw.cresult->alimitedp others-rw)))
             (if others-trace
                 others-rw
               ;; No matches worked.  The matches are limited if any of them is limited
               (rw.cresult nil others-cache (or match1-limited others-limited))))))
     (rw.cresult nil cache nil)))

(defconst *rw.crewrite-hyp*
  ;; Try to relieve a hyp.  Returns (list trace/nil new-cache limitedp)
  '(let ((goal   (logic.substitute (rw.hyp->term x) sigma[s]))
         (hypbox (rw.assms->hypbox assms)))
     (or
      ;; Perhaps the hyp is cached?
      (let ((cache-trace (rw.cache-lookup goal t cache)))
        (and cache-trace
             (let ((rhs (rw.trace->rhs cache-trace)))
               (cond ((equal rhs ''t)
                      (rw.cresult cache-trace cache nil))
                     ((equal rhs ''nil)
                      (let ((fmode (and (rw.control->forcingp control)
                                        (rw.hyp->fmode x))))
                        (cond ((not fmode)
                               (rw.cresult nil cache nil))
                              ((equal fmode 'weak)
                               (rw.cresult nil cache nil))
                              (t ;; The fmode is strong
                               (let* ((ret-trace (rw.force-trace hypbox goal))
                                      (new-cache (rw.cache-update goal ret-trace t cache)))
                                 (rw.cresult ret-trace new-cache nil))))))
                     (t
                      ;; The cache knows something about goal, but not whether it's true or false.
                      ;; Try to relieve it some other way.
                      nil)))))
      ;; Perhaps we can just evaluate the hyp?
      (let ((eval-trace (and (logic.groundp goal)
                             (rw.try-ground-simplify hypbox goal t control))))
        (and eval-trace
             (cond ((equal (rw.trace->rhs eval-trace) ''t)
                    (rw.cresult eval-trace cache nil))
                   (t
                    (let ((fmode (and (rw.control->forcingp control)
                                      (rw.hyp->fmode x))))
                      (cond ((not fmode)
                             (rw.cresult nil cache nil))
                            ((equal fmode 'weak)
                             (rw.cresult nil cache nil))
                            (t ;; The fmode is strong
                             (let* ((ret-trace (rw.force-trace hypbox goal))
                                    (new-cache (rw.cache-update goal ret-trace t cache)))
                               (rw.cresult ret-trace new-cache nil)))))))))
      ;; Perhaps we can use assms?
      (let ((assm-trace (rw.assumptions-trace assms goal t)))
        (and assm-trace
             (let ((rhs (rw.trace->rhs assm-trace)))
               (cond ((equal rhs ''t)
                      (rw.cresult assm-trace cache nil))
                     ((equal rhs ''nil)
                      (let ((fmode (and (rw.control->forcingp control)
                                        (rw.hyp->fmode x))))
                        (cond ((not fmode)
                               (rw.cresult nil cache nil))
                              ((equal fmode 'weak)
                               (rw.cresult nil cache nil))
                              (t ;; The fmode is strong
                               (let* ((ret-trace (rw.force-trace hypbox goal))
                                      (new-cache (rw.cache-update goal ret-trace t cache)))
                                 (rw.cresult ret-trace new-cache nil))))))
                     (t
                      ;; The assms know something about goal, but not whether it's true or false.
                      ;; Try to relieve it some other way.
                      nil)))))
      ;; Perhaps we can use backchaining to rewrite the hyp?
      (cond ((zp blimit)
             ;; Nope, the backchain limit has already been hit.  At one point, I tried calling
             ;; urewrite here as a last-ditch effort, but this *doubled* the time crewrite took
             ;; on some examples.  Now, my strategy is to give up right away unless it's forced,
             ;; in which case we'll try urewrite so that we force a prettier goal.
             (if (and (rw.hyp->fmode x)
                      (rw.control->forcingp control))
                 (let* ((urw-trace (rw.urewrite goal t control 100))
                        (new-goal  (rw.trace->rhs urw-trace)))
                   (cond ((equal new-goal ''t)
                          (rw.cresult (rw.weakening-trace hypbox urw-trace) cache nil))
                         ((equal new-goal ''nil)
                          (rw.cresult nil cache nil))
                         (t
                          (let* ((force-trace (rw.force-trace hypbox new-goal))
                                 (ret-trace   (rw.transitivity-trace (rw.weakening-trace hypbox urw-trace) force-trace))
                                 (new-cache   (rw.cache-update goal ret-trace t cache)))
                            (rw.cresult ret-trace new-cache nil)))))
               (rw.cresult nil cache nil)))


            ((rw.ancestors-check goal (list rule[s]) anstack)
             ;; We are allowed to backchain, but the new goal looks "worse" than something we were
             ;; trying to prove before.
             (if (and (rw.hyp->fmode x)
                      (rw.control->forcingp control))
                 (let* ((ret-trace (rw.force-trace hypbox goal))
                        (new-cache (rw.cache-update goal ret-trace t cache)))
                   (rw.cresult ret-trace new-cache nil))
               (rw.cresult nil cache t)))

            (t
             ;; Time to backchain.  If the hyp has a backchain limit and the cache is not yet
             ;; blocked, we block it until we are finished rewriting.
             (let* ((must-blockp  (and (rw.hyp->limitp x)
                                       (not (rw.cache->blockp cache))))
                    (new-anstack  (cons (rw.anframe goal (list rule[s])) anstack))
                    (new-blimit   (if (rw.hyp->limitp x)
                                      (min (rw.hyp->limit x) (- blimit 1))
                                    (- blimit 1)))
                    (new-cache    (if must-blockp ;; could use if alias to avoid split
                                      (rw.set-blockedp t cache)
                                    cache))
                    (goal-rw      (rw.crewrite-core$ goal
                                                     :iffp t
                                                     :blimit new-blimit
                                                     :anstack new-anstack
                                                     :cache new-cache))
                    (goal-trace   (rw.cresult->data goal-rw))
                    (goal-cache   (rw.cresult->cache goal-rw))
                    (goal-limited (rw.cresult->alimitedp goal-rw))
                    (final-rhs    (rw.trace->rhs goal-trace))
                    (ret-cache    (if must-blockp ;; could use if alias to avoid split
                                      (rw.set-blockedp nil goal-cache)
                                    goal-cache)))
               (cond ((equal final-rhs ''t)
                      (rw.cresult goal-trace ret-cache nil))
                     ((and (rw.hyp->fmode x)
                           (rw.control->forcingp control))
                      (let* ((ret-trace (rw.force-trace hypbox goal))
                             (new-cache (rw.cache-update goal ret-trace t goal-cache)))
                        (rw.cresult ret-trace new-cache nil)))
                     (t
                      (rw.cresult nil ret-cache goal-limited)))))))))

(defconst *rw.crewrite-hyps*
  ;; Try to relieve a list of hyps.  Returns (list successp trace-list new-cache limitedp).
  '(if (not (consp x))
       (rw.hypresult t nil cache nil)
     (let* ((hyp1-rw      (rw.crewrite-relieve-hyp$ (car x) rule[s] sigma[s]))
            (hyp1-trace   (rw.cresult->data hyp1-rw))
            (hyp1-cache   (rw.cresult->cache hyp1-rw))
            (hyp1-limited (rw.cresult->alimitedp hyp1-rw)))
       (if (not hyp1-trace)
           ;; We are being a little conservative here: if hyp1 is limited, it might still be
           ;; that some other hyp would have failed without being limited.  So, we might prevent
           ;; some caching, but this way we can stop early and don't have to look at the rest
           ;; of the hyps.
           (rw.hypresult nil nil hyp1-cache hyp1-limited)
         (let* ((others-rw       (rw.crewrite-relieve-hyps$ (cdr x) rule[s] sigma[s] :cache hyp1-cache))
                (others-successp (rw.hypresult->successp others-rw))
                (others-traces   (rw.hypresult->traces others-rw))
                (others-cache    (rw.hypresult->cache others-rw))
                (others-limited  (rw.hypresult->alimitedp others-rw)))
           (if others-successp
               ;; Can't be limited, because everything was successful
               (rw.hypresult t (cons hyp1-trace others-traces) others-cache nil)
             ;; Otherwise, we know hyp1 is not limited (it was successful), so we are limited
             ;; only if one of the others is limited.
             (rw.hypresult nil nil others-cache others-limited)))))))

(defconst *rw.crewrite-flag-sigma*
  ;; Substitutions used to generate the flag function's definition.
  (list (cons '(rw.crewrite-core$ ?x)
              '(rw.flag-crewrite 'term assms ?x nil nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp)
              '(rw.flag-crewrite 'term assms ?x nil nil cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :rlimit ?rlimit :cache ?cache)
              '(rw.flag-crewrite 'term assms ?x nil nil ?cache iffp blimit ?rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache)
              '(rw.flag-crewrite 'term assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache :assms ?assms)
              '(rw.flag-crewrite 'term ?assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp :blimit ?blimit :anstack ?anstack :cache ?cache)
              '(rw.flag-crewrite 'term assms ?x nil nil ?cache ?iffp ?blimit rlimit ?anstack control))
        (cons '(rw.crewrite-core-list$ ?x :iffp ?iffp)
              '(rw.flag-crewrite 'list assms ?x nil nil cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core-list$ ?x :cache ?cache)
              '(rw.flag-crewrite 'list assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rule$ ?x ?rules)
              '(rw.flag-crewrite 'rule assms ?x ?rules nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules)
              '(rw.flag-crewrite 'rules assms ?x ?rules nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules :cache ?cache)
              '(rw.flag-crewrite 'rules assms ?x ?rules nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-match$ ?x ?rules ?sigmas)
              '(rw.flag-crewrite 'match assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas)
              '(rw.flag-crewrite 'matches assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.flag-crewrite 'matches assms ?x ?rules ?sigmas ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyp$ ?x ?rules ?sigmas)
              '(rw.flag-crewrite 'hyp assms ?x ?rules ?sigmas cache t blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas)
              '(rw.flag-crewrite 'hyps assms ?x ?rules ?sigmas cache t blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.flag-crewrite 'hyps assms ?x ?rules ?sigmas ?cache t blimit rlimit anstack control))))

(defconst *rw.crewrite-noflag-sigma*
  ;; Substitutions used to generate the flagless :definition rules
  (list (cons '(rw.crewrite-core$ ?x)
              '(rw.crewrite-core assms ?x cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp)
              '(rw.crewrite-core assms ?x cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :rlimit ?rlimit :cache ?cache)
              '(rw.crewrite-core assms ?x ?cache iffp blimit ?rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache)
              '(rw.crewrite-core assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache :assms ?assms)
              '(rw.crewrite-core ?assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp :blimit ?blimit :anstack ?anstack :cache ?cache)
              '(rw.crewrite-core assms ?x ?cache ?iffp ?blimit rlimit ?anstack control))
        (cons '(rw.crewrite-core-list$ ?x :iffp ?iffp)
              '(rw.crewrite-core-list assms ?x cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core-list$ ?x :cache ?cache)
              '(rw.crewrite-core-list assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rule$ ?x ?rules)
              '(rw.crewrite-try-rule assms ?x ?rules cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules)
              '(rw.crewrite-try-rules assms ?x ?rules cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules :cache ?cache)
              '(rw.crewrite-try-rules assms ?x ?rules ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-match$ ?x ?rules ?sigmas)
              '(rw.crewrite-try-match assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas)
              '(rw.crewrite-try-matches assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.crewrite-try-matches assms ?x ?rules ?sigmas ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyp$ ?x ?rules ?sigmas)
              '(rw.crewrite-relieve-hyp assms ?x ?rules ?sigmas cache blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas)
              '(rw.crewrite-relieve-hyps assms ?x ?rules ?sigmas cache blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.crewrite-relieve-hyps assms ?x ?rules ?sigmas ?cache blimit rlimit anstack control))))


(ACL2::make-event
 `(defun rw.flag-crewrite (flag ;; which mode we are in (we're really 8 mutually recursive functions)
                            assms ;; the current assumptions
                            x ;; the term we are rewriting (or the hyp we are relieving)
                            rule[s] ;; the rule (or list of rules) we want to try
                            sigma[s] ;; the sigma (or sigma list) we want to try (once we've already chosen a rule)
                            cache ;; rewrite cache to avoid repeated relieve-hyps from match-free
                            iffp ;; t if we can use iff rules, nil if we can only use equal rules
                            blimit ;; limit on backchaining depth (how hard may we try to relieving hyps?)
                            rlimit ;; limit on successful rewrites (how many rules can we successively apply?)
                            anstack ;; the ancestors stack (used to control backchaining; see ancestors.lisp)
                            control ;; the rewriter control object (stores rules, definitions, etc.; see controlp.lisp)
                            )
    (declare (xargs :guard (and (rw.assmsp assms)
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control)
                                (cond ((equal flag 'term)
                                       (logic.termp x))
                                      ((equal flag 'list)
                                       (logic.term-listp x))
                                      ((equal flag 'match)
                                       (and (logic.termp x)
                                            (rw.rulep rule[s])
                                            (or (equal (rw.rule->equiv rule[s]) 'equal)
                                                (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                            (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                            (logic.sigmap sigma[s])
                                            (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                                      ((equal flag 'matches)
                                       (and (logic.termp x)
                                            (rw.rulep rule[s])
                                            (or (equal (rw.rule->equiv rule[s]) 'equal)
                                                (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                            (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                            (logic.sigma-listp sigma[s])
                                            (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                                      ((equal flag 'rule)
                                       (and (logic.termp x)
                                            (rw.rulep rule[s])))
                                      ((equal flag 'rules)
                                       (and (logic.termp x)
                                            (rw.rule-listp rule[s])))
                                      ((equal flag 'hyp)
                                       (and (rw.hypp x)
                                            (rw.rulep rule[s])
                                            (logic.sigmap sigma[s])))
                                      (t
                                       (and (equal flag 'hyps)
                                            (rw.hyp-listp x)
                                            (rw.rulep rule[s])
                                            (logic.sigmap sigma[s])))))
                    :verify-guards nil
                    :measure (cond ((or (equal flag 'term)
                                        (equal flag 'list))
                                    (four-nats-measure rlimit (nfix blimit) 4 (rank x)))
                                   ((or (equal flag 'rule)
                                        (equal flag 'rules))
                                    (four-nats-measure rlimit (nfix blimit) 3 (rank rule[s])))
                                   ((or (equal flag 'match)
                                        (equal flag 'matches))
                                    (four-nats-measure rlimit (nfix blimit) 2 (rank sigma[s])))
                                   (t
                                    (four-nats-measure rlimit (nfix blimit) 1 (rank x))))
                    :hints (("Goal" :in-theory (disable (:executable-counterpart ACL2::force))))))
    (cond ((equal flag 'term)
           ,(ACL2::jared-rewrite *rw.crewrite-core* *rw.crewrite-flag-sigma*))
          ((equal flag 'list)
           ,(ACL2::jared-rewrite *rw.crewrite-list* *rw.crewrite-flag-sigma*))
          ((equal flag 'rule)
           ,(ACL2::jared-rewrite *rw.crewrite-rule* *rw.crewrite-flag-sigma*))
          ((equal flag 'rules)
           ,(ACL2::jared-rewrite *rw.crewrite-rules* *rw.crewrite-flag-sigma*))
          ((equal flag 'match)
           ,(ACL2::jared-rewrite *rw.crewrite-match* *rw.crewrite-flag-sigma*))
          ((equal flag 'matches)
           ,(ACL2::jared-rewrite *rw.crewrite-matches* *rw.crewrite-flag-sigma*))
          ((equal flag 'hyp)
           ,(ACL2::jared-rewrite *rw.crewrite-hyp* *rw.crewrite-flag-sigma*))
          (t
           ,(ACL2::jared-rewrite *rw.crewrite-hyps* *rw.crewrite-flag-sigma*)))))




(defsection irrelevant-argument-reduction

  ;; Some of the functions do not use all the arguments here, so we provide
  ;; reduction theorems to show which arguments are irrelevant.

 (local (in-theory (disable (:executable-counterpart ACL2::force))))

 (defthmd rw.flag-crewrite-of-term-reduction
   (equal (rw.flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-core$ x :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-core$ x :flagp t)))))

 (defthmd rw.flag-crewrite-of-list-reduction
   (equal (rw.flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-core-list$ x :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-core-list$ x :flagp t)))))

 (defthmd rw.flag-crewrite-of-rule-reduction
   (equal (rw.flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-rule$ x rule[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-try-rule$ x rule[s] :flagp t)))))

 (defthmd rw.flag-crewrite-of-rules-reduction
   (equal (rw.flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-rules$ x rule[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-try-rules$ x rule[s] :flagp t)))))

 (defthmd rw.flag-crewrite-of-hyp-reduction
   (equal (rw.flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t)))))

 (defthmd rw.flag-crewrite-of-hyps-reduction
   (equal (rw.flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t))))))



(defsection flag-wrapper-functions

  ;; We now introduce wrappers for the various functions inside the nest.

  (definlined rw.crewrite-core (assms x cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.termp x)
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-core$ x :flagp t))

  (definlined rw.crewrite-core-list (assms x cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.term-listp x)
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-core-list$ x :flagp t))

  (definlined rw.crewrite-try-rule (assms x rule[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-try-rule$ x rule[s] :flagp t))

  (definlined rw.crewrite-try-rules (assms x rule[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.termp x)
                                (rw.rule-listp rule[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-try-rules$ x rule[s] :flagp t))

  (definlined rw.crewrite-try-match (assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (or (equal (rw.rule->equiv rule[s]) 'equal)
                                    (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                (logic.sigmap sigma[s])
                                (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-try-match$ x rule[s] sigma[s] :flagp t))

  (definlined rw.crewrite-try-matches (assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (or (equal (rw.rule->equiv rule[s]) 'equal)
                                    (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                (logic.sigma-listp sigma[s])
                                (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-try-matches$ x rule[s] sigma[s] :flagp t))

  (definlined rw.crewrite-relieve-hyp (assms x rule[s] sigma[s] cache blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (rw.hypp x)
                                (rw.rulep rule[s])
                                (logic.sigmap sigma[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t))

  (definlined rw.crewrite-relieve-hyps (assms x rule[s] sigma[s] cache blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.assmsp assms)
                                (rw.hyp-listp x)
                                (rw.rulep rule[s])
                                (logic.sigmap sigma[s])
                                (rw.cachep cache)
                                (rw.cache-assmsp cache assms)
                                (rw.cache-lhses-okp cache)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t)))




(defsection rw.flag-crewrite-removal

  ;; We now prove the elimination rules for flag-crewrite to transform it into
  ;; calls of these wrapper functions.

 (defthm rw.flag-crewrite-of-term
   (equal (rw.flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-core$ x))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-core)
           :use ((:instance rw.flag-crewrite-of-term-reduction)))))

 (defthm rw.flag-crewrite-of-list
   (equal (rw.flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-core-list$ x))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-core-list)
           :use ((:instance rw.flag-crewrite-of-list-reduction)))))

 (defthm rw.flag-crewrite-of-rule
   (equal (rw.flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-rule$ x rule[s]))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-try-rule)
           :use ((:instance rw.flag-crewrite-of-rule-reduction)))))

 (defthm rw.flag-crewrite-of-rules
   (equal (rw.flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-rules$ x rule[s]))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-try-rules)
           :use ((:instance rw.flag-crewrite-of-rules-reduction)))))

 (defthm rw.flag-crewrite-of-match
   (equal (rw.flag-crewrite 'match assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-match$ x rule[s] sigma[s]))
   :hints(("Goal" :in-theory (enable rw.crewrite-try-match))))

 (defthm rw.flag-crewrite-of-matches
   (equal (rw.flag-crewrite 'matches assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-try-matches$ x rule[s] sigma[s]))
   :hints(("Goal" :in-theory (enable rw.crewrite-try-matches))))

 (defthm rw.flag-crewrite-of-hyp
   (equal (rw.flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-relieve-hyp)
           :use ((:instance rw.flag-crewrite-of-hyp-reduction)))))

 (defthm rw.flag-crewrite-of-hyps
   (equal (rw.flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
   :hints(("Goal"
           :in-theory (enable rw.crewrite-relieve-hyps)
           :use ((:instance rw.flag-crewrite-of-hyps-reduction))))))




(defthm equal-with-quoted-list-of-nil
  (equal (equal x '(nil))
         (and (consp x)
              (equal (car x) nil)
              (equal (cdr x) nil))))

(ACL2::make-event
 `(encapsulate
   ()
   (defthmd definition-of-rw.crewrite-core
     (equal (rw.crewrite-core$ x)
            ,(ACL2::jared-rewrite *rw.crewrite-core* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal"
             :use ((:instance rw.flag-crewrite (flag 'term))))))

   (defthmd definition-of-rw.crewrite-core-list
     (equal (rw.crewrite-core-list$ x)
            ,(ACL2::jared-rewrite *rw.crewrite-list* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'list))))))

   (defthmd definition-of-rw.crewrite-try-rule
     (equal (rw.crewrite-try-rule$ x rule[s])
            ,(ACL2::jared-rewrite *rw.crewrite-rule* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'rule))))))

   (defthmd definition-of-rw.crewrite-try-rules
     (equal (rw.crewrite-try-rules$ x rule[s])
            ,(ACL2::jared-rewrite *rw.crewrite-rules* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'rules))))))

   (defthmd definition-of-rw.crewrite-try-match
     (equal (rw.crewrite-try-match$ x rule[s] sigma[s])
            ,(ACL2::jared-rewrite *rw.crewrite-match* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'match))))))

   (defthmd definition-of-rw.crewrite-try-matches
     (equal (rw.crewrite-try-matches$ x rule[s] sigma[s])
            ,(ACL2::jared-rewrite *rw.crewrite-matches* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'matches))))))

   (defthmd definition-of-rw.crewrite-relieve-hyp
     (equal (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])
            ,(ACL2::jared-rewrite *rw.crewrite-hyp* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'hyp))))))

   (defthmd definition-of-rw.crewrite-relieve-hyps
     (equal (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])
            ,(ACL2::jared-rewrite *rw.crewrite-hyps* *rw.crewrite-noflag-sigma*))
     :rule-classes :definition
     :hints(("Goal" :use ((:instance rw.flag-crewrite (flag 'hyps))))))))



(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-core))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-core-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-try-rule))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-try-rules))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-try-match))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-try-matches))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-relieve-hyp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.crewrite-relieve-hyps))))






(defthm rw.crewrite-core-list-when-not-consp
   (implies (not (consp x))
            (equal (rw.crewrite-core-list$ x)
                   (rw.cresult nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-core-list))))

(defthm rw.crewrite-core-list-of-cons
   (equal (rw.crewrite-core-list$ (cons a x))
          (let* ((term1-rw      (rw.crewrite-core$ a))
                 (term1-trace   (rw.cresult->data term1-rw))
                 (term1-cache   (rw.cresult->cache term1-rw))
                 (term1-limited (rw.cresult->alimitedp term1-rw))
                 (others-rw      (rw.crewrite-core-list$ x :cache term1-cache))
                 (others-traces  (rw.cresult->data others-rw))
                 (others-cache   (rw.cresult->cache others-rw))
                 (others-limited (rw.cresult->alimitedp others-rw)))
            (rw.cresult (cons term1-trace others-traces)
                        others-cache
                        (or term1-limited others-limited))))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-core-list))))

(defun rw.crewrite-list-induction (assms x cache iffp blimit rlimit anstack control)
   (declare (xargs :verify-guards nil))
   (if (consp x)
       (rw.crewrite-list-induction assms (cdr x)
                                   (rw.cresult->cache (rw.crewrite-core$ (car x)))
                                   iffp blimit rlimit anstack control)
     (list assms x cache iffp blimit rlimit anstack control)))

(defmacro rw.crewrite-list-induction$ (x &key (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
   `(rw.crewrite-list-induction ,assms ,x ,cache ,iffp ,blimit ,rlimit ,anstack ,control))

(defthm true-listp-of-rw.cresult->data-of-rw.crewrite-core-list
   (equal (true-listp (rw.cresult->data (rw.crewrite-core-list$ x)))
          t)
   :hints(("Goal" :induct (rw.crewrite-list-induction$ x))))

(defthm len-of-rw.cresult->data-of-rw.crewrite-core-list$
   (equal (len (rw.cresult->data (rw.crewrite-core-list$ x)))
          (len x))
   :hints(("Goal" :induct (rw.crewrite-list-induction$ x))))





(defthm rw.crewrite-try-rules-when-not-consp
   (implies (not (consp rule[s]))
            (equal (rw.crewrite-try-rules$ x rule[s])
                   (rw.cresult nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-try-rules))))

(defthm rw.crewrite-try-rules-of-cons
   (equal (rw.crewrite-try-rules$ x (cons rule rules))
          (let* ((rule1-rw      (rw.crewrite-try-rule$ x rule))
                 (rule1-trace   (rw.cresult->data rule1-rw))
                 (rule1-cache   (rw.cresult->cache rule1-rw))
                 (rule1-limited (rw.cresult->alimitedp rule1-rw)))
            (if rule1-trace
                rule1-rw
              (let* ((others-rw      (rw.crewrite-try-rules$ x rules :cache rule1-cache))
                     (others-trace   (rw.cresult->data others-rw))
                     (others-cache   (rw.cresult->cache others-rw))
                     (others-limited (rw.cresult->alimitedp others-rw)))
                (if others-trace
                    others-rw
                  (rw.cresult nil others-cache (or rule1-limited others-limited)))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-try-rules))))

(defun rw.crewrite-try-rules-induction (assms x rule[s] cache iffp blimit rlimit anstack control)
   (declare (xargs :verify-guards nil))
   (if (consp rule[s])
       (rw.crewrite-try-rules-induction assms x (cdr rule[s])
                                        (rw.cresult->cache (rw.crewrite-try-rule$ x (car rule[s])))
                                        iffp blimit rlimit anstack control)
     (list assms x rule[s] cache iffp blimit rlimit anstack control)))

(defmacro rw.crewrite-try-rules-induction$ (x &key (assms 'assms) (rule[s] 'rule[s]) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
   `(rw.crewrite-try-rules-induction ,assms ,x ,rule[s] ,cache ,iffp ,blimit ,rlimit ,anstack ,control))






(defthm rw.crewrite-try-matches-when-not-consp
   (implies (not (consp sigma[s]))
            (equal (rw.crewrite-try-matches$ x rule[s] sigma[s])
                   (rw.cresult nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-try-matches))))

(defthm rw.crewrite-try-matches-of-cons
   (equal (rw.crewrite-try-matches$ x rule[s] (cons sigma sigmas))
          (let* ((match1-rw      (rw.crewrite-try-match$ x rule[s] sigma))
                 (match1-trace   (rw.cresult->data match1-rw))
                 (match1-cache   (rw.cresult->cache match1-rw))
                 (match1-limited (rw.cresult->alimitedp match1-rw)))
            (if match1-trace
                match1-rw
              (let* ((others-rw      (rw.crewrite-try-matches$ x rule[s] sigmas :cache match1-cache))
                     (others-trace   (rw.cresult->data others-rw))
                     (others-cache   (rw.cresult->cache others-rw))
                     (others-limited (rw.cresult->alimitedp others-rw)))
                (if others-trace
                    others-rw
                  (rw.cresult nil others-cache (or match1-limited others-limited)))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-try-matches))))




(defthm rw.crewrite-relieve-hyps-when-not-consp
   (implies (not (consp x))
            (equal (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])
                   (rw.hypresult t nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-relieve-hyps))))

(defthm rw.crewrite-relieve-hyps-of-cons
   (equal (rw.crewrite-relieve-hyps$ (cons a x) rule[s] sigma[s])
          (let* ((hyp1-rw      (rw.crewrite-relieve-hyp$ a rule[s] sigma[s]))
                 (hyp1-trace   (rw.cresult->data hyp1-rw))
                 (hyp1-cache   (rw.cresult->cache hyp1-rw))
                 (hyp1-limited (rw.cresult->alimitedp hyp1-rw)))
            (if (not hyp1-trace)
                (rw.hypresult nil nil hyp1-cache hyp1-limited)
              (let* ((others-rw       (rw.crewrite-relieve-hyps$ x rule[s] sigma[s] :cache hyp1-cache))
                     (others-successp (rw.hypresult->successp others-rw))
                     (others-traces   (rw.hypresult->traces others-rw))
                     (others-cache    (rw.hypresult->cache others-rw))
                     (others-limited  (rw.hypresult->alimitedp others-rw)))
                (if others-successp
                    (rw.hypresult t (cons hyp1-trace others-traces) others-cache nil)
                  (rw.hypresult nil nil others-cache others-limited))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.crewrite-relieve-hyps))))

(defthm booleanp-of-rw.hypresult->successp-of-rw.crewrite-relieve-hyps
   (equal (booleanp (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
          t)
   :hints(("Goal" :use ((:instance definition-of-rw.crewrite-relieve-hyps)))))



 ;; BOZO.  We should remove this rule or disable it by default.  There's no
 ;; reason that we should care what rw.assumptions-trace produces as its rhs.
;; (local (in-theory (disable rw.trace->rhs-of-rw.assumptions-trace)))


 ;; Let's just let it go and see how long it takes
 ;; Then we can change the numbers are try to find a semi-optimal solution
 ;; We can also look at AP output
;(set-case-split-limitations '(500 100))  ;; 264.16 seconds, i think it's 400+ with nil limit
;(set-case-split-limitations '(1000 100)) ;; 269.78 seconds
;(set-case-split-limitations '(500 200))  ;; 284.32 seconds
;(set-case-split-limitations '(250 100))  ;; 268.45 seconds

(local (defthm rw.trace-list-rhses-when-not-consp-cheap
         (implies (not (consp x))
                  (equal (rw.trace-list-rhses x)
                         nil))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm rw.crewrite-core-list-when-not-consp-cheap
         (implies (not (consp x))
                  (equal (rw.crewrite-core-list$ x)
                         (rw.cresult nil cache nil)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (in-theory (disable rw.trace-list-rhses-when-not-consp)))
(local (in-theory (disable rw.crewrite-core-list-when-not-consp)))

(local (deftheory my-disables-for-extra-speed
          '(consp-when-memberp-of-logic.sigmap
            consp-when-memberp-of-logic.sigmap-alt
            consp-when-memberp-of-logic.sigma-atblp
            consp-when-memberp-of-logic.sigma-atblp-alt
            consp-when-memberp-of-logic.arity-tablep
            consp-when-memberp-of-logic.arity-tablep-alt
            consp-when-memberp-of-logic.callmapp
            consp-when-memberp-of-logic.callmapp-alt
            consp-when-memberp-of-logic.callmap-atblp
            consp-when-memberp-of-logic.callmap-atblp-alt
            consp-when-memberp-of-rw.cachemapp
            consp-when-memberp-of-rw.cachemapp-alt
            consp-when-memberp-of-none-consp
            consp-when-memberp-of-none-consp-alt
            consp-when-memberp-of-cons-listp
            consp-when-memberp-of-cons-listp-alt

            same-length-prefixes-equal-cheap

            car-when-not-consp
            cdr-when-not-consp
            consp-when-natp-cheap
            forcing-logic.groundp-of-logic.substitute
            consp-when-logic.lambdap-cheap
            consp-when-logic.functionp-cheap
            consp-when-nonempty-subset-cheap
            consp-when-memberp-cheap
            logic.substitute-when-malformed-cheap
            logic.constant-listp-when-not-consp
            subsetp-when-not-consp
            subsetp-when-not-consp-two
            cons-listp-when-not-consp
            none-consp-when-not-consp
            forcing-logic.substitute-of-empty-sigma
            not-equal-when-less
            trichotomy-of-<
            natp-of-len-free
            transitivity-of-<
            transitivity-of-<-three
            transitivity-of-<-two
            less-completion-left
            less-of-one-right)))

(local (in-theory (disable my-disables-for-extra-speed)))


(defthm zp-of-one-plus
  (equal (zp (+ 1 x))
         nil))

(local (in-theory (disable zp min)))

(DEFTHM RW.CREWRITE-TRY-RULES-WHEN-NOT-CONSP-CHEAP
  (IMPLIES (NOT (CONSP RULE[S]))
           (EQUAL (RW.CREWRITE-TRY-RULES$ X RULE[S])
                  (RW.CRESULT NIL CACHE NIL)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

;; new disables for MORE SPEED
(local (in-theory (disable RW.CREWRITE-TRY-RULES-WHEN-NOT-CONSP
                           FORCING-LOGIC.FUNCTION-OF-LOGIC.FUNCTION-NAME-AND-LOGIC.FUNCTION-ARGS-FREE
                           CONSP-WHEN-TRUE-LISTP-CHEAP
                           LOOKUP-WHEN-NOT-CONSP
                           MINUS-WHEN-NOT-LESS
                           LESS-OF-ONE-LEFT
                           NOT-EQUAL-WHEN-LESS-TWO)))

(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.controlp control)
                          (rw.cachep cache)))
  :thms ((term forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.tracep (rw.cresult->data (rw.crewrite-core$ x)))
                               t)))
         (term forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.cachep (rw.cresult->cache (rw.crewrite-core$ x)))
                               t)))

         (list forcing-rw.trace-listp-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-listp (rw.cresult->data (rw.crewrite-core-list$ x)))
                               t)))
         (list forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.cachep (rw.cresult->cache (rw.crewrite-core-list$ x)))
                               t)))

         (rule forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.tracep (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])))
                               t)))
         (rule forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.cachep (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])))
                               t)))

         (rules forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.tracep (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])))
                                t)))
         (rules forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.cachep (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])))
                                t)))

         (match forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.tracep (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                t)))
         (match forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.cachep (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                t)))

         (matches forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.tracep (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  t)))
         (matches forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.cachep (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  t)))

         (hyp forcing-rw.tracep-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.tracep (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              t)))
         (hyp forcing-rw.cachep-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.cachep (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              t)))

         (t forcing-rw.trace-listp-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.trace-listp (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            t)))
         (t forcing-rw.cachep-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.cachep (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            t))))
  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :in-theory (disable forcing-lookup-of-logic.function-name
                               forcing-lookup-of-logic.function-name-free)
           :do-not-induct t)))

(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.controlp control)
                          (rw.cachep cache)))
  :thms ((term forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-core$ x)))
                               iffp)))

         (list forcing-rw.trace-list-iffps-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-iffps (rw.cresult->data (rw.crewrite-core-list$ x)))
                               (repeat iffp (len x)))))

         (rule forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])))
                               iffp)))

         (rules forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])))
                                iffp)))

         (match forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                iffp)))

         (matches forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  iffp)))

         (hyp forcing-rw.trace->iffp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.trace->iffp (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              t)))

         (t forcing-rw.trace-list-iffps-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.trace-list-iffps (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            (repeat t (len x))))))
  :hints(("Goal"
          :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                   (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                   (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                   (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
          :in-theory (disable forcing-lookup-of-logic.function-name
                              forcing-lookup-of-logic.function-name-free)
          :do-not-induct t)))


(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.controlp control)
                          (rw.cachep cache)
                          (rw.cache-assmsp cache assms)))
  :thms ((term forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-core$ x)))
                               (rw.assms->hypbox assms))))
         (term forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-core$ x)) assms)
                               t)))

         (list forcing-rw.trace-list-hypboxes-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-hypboxes (rw.cresult->data (rw.crewrite-core-list$ x)))
                               (repeat (rw.assms->hypbox assms) (len x)))))
         (list forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-core-list$ x)) assms)
                               t)))

         (rule forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])))
                               (rw.assms->hypbox assms))))
         (rule forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])) assms)
                               t)))

         (rules forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])))
                                (rw.assms->hypbox assms))))
         (rules forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])) assms)
                                t)))

         (match forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                (rw.assms->hypbox assms))))
         (match forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])) assms)
                                t)))

         (matches forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  (rw.assms->hypbox assms))))
         (matches forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])) assms)
                                  t)))

         (hyp forcing-rw.trace->hypbox-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.trace->hypbox (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              (rw.assms->hypbox assms))))
         (hyp forcing-rw.cache-assmsp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.cache-assmsp (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])) assms)
                              t)))

         (t forcing-rw.trace-list-hypboxes-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.trace-list-hypboxes (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            (repeat (rw.assms->hypbox assms) (len x)))))
         (t forcing-rw.cache-assmsp-of-rw.hyprseult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.cache-assmsp (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])) assms)
                            t))))
  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :in-theory (disable forcing-lookup-of-logic.function-name
                               forcing-lookup-of-logic.function-name-free)
           :do-not-induct t)))



(encapsulate
 ()
 (local (in-theory (enable consp-when-true-listp-cheap
                           forcing-logic.function-of-logic.function-name-and-logic.function-args-free
                           )))

 (local (in-theory (disable equal-of-logic.function-rewrite)))

 (defthms-flag
   :shared-hyp (and (rw.assmsp assms)
                    (rw.controlp control)
                    (rw.cachep cache)
                    (rw.cache-lhses-okp cache))
   :thms ((term forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-core
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)))
                         (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-core$ x)))
                                x)))
          (term forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-core
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)))
                         (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-core$ x)))
                                t)))

          (list forcing-rw.trace-list-lhses-of-rw.cresult->data-of-rw.crewrite-core-list
                (implies (force (and (logic.term-listp x)
                                     (booleanp iffp)))
                         (equal (rw.trace-list-lhses (rw.cresult->data (rw.crewrite-core-list$ x)))
                                (list-fix x))))
          (list forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
                (implies (force (and (logic.term-listp x)
                                     (booleanp iffp)))
                         (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-core-list$ x)))
                                t)))

          (rule forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-rule
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])))
                         (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])))
                                x)))
          (rule forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])))
                         (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])))
                                t)))

          (rules forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-rules
                 (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                      (booleanp iffp)
                                      (logic.termp x)
                                      (rw.rule-listp rule[s])))
                          (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])))
                                 x)))
          (rules forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
                 (implies (force (and (booleanp iffp)
                                      (logic.termp x)
                                      (rw.rule-listp rule[s])))
                          (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])))
                                 t)))

          (match forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-match
                 (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                      (logic.termp x)
                                      (booleanp iffp)
                                      (rw.rulep rule[s])
                                      (logic.sigmap sigma[s])))
                          (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                 x)))
          (match forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
                 (implies (force (and (logic.termp x)
                                      (booleanp iffp)
                                      (rw.rulep rule[s])
                                      (logic.sigmap sigma[s])))
                          (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                 t)))

          (matches forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-try-matches
                   (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                        (logic.termp x)
                                        (booleanp iffp)
                                        (rw.rulep rule[s])
                                        (logic.sigma-listp sigma[s])))
                            (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                   x)))
          (matches forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
                   (implies (force (and (logic.termp x)
                                        (booleanp iffp)
                                        (rw.rulep rule[s])
                                        (logic.sigma-listp sigma[s])))
                            (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                   t)))

          (hyp forcing-rw.trace->lhs-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
               (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                    (rw.hypp x)
                                    (rw.rulep rule[s])
                                    (logic.sigmap sigma[s])))
                        (equal (rw.trace->lhs (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                               (logic.substitute (rw.hyp->term x) sigma[s]))))
          (hyp forcing-rw.cache-lhses-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
               (implies (force (and (rw.hypp x)
                                    (rw.rulep rule[s])
                                    (logic.sigmap sigma[s])))
                        (equal (rw.cache-lhses-okp (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                               t)))

          (t forcing-rw.trace-list-lhses-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
             (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                  (rw.hyp-listp x)
                                  (rw.rulep rule[s])
                                  (logic.sigmap sigma[s])))
                      (equal (rw.trace-list-lhses (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                             (logic.substitute-list (rw.hyp-list-terms x) sigma[s]))))
          (t forcing-rw.cache-lhses-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
             (implies (force (and (rw.hyp-listp x)
                                  (rw.rulep rule[s])
                                  (logic.sigmap sigma[s])))
                      (equal (rw.cache-lhses-okp (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                             t))))
   :hints (("Goal"
            :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
            :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                     (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                     (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                     (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
            :in-theory (disable forcing-lookup-of-logic.function-name
                                forcing-lookup-of-logic.function-name-free)
            :do-not-induct t))))



(defthm forcing-rw.trace->rhs-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
  (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                       (rw.hypp x)
                       (rw.rulep rule[s])
                       (logic.sigmap sigma[s])
                       (rw.cachep cache)
                       (rw.assmsp assms)
                       (rw.controlp control)))
           (equal (rw.trace->rhs (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                  ''t))
  :hints(("Goal" :expand (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))))

(encapsulate
 ()
 (local (defun rw.crewrite-relieve-hyps-induction (assms x rule[s] sigma[s] cache blimit rlimit anstack control)
          (declare (xargs :verify-guards nil))
          (if (consp x)
              (rw.crewrite-relieve-hyps-induction assms (cdr x) rule[s] sigma[s]
                                                  (rw.cresult->cache (rw.crewrite-relieve-hyp assms (car x) rule[s] sigma[s] cache
                                                                                              blimit rlimit anstack control))
                                                  blimit rlimit anstack control)
            (list assms x rule[s] sigma[s] cache blimit rlimit anstack control))))

 (defthm forcing-rw.trace-list-rhses-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
   (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                        (rw.hyp-listp x)
                        (rw.rulep rule[s])
                        (logic.sigmap sigma[s])
                        (rw.cachep cache)
                        (rw.assmsp assms)
                        (rw.controlp control)))
            (equal (rw.trace-list-rhses (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                   (repeat ''t (len x))))
   :hints(("Goal" :induct (rw.crewrite-relieve-hyps-induction assms x rule[s] sigma[s] cache blimit rlimit anstack control)))))


(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.controlp control)
                          (rw.cachep cache)
                          (rw.cache-traces-okp cache (rw.control->defs control))
                          (rw.cache-lhses-okp cache)
                          (rw.cache-assmsp cache assms)))
  :thms ((term forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-core$ x))
                                             (rw.control->defs control))
                               t)))
         (term forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-core$ x))
                                                    (rw.control->defs control))
                               t)))

         (list forcing-rw.trace-list-okp-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-okp (rw.cresult->data (rw.crewrite-core-list$ x))
                                                  (rw.control->defs control))
                               t)))
         (list forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-core-list$ x))
                                                    (rw.control->defs control))
                               t)))

         (rule forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                             (rw.control->defs control))
                               t)))
         (rule forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s]))
                                                    (rw.control->defs control))
                               t)))

         (rules forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                              (rw.control->defs control))
                                t)))
         (rules forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s]))
                                                     (rw.control->defs control))
                                t)))

         (match forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])
                                     (or (equal (rw.rule->equiv rule[s]) 'equal)
                                         (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                     (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                     (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                         (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                              (rw.control->defs control))
                                t)))
         (match forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])
                                     (or (equal (rw.rule->equiv rule[s]) 'equal)
                                         (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                     (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                     (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                         (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                                     (rw.control->defs control))
                                t)))

         (matches forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (or (equal (rw.rule->equiv rule[s]) 'equal)
                                           (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                       (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                       (logic.sigma-listp sigma[s])
                                       (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                           (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                                (rw.control->defs control))
                                  t)))
         (matches forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (or (equal (rw.rule->equiv rule[s]) 'equal)
                                           (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                       (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                       (logic.sigma-listp sigma[s])
                                       (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                           (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                                       (rw.control->defs control))
                                  t)))

         (hyp forcing-rw.trace-okp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.trace-okp (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                            (rw.control->defs control))
                              t)))
         (hyp forcing-rw.cache-traces-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.cache-traces-okp (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                                   (rw.control->defs control))
                              t)))

         (t forcing-rw.trace-list-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.trace-list-okp (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                               (rw.control->defs control))
                            t)))
         (t forcing-rw.cache-traces-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.cache-traces-okp (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                                 (rw.control->defs control))
                            t))))

  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :in-theory (disable forcing-lookup-of-logic.function-name
                               forcing-lookup-of-logic.function-name-free

                               )
           :restrict ((forcing-rw.trace->hypbox-of-rw.cache-lookup ((assms assms))))
           :do-not-induct t)))


(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.assms-atblp assms atbl)
                          (rw.controlp control)
                          (rw.control-atblp control atbl)
                          (rw.cachep cache)
                          (rw.cache-atblp cache atbl)
                          (equal (cdr (lookup 'not atbl)) 1)))
  :thms ((term forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-core$ x)) atbl)
                               t)))
         (term forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-core$ x)) atbl)
                               t)))

         (list forcing-rw.trace-list-atblp-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (logic.term-list-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-atblp (rw.cresult->data (rw.crewrite-core-list$ x)) atbl)
                               t)))
         (list forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (logic.term-list-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-core-list$ x)) atbl)
                               t)))

         (rule forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])
                                    (rw.rule-atblp rule[s] atbl)))
                        (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])) atbl)
                               t)))
         (rule forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])
                                    (rw.rule-atblp rule[s] atbl)))
                        (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])) atbl)
                               t)))

         (rules forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])
                                     (rw.rule-list-atblp rule[s] atbl)))
                         (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])) atbl)
                                t)))
         (rules forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])
                                     (rw.rule-list-atblp rule[s] atbl)))
                         (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])) atbl)
                                t)))

         (match forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (rw.rule-atblp rule[s] atbl)
                                     (logic.sigmap sigma[s])
                                     (logic.sigma-atblp sigma[s] atbl)))
                         (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])) atbl)
                                t)))
         (match forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (rw.rule-atblp rule[s] atbl)
                                     (logic.sigmap sigma[s])
                                     (logic.sigma-atblp sigma[s] atbl)))
                         (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])) atbl)
                                t)))

         (matches forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (logic.term-atblp x atbl)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (rw.rule-atblp rule[s] atbl)
                                       (logic.sigma-listp sigma[s])
                                       (logic.sigma-list-atblp sigma[s] atbl)))
                           (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])) atbl)
                                  t)))
         (matches forcing-rw.cache-atblp-of-rw.cresult->cache-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (logic.term-atblp x atbl)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (rw.rule-atblp rule[s] atbl)
                                       (logic.sigma-listp sigma[s])
                                       (logic.sigma-list-atblp sigma[s] atbl)))
                           (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])) atbl)
                                  t)))

         (hyp forcing-rw.trace-atblp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.hyp-atblp x atbl)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])
                                   (logic.sigma-atblp sigma[s] atbl)))
                       (equal (rw.trace-atblp (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])) atbl)
                              t)))
         (hyp forcing-rw.cache-atblp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.hyp-atblp x atbl)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])
                                   (logic.sigma-atblp sigma[s] atbl)))
                       (equal (rw.cache-atblp (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])) atbl)
                              t)))

         (t forcing-rw.trace-list-atblp-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.hyp-list-atblp x atbl)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])
                                 (logic.sigma-atblp sigma[s] atbl)))
                     (equal (rw.trace-list-atblp (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])) atbl)
                            t)))
         (t forcing-rw.cache-atblp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.hyp-list-atblp x atbl)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])
                                 (logic.sigma-atblp sigma[s] atbl)))
                     (equal (rw.cache-atblp (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])) atbl)
                            t))))
  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl)))
                      (forcing-lookup-of-logic.function-name-free ((atbl atbl))))
           :do-not-induct t)))


(defthms-flag
  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.assms-atblp assms atbl)
                          (rw.controlp control)
                          (rw.control-atblp control atbl)
                          (rw.control-env-okp control axioms thms)
                          (rw.cachep cache)
                          (rw.cache-atblp cache atbl)
                          (rw.cache-env-okp cache defs thms atbl)
                          (equal (cdr (lookup 'not atbl)) 1)))
  :thms ((term forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-core$ x)) defs thms atbl)
                               t)))
         (term forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-core$ x)) defs thms atbl)
                               t)))

         (list forcing-rw.trace-list-env-okp-of-rw.cresult->data-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (logic.term-list-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-env-okp (rw.cresult->data (rw.crewrite-core-list$ x)) defs thms atbl)
                               t)))
         (list forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (logic.term-list-atblp x atbl)
                                    (booleanp iffp)))
                        (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-core-list$ x)) defs thms atbl)
                               t)))

         (rule forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])
                                    (rw.rule-atblp rule[s] atbl)
                                    (rw.rule-env-okp rule[s] thms)))
                        (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])) defs thms atbl)
                               t)))
         (rule forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])
                                    (rw.rule-atblp rule[s] atbl)
                                    (rw.rule-env-okp rule[s] thms)))
                        (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])) defs thms atbl)
                               t)))

         (rules forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])
                                     (rw.rule-list-atblp rule[s] atbl)
                                     (rw.rule-list-env-okp rule[s] thms)))
                         (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])) defs thms atbl)
                                t)))
         (rules forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])
                                     (rw.rule-list-atblp rule[s] atbl)
                                     (rw.rule-list-env-okp rule[s] thms)))
                         (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])) defs thms atbl)
                                t)))

         (match forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (rw.rule-atblp rule[s] atbl)
                                     (rw.rule-env-okp rule[s] thms)
                                     (logic.sigmap sigma[s])
                                     (logic.sigma-atblp sigma[s] atbl)))
                         (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])) defs thms atbl)
                                t)))
         (match forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (logic.term-atblp x atbl)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (rw.rule-atblp rule[s] atbl)
                                     (rw.rule-env-okp rule[s] thms)
                                     (logic.sigmap sigma[s])
                                     (logic.sigma-atblp sigma[s] atbl)))
                         (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])) defs thms atbl)
                                t)))

         (matches forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (logic.term-atblp x atbl)
                                       (booleanp iffp)
                                       (logic.sigma-listp sigma[s])
                                       (logic.sigma-list-atblp sigma[s] atbl)
                                       (rw.rulep rule[s])
                                       (rw.rule-atblp rule[s] atbl)
                                       (rw.rule-env-okp rule[s] thms)))
                           (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])) defs thms atbl)
                                  t)))
         (matches forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (logic.term-atblp x atbl)
                                       (booleanp iffp)
                                       (logic.sigma-listp sigma[s])
                                       (logic.sigma-list-atblp sigma[s] atbl)
                                       (rw.rulep rule[s])
                                       (rw.rule-atblp rule[s] atbl)
                                       (rw.rule-env-okp rule[s] thms)))
                           (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])) defs thms atbl)
                                  t)))

         (hyp forcing-rw.trace-env-okp-of-rw.cresult->data-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.hyp-atblp x atbl)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])
                                   (logic.sigma-atblp sigma[s] atbl)))
                       (equal (rw.trace-env-okp (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])) defs thms atbl)
                              t)))
         (hyp forcing-rw.cache-env-okp-of-rw.cresult->cache-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.hyp-atblp x atbl)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])
                                   (logic.sigma-atblp sigma[s] atbl)))
                       (equal (rw.cache-env-okp (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])) defs thms atbl)
                              t)))

         (t forcing-rw.trace-list-env-okp-of-rw.hypresult->traces-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.hyp-list-atblp x atbl)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])
                                 (logic.sigma-atblp sigma[s] atbl)))
                     (equal (rw.trace-list-env-okp (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])) defs thms atbl)
                            t)))
         (t forcing-rw.cache-env-okp-of-rw.hypresult->cache-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.hyp-list-atblp x atbl)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])
                                 (logic.sigma-atblp sigma[s] atbl)))
                     (equal (rw.cache-env-okp (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])) defs thms atbl)
                            t))))
  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :restrict ((forcing-lookup-of-logic.function-name ((atbl atbl))))
           :do-not-induct t)))



(defthm map-listp-when-logic.sigma-listp
  (implies (logic.sigma-listp x)
           (map-listp x))
  :hints(("Goal" :induct (cdr-induction x))))



(local (in-theory (enable zp)))



(encapsulate
 ()
 (verify-guards rw.flag-crewrite
                :hints(("Goal"
                        :in-theory (disable subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
                        :use ((:instance subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
                                         (x (RW.RULE->LHS RULE[S]))
                                         (y x)
                                         (sigma nil)))
                        :restrict ((forcing-rw.trace->hypbox-of-rw.cache-lookup ((assms assms)))))))

 (verify-guards rw.crewrite-core)
 (verify-guards rw.crewrite-core-list)
 (verify-guards rw.crewrite-try-rule)
 (verify-guards rw.crewrite-try-rules)
 (verify-guards rw.crewrite-try-match)
 (verify-guards rw.crewrite-try-matches)
 (verify-guards rw.crewrite-relieve-hyp)
 (verify-guards rw.crewrite-relieve-hyps))




#||

;; For a long time, I thought it was necessary to perform multiple passes of
;; rewriting on each literal.  I no longer think this is the case, and just
;; wish to rewrite each literal once.



(defund rw.aux-crewrite (assms x cache iffp blimit rlimit control n)
  ;; We perform (up to) n+1 inside-out passes of conditional rewriting, and
  ;; produce a trace of our progress.
  (declare (xargs :guard (and (rw.assmsp assms)
                              (logic.termp x)
                              (rw.cachep cache)
                              (rw.cache-assmsp cache assms)
                              (rw.controlp control)
                              (rw.cache-traces-okp cache (rw.control->defs control))
                              (rw.cache-lhses-okp cache)
                              (booleanp iffp)
                              (natp blimit)
                              (natp rlimit)
                              (natp n))
                  :measure (nfix n)
                  :verify-guards nil))
  (let* ((pass1-rw    (rw.crewrite-core assms x cache iffp blimit rlimit nil control))
         (pass1-trace (rw.cresult->data pass1-rw))
         (pass1-cache (rw.cresult->cache pass1-rw)))
    (cond ((equal x (rw.trace->rhs pass1-trace))
           ;; Originally, we instead checked if the method was 'fail.  But when
           ;; we started to develop fast-crewrite, we adopted the above approach
           ;; instead.
           ;;
           ;; This gives us a wonderful property: our rewriter never looks at
           ;; the method of a trace.  Because of this, we can omit the method
           ;; from fast-traces.  (The method is still needed for regular traces
           ;; because of the trace compilers.)
           ;;
           ;; This also allows further optimization.  For instance, the method
           ;; of (rw.transitivity-trace x y) might be 'fail or 'transitivity,
           ;; but to compute this we must have the lhs of x to compare against
           ;; the lhs of y.  By obviating the method computation, we can (1)
           ;; omit lhses from fast-traces entirely, and (2) eliminate the
           ;; overhead of these equality checks.
           (ACL2::prog2$
            (ACL2::flush-hons-get-hash-table-link pass1-cache)
            (ACL2::prog2$
             (ACL2::cw ";;; rw.aux-crewrite reached fixed-point with n = ~x0.~%" n)
             pass1-trace)))

          ((zp n)
           ;; We cannot further simplify becuase we have run out of steps.
           (ACL2::prog2$ (ACL2::cw "[rw.crewrite] Warning: ran out of rewriting steps.~%")
                         (ACL2::prog2$
                          (ACL2::flush-hons-get-hash-table-link pass1-cache)
                          pass1-trace)))

          (t
           ;; Perhaps we can simplify it further?
           (rw.transitivity-trace pass1-trace
                                  (rw.aux-crewrite assms (rw.trace->rhs pass1-trace) pass1-cache iffp blimit rlimit control (- n 1)))))))

(encapsulate
 ()
 (local (in-theory (enable rw.aux-crewrite)))

 (defthm forcing-rw.tracep-of-rw.aux-crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.controlp control)))
            (equal (rw.tracep (rw.aux-crewrite assms x cache iffp blimit rlimit control n))
                   t)))

 (defthm forcing-rw.trace->hypbox-of-rw.aux-crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.cache-assmsp cache assms)
                        (rw.controlp control)))
            (equal (rw.trace->hypbox (rw.aux-crewrite assms x cache iffp blimit rlimit control n))
                   (rw.assms->hypbox assms))))

 (defthm forcing-rw.trace->lhs-of-rw.aux-crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.cache-lhses-okp cache)
                        (rw.controlp control)))
            (equal (rw.trace->lhs (rw.aux-crewrite assms x cache iffp blimit rlimit control n))
                   x)))

 (defthm forcing-rw.trace->iffp-of-rw.aux-crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.controlp control)))
            (equal (rw.trace->iffp (rw.aux-crewrite assms x cache iffp blimit rlimit control n))
                   iffp)))

 (defthm forcing-rw.trace-atblp-of-rw.aux-crewrite
   (implies (force (and (rw.assmsp assms)
                        (rw.assms-atblp assms atbl)
                        (logic.termp x)
                        (logic.term-atblp x atbl)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.cache-atblp cache atbl)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (rw.trace-atblp (rw.aux-crewrite assms x cache iffp blimit rlimit control n) atbl)
                   t)))

 (verify-guards rw.aux-crewrite)

 (defthm forcing-rw.trace-okp-of-rw.aux-crewrite
   (implies (force (and (logic.termp x)
                        (rw.assmsp assms)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.cache-lhses-okp cache)
                        (rw.cache-traces-okp cache (rw.control->defs control))
                        (rw.cache-assmsp cache assms)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.aux-crewrite assms x cache iffp blimit rlimit control n)
                                 (rw.control->defs control))
                   t)))

 (defthm forcing-rw.trace-env-okp-of-rw.aux-crewrite
   (implies (force (and (logic.termp x)
                        (logic.term-atblp x atbl)
                        (rw.assmsp assms)
                        (rw.assms-atblp assms atbl)
                        (booleanp iffp)
                        (rw.cachep cache)
                        (rw.cache-atblp cache atbl)
                        (rw.cache-env-okp cache (rw.control->defs control) thms atbl)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (rw.trace-env-okp (rw.aux-crewrite assms x cache iffp blimit rlimit control n)
                                     (rw.control->defs control)
                                     thms atbl)
                   t))))

||#

;; BOZO eventually we should remove n, since it isn't used.  For now I'm leaving it
;; so I can verify that this really is okay.

(defund rw.crewrite (assms x iffp blimit rlimit control n)
  (declare (xargs :guard (and (rw.assmsp assms)
                              (logic.termp x)
                              (booleanp iffp)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil)
           (ignore n))
  ;; Old definition:
  ;;  (rw.aux-crewrite assms x (rw.empty-cache) iffp blimit rlimit control n))
  ;; New definition:
  (let ((result (rw.crewrite-core assms x (rw.empty-cache) iffp blimit rlimit nil control)))
    (ACL2::prog2$
     (ACL2::flush-hons-get-hash-table-link (rw.cresult->cache result))
     (rw.cresult->data result))))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite)))

 (defthm forcing-rw.tracep-of-rw.crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.tracep (rw.crewrite assms x iffp blimit rlimit control n))
                   t)))

 (defthm forcing-rw.trace->hypbox-of-rw.crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace->hypbox (rw.crewrite assms x iffp blimit rlimit control n))
                   (rw.assms->hypbox assms))))

 (defthm forcing-rw.trace->lhs-of-rw.crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace->lhs (rw.crewrite assms x iffp blimit rlimit control n))
                   x)))

 (defthm forcing-rw.trace->iffp-of-rw.crewrite
   (implies (force (and (rw.assmsp assms)
                        (logic.termp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace->iffp (rw.crewrite assms x iffp blimit rlimit control n))
                   iffp)))

 (defthm forcing-rw.trace-atblp-of-rw.crewrite
   (implies (force (and (rw.assmsp assms)
                        (rw.assms-atblp assms atbl)
                        (logic.termp x)
                        (logic.term-atblp x atbl)
                        (booleanp iffp)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (rw.trace-atblp (rw.crewrite assms x iffp blimit rlimit control n) atbl)
                   t)))

 (verify-guards rw.crewrite)

 (defthm forcing-rw.trace-okp-of-rw.crewrite
   (implies (force (and (logic.termp x)
                        (rw.assmsp assms)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.crewrite assms x iffp blimit rlimit control n)
                                 (rw.control->defs control))
                   t)))

 (defthm forcing-rw.trace-env-okp-of-rw.crewrite
   (implies (force (and (logic.termp x)
                        (logic.term-atblp x atbl)
                        (rw.assmsp assms)
                        (rw.assms-atblp assms atbl)
                        (booleanp iffp)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (rw.trace-env-okp (rw.crewrite assms x iffp blimit rlimit control n)
                                     (rw.control->defs control)
                                     thms atbl)
                   t))))







#||

;; This was a new version of the core that I tried to use at one point.  It pretty much works, but
;; it fails to prove a lemma in functional-axiom.lisp and has some trouble later in level8.  I am
;; not very happy with the current handling of assumptions.  Oh well.

(defconst *rw.crewrite-core*
  ;; Rewrite a term; returns (list trace new-cache limitedp)
  '(cond ((logic.constantp x)
          ;; We don't consult/modify the cache since this is cheap.
          (let* ((hypbox    (rw.assms->hypbox assms))
                 (ret-trace (or (rw.try-ground-simplify hypbox x iffp control)
                                (rw.fail-trace hypbox x iffp))))
            (rw.cresult ret-trace cache nil)))
         ((logic.variablep x)
          ;; We don't consult/modify the cache since this is cheap.
          (let* ((ret-trace (or (rw.assumptions-trace assms x iffp)
                                (rw.fail-trace (rw.assms->hypbox assms) x iffp))))
            (rw.cresult ret-trace cache nil)))
         ((and (logic.functionp x)
               (equal (logic.function-name x) 'if)
               (equal (len (logic.function-args x)) 3))
          ;; We don't cache "if" expressions, so there's no need to consult the cache
          (let* ((args         (logic.function-args x))
                 (arg1         (first args))
                 (arg2         (second args))
                 (arg3         (third args))
                 (arg1-rw      (rw.crewrite-core$ arg1 :iffp t))
                 (arg1-trace   (rw.cresult->data arg1-rw))
                 (arg1-cache   (rw.cresult->cache arg1-rw))
                 (arg1-limited (rw.cresult->alimitedp arg1-rw))
                 (arg1-prime   (rw.trace->rhs arg1-trace)))
            (if (logic.constantp arg1-prime)
                ;; Here we don't have to use a new cache, because we don't make a new assm
                ;; We say we are limited if arg2/3 is limited.
                (if (logic.unquote arg1-prime)
                    (let* ((arg2-rw      (rw.crewrite-core$ arg2 :cache arg1-cache))
                           (arg2-trace   (rw.cresult->data arg2-rw))
                           (arg2-cache   (rw.cresult->cache arg2-rw))
                           (arg2-limited (rw.cresult->alimitedp arg2-rw))
                           (ret-trace    (rw.if-specialcase-t-trace arg1-trace arg2-trace arg3)))
                      (rw.cresult ret-trace arg2-cache arg2-limited))
                  (let* ((arg3-rw      (rw.crewrite-core$ arg3 :cache arg1-cache))
                         (arg3-trace   (rw.cresult->data arg3-rw))
                         (arg3-cache   (rw.cresult->cache arg3-rw))
                         (arg3-limited (rw.cresult->alimitedp arg3-rw))
                         (ret-trace    (rw.if-specialcase-nil-trace arg1-trace arg3-trace arg2)))
                    (rw.cresult ret-trace arg3-cache arg3-limited)))
              ;; Here we have to start new caches because we make new assumptions.
              (let* ((arg2-rw      (rw.crewrite-core$ arg2 :cache (rw.empty-cache) :assms (rw.assume-left (logic.function 'not (list arg1-prime)) assms)))
                     (arg2-trace   (rw.cresult->data arg2-rw))
                     (arg2-limited (rw.cresult->alimitedp arg2-rw))
                     (arg3-rw      (rw.crewrite-core$ arg3 :cache (rw.empty-cache) :assms (rw.assume-left arg1-prime assms)))
                     (arg3-trace   (rw.cresult->data arg3-rw))
                     (arg3-limited (rw.cresult->alimitedp arg3-rw)))
                (if (equal (rw.trace->rhs arg2-trace) (rw.trace->rhs arg3-trace))
                    ;; Produced (if x y y); canonicalize to y
                    (let ((ret-trace (rw.crewrite-if-specialcase-same-trace arg1-trace arg2-trace arg3-trace)))
                      (rw.cresult ret-trace arg1-cache (and arg2-limited arg3-limited)))
                  (let* ((general-trace (rw.crewrite-if-generalcase-trace arg1-trace arg2-trace arg3-trace))
                         (gt-args       (logic.function-args (rw.trace->rhs general-trace))))
                    (if (and (equal (second gt-args) ''nil)
                             (equal (third gt-args) ''t))
                        ;; Produced (if x nil t); canonicalize to (not x)
                        (let* ((can-trace (rw.negative-if-trace (first gt-args) iffp (rw.assms->hypbox assms)))
                               (ret-trace (rw.transitivity-trace general-trace can-trace)))
                          (rw.cresult ret-trace arg1-cache arg1-limited))
                      ;; Produced (if x' y' z')
                      (rw.cresult general-trace arg1-cache (or arg1-limited arg2-limited arg3-limited)))))))))
         ((and (logic.functionp x)
               (equal (logic.function-name x) 'not)
               (equal (len (logic.function-args x)) 1))
          ;; We don't cache "not" expressions, so there's no need to consult the cache
          (let* ((args          (logic.function-args x))
                 (arg1          (first args))
                 (arg1-rw       (rw.crewrite-core$ arg1 :iffp t))
                 (arg1-trace    (rw.cresult->data arg1-rw))
                 (arg1-cache    (rw.cresult->cache arg1-rw))
                 (arg1-limitedp (rw.cresult->alimitedp arg1-rw))
                 (main-trace    (rw.not-trace arg1-trace iffp))
                 ;; -- We don't try rules; you shouldn't target "not" with a rewrite rule
                 ;; -- We don't try evaluation; rw.not-trace already evaluates (not t) and (not nil)
                 (main-rhs      (rw.trace->rhs main-trace))
                 ;; I'm not sure if we should use assms here or not, but "why not?"
                 (assm-trace    (and (not (logic.constantp main-rhs))
                                     (rw.assumptions-trace assms main-rhs iffp)))
                 (ret-trace     (rw.maybe-extend-trace main-trace assm-trace))
                 (ret-limitedp  (if assm-trace
                                    (and arg1-limitedp (not (logic.constantp (rw.trace->rhs assm-trace))))
                                  arg1-limitedp)))
            (rw.cresult ret-trace arg1-cache ret-limitedp)))

         ((logic.functionp x)
          ;; Generic handling for other functions than "if".
          (let* ((name       (logic.function-name x))
                 (args       (logic.function-args x))
                 (hypbox     (rw.assms->hypbox assms))
                 ;; We immediately try evaluation.  Without this, "constant-gathering" rules that
                 ;; break normal forms can get into loops with outside-in rules.
                 (eval-trace (and (logic.constant-listp args)
                                  (rw.try-ground-simplify hypbox x iffp control))))
            (if eval-trace
                ;; The term was evaluated.  We know the result is a constant and is canonical under iffp.
                ;; No more work can be done, so just return it.
                (rw.cresult eval-trace cache nil)
              ;; Now we try to use outside-in rewrite rules.
              (let* ((theory       (rw.control->theory control))
                     (rulemap      (rw.theory-lookup x theory))
                     (out-rules    (cdr (lookup 'outside rulemap)))
                     (out-rw       (rw.crewrite-try-rules$ x out-rules))
                     (out-trace    (rw.cresult->data out-rw))
                     (out-cache    (rw.cresult->cache out-rw))
                     (out-limitedp (rw.cresult->alimitedp out-rw)))
                (if out-trace
                    ;; An outside-in rule worked.  We don't have any idea what the result looks like, so
                    ;; we recur if we're allowed to.
                    (if (zp rlimit)
                        (ACL2::prog2$ (rw.rlimit-warn)
                                      (rw.cresult out-trace out-cache out-limitedp))
                      (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs out-trace) :rlimit (- rlimit 1) :cache out-cache))
                             (next-trace    (rw.cresult->data next-rw))
                             (next-cache    (rw.cresult->cache next-rw))
                             (next-limitedp (rw.cresult->alimitedp next-rw))
                             (ret-trace     (rw.transitivity-trace out-trace next-trace)))
                        (rw.cresult ret-trace next-cache next-limitedp)))
                  ;; Otherwise, no outside-in rules applied.  Rewrite the arguments.
                  (let* ((args-rw        (rw.crewrite-core-list$ args :iffp nil))
                         (args-traces    (rw.cresult->data args-rw))
                         (args-cache     (rw.cresult->cache args-rw))
                         (args-limitedp  (rw.cresult->alimitedp args-rw))
                         (part1-trace    (rw.equiv-by-args-trace hypbox name iffp args-traces)) ;; (f args) == (f args')
                         (term-prime     (rw.trace->rhs part1-trace))
                         (args-prime     (logic.function-args term-prime))
                         (cache-trace    (rw.cache-lookup term-prime iffp args-cache)))
                    (if cache-trace
                        ;; (f args') is cached; we assume the result is fully rewritten
                        (let ((final-trace (rw.transitivity-trace part1-trace cache-trace)))
                          (rw.cresult final-trace args-cache nil))
                      (let ((eval-trace (and (logic.constant-listp args-prime)
                                             (rw.try-ground-simplify hypbox term-prime iffp control))))
                        (if eval-trace
                            ;; (f args') can be evaluated; we cache the result
                            (let ((final-trace (rw.transitivity-trace part1-trace eval-trace))
                                  (new-cache   (rw.cache-update term-prime eval-trace iffp args-cache)))
                              (rw.cresult final-trace new-cache nil))

                          ;; We still might be able to use rules or assms.
                          (let* ((in-rules       (cdr (lookup 'inside rulemap)))
                                 (in-rw          (rw.crewrite-try-rules$ term-prime in-rules :cache args-cache))
                                 (in-trace       (rw.cresult->data in-rw))
                                 (in-cache       (rw.cresult->cache in-rw))
                                 (in-limitedp    (rw.cresult->alimitedp in-rw)))

                            (if in-trace
                                ;; part1-trace: (f args) == (f args')
                                ;; in-trace:    (f args') == alpha
                                ;; we don't know anything about alpha, so recursively rewrite it, if allowed.
                                (if (zp rlimit)
                                    (let ((ret-trace (rw.transitivity-trace part1-trace in-trace)))
                                      (ACL2::prog2$
                                       ;; we call a rw.rlimit-warn to print the rlimit warning.  this function gets modified
                                       ;; via "advise" when we want to debug loops.
                                       (rw.rlimit-warn)
                                       (rw.cresult ret-trace in-cache (or args-limitedp in-limitedp))))
                                  ;; allowed to recur
                                  (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs in-trace) :rlimit (- rlimit 1) :cache in-cache))
                                         ;; next-trace: alpha == alpha'
                                         (next-trace    (rw.cresult->data next-rw))
                                         (next-cache    (rw.cresult->cache next-rw))
                                         (next-limitedp (rw.cresult->alimitedp next-rw))
                                         ;; part2-trace: (f args') == alpha'

                                         ;; HORRIBLE.  SUBTLE.  In the proof, to show that rw.maybe-update-cache makes
                                         ;; a legitimage cachep, we need to know that the trace we give it agrees with
                                         ;; the iffp we give it.  but we don't prove the property of iffp until after
                                         ;; we prove cachep.  Horrible.
                                         ;;
                                         ;; We can't just use (rw.trace->iffp part2-trace), because the fast rewriter's
                                         ;; traces have no such concept.
                                         ;;
                                         ;; So what we do is "seed" part2-trace by creating a failure trace to begin
                                         ;; with, and then maybe-extending it.  This gives us a trace which we know
                                         ;; agrees with iffp, whereas if we start with in-trace, we can't be sure
                                         ;; until we've done the whole analysis on the crewrite nest.

                                         (part2-trace   (rw.fail-trace hypbox term-prime iffp))         ;; (f args') == (f args')
                                         (part2-trace   (rw.transitivity-trace part2-trace in-trace))   ;; (f args') == alpha
                                         (part2-trace   (rw.transitivity-trace part2-trace next-trace)) ;; (f args') == alpha'

                                         ;; final-trace: (f args) == alpha'
                                         (final-trace   (rw.transitivity-trace part1-trace part2-trace)) ;; (f args) == alpha'

                                         ;; acl2 seems upset about this new cache.
                                         (new-cache     (ACL2::prog2$ (rw.rlimit-exit rlimit final-trace)
                                                                      ;; The result is limited only if the next-rw is limited
                                                                      ;; New cache adds (f args') == alpha'
                                                                      (rw.maybe-update-cache (not next-limitedp)
                                                                                             term-prime
                                                                                             part2-trace
                                                                                             iffp
                                                                                             next-cache))))

                                    (rw.cresult final-trace new-cache next-limitedp)))


                              ;; Otherwise, rules failed.  Try assumptions.
                             (let ((assm-trace (rw.assumptions-trace assms term-prime iffp)))
                                (if assm-trace
                                    ;; part1-trace: (f args) == (f args')
                                    ;; assm-trace: (f args') == alpha
                                    ;; Again we know nothing about alpha, so recursively rewrite it, if allowed.
                                    (if (zp rlimit)
                                        ;; Not allowed to recur.  As before.
                                        (let ((ret-trace (rw.transitivity-trace part1-trace assm-trace)))
                                          (ACL2::prog2$ (rw.rlimit-warn)
                                                        (rw.cresult ret-trace in-cache (or args-limitedp in-limitedp))))
                                      ;; Allowed to recur.
                                      (let* ((next-rw       (rw.crewrite-core$ (rw.trace->rhs assm-trace) :rlimit (- rlimit 1) :cache in-cache))
                                             ;; next-trace: alpha == alpha'
                                             (next-trace    (rw.cresult->data next-rw))
                                             (next-cache    (rw.cresult->cache next-rw))
                                             (next-limitedp (rw.cresult->alimitedp next-rw))
                                             ;; part2-trace: (f args') == alpha'
                                             (part2-trace   (rw.transitivity-trace assm-trace next-trace))
                                             ;; final-trace: (f args) == alpha'
                                             (final-trace   (rw.transitivity-trace part1-trace part2-trace))
                                             (new-cache     (ACL2::prog2$ (rw.rlimit-exit rlimit final-trace)
                                                                          ;; The result is limited only if the next-rw is limited
                                                                          ;; New cache adds (f args') == alpha'
                                                                          (rw.maybe-update-cache (not next-limitedp) term-prime part2-trace iffp next-cache))))
                                        (rw.cresult final-trace new-cache next-limitedp)))

                                  ;; Otherwise, assms and rules failed.
                                  ;; We'll just use the result of rewriting the args.
                                  (let* ((limitedp   (or args-limitedp in-limitedp))
                                         (fail-trace (rw.fail-trace hypbox term-prime iffp))
                                         (new-cache  (rw.maybe-update-cache (not limitedp) term-prime fail-trace iffp in-cache)))
                                    (ACL2::prog2$ (rw.rlimit-exit rlimit part1-trace)
                                                  (rw.cresult part1-trace new-cache limitedp))))))))))))))))

         ((logic.lambdap x)
          (let* ((formals       (logic.lambda-formals x))
                 (body          (logic.lambda-body x))
                 (actuals       (logic.lambda-actuals x))
                 (args-rw       (rw.crewrite-core-list$ actuals :iffp nil))
                 (args-traces   (rw.cresult->data args-rw))
                 (args-cache    (rw.cresult->cache args-rw))
                 (args-limitedp (rw.cresult->alimitedp args-rw))
                 ;; We'll return the best "ret trace" we can come up with.
                 (hypbox        (rw.assms->hypbox assms))
                 (ret-trace1    (rw.lambda-equiv-by-args-trace hypbox formals body iffp args-traces))
                 (term-prime    (rw.trace->rhs ret-trace1))
                 (args-prime    (logic.lambda-actuals term-prime))
                 ;; First try evaluation if all the actuals are constants.
                 (eval-trace    (and (logic.constant-listp args-prime)
                                     (rw.try-ground-simplify hypbox term-prime iffp control))))
            (if eval-trace
                ;; We evaluated the term successfully so it's a constant; nothing more to do.
                (let ((final-trace (rw.transitivity-trace ret-trace1 eval-trace)))
                  (rw.cresult final-trace args-cache nil))
              ;; Else we might be allowed to beta reduce it. We've decided not to do anything else here.
              ;; BOZO this seems weird; don't we want to recursively rewrite?  I guess we'll get it on the next pass?
              (if (rw.control->betap control)
                  (let ((final-trace (rw.transitivity-trace ret-trace1 (rw.beta-reduction-trace hypbox term-prime iffp))))
                    (rw.cresult final-trace args-cache args-limitedp))
                (rw.cresult ret-trace1 args-cache args-limitedp)))))
         (t nil)))

||#
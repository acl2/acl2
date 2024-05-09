; Copyright (C) 2023, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

; Seven Proofs that PPR1 returns a PPR-TUPLE-P
; J Moore
; October, 2023

; This book illustrates the ideas discussed in
; :DOC induction-coarse-v-fine-grained
; -----------------------------------------------------------------
; 0 Setup

; We inherit lemmas from fmt-support and disable the lemma we'll repeatedly
; prove.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "system/fmt-support" :dir :system)

; Matt K. mod, 2/2/2024 to avoid failure apparently due to ACL2(p) parallelism
; issues:
(set-waterfall-parallelism nil)

(in-theory (disable fix ppr-tuple-p-ppr1 ppr-tuple-lst-p-ppr1-lst))

; We will create two induction schemes, a ``coarse'' one and a ``fine'' one.
; We'll repeatedly prove the ppr-tuple-p-ppr1 theorem (and its counterpart
; about ppr1-lst) using both schemes and various hints.

(make-flag coarse-induction-scheme ppr1
           :ruler-extenders :basic)

(make-flag fine-induction-scheme ppr1
           :ruler-extenders :lambdas)

; This function sketches an induction scheme.  We illustrate below.
(defun about-imach (fn wrld)
  (cons (len (getpropc fn 'induction-machine nil wrld))
        (merge-sort-lexorder
         (loop$ with imach = (getpropc fn 'induction-machine nil wrld)
                with alist = nil
                do
                (cond
                 ((consp imach)
                  (progn
                    (setq alist
                          (let ((n (len (access tests-and-calls (car imach) :calls))))
                            (put-assoc-equal n
                                             (+ 1
                                                (or (cdr (assoc-equal n alist)) 0))
                                             alist)))
                    (setq imach (cdr imach))))
                 (t (return alist)))))))

(assert-event
 (equal (about-imach 'coarse-induction-scheme (w state))
        '(76       ;; 76 cases in the induction scheme
          (0 . 6)  ;; no induction hyps in 6 cases, i.e., Base Cases
          (1 . 8)  ;; 1 induction hyp in 8 cases
          (2 . 2)  ;; 2 induction hyps in 2 cases
          (3 . 16) ;; ...
          (4 . 32)
          (8 . 4)
          (9 . 8)  ;; 9 induction hyps in 8 cases
          )))

(assert-event
 (equal (about-imach 'fine-induction-scheme (w state))
        '(256      ;; 256 cases in the induction scheme
          (0 . 6)  ;; no induction hyps in 6 cases, i.e., Base Cases
          (1 . 8)  ;; 1 induction hyp in 8 cases
          (2 . 82) ;; 2 induction hyps in 82 cases
          (3 . 80) ;; 3 induction hyps in 80 cases
          (4 . 80) ;; 4 induction hyps in 80 cases
          )))

; The following are used in our computed hint.

(defun find-all-calls-of-any (fns term ans)
  (cond
   ((endp fns) ans)
   (t (find-all-calls-of-any (cdr fns)
                             term
                             (find-all-calls (car fns) term ans)))))

(defun all-fnnames-intersect-fns (fns clause)

; We wish to compute the intersection of all the fnnames used in clause with
; the set of names listed in fns.  But rather than collect all the fnnames in
; clause we just ask of each fn in fns whether it is used in clause.

  (cond ((endp fns) nil)
        ((ffnnamep-lst (car fns) clause)
         (cons (car fns)
               (all-fnnames-intersect-fns (cdr fns) clause)))
        (t (all-fnnames-intersect-fns (cdr fns) clause))))

(set-state-ok t)
(defun computed-hint
    (fns opened-conclp enabledp clause stable-under-simplificationp state)

; The idea here is that we'll start with ppr1/ppr1-lst disabled.  The flagged
; induction will produce a bunch of hideous induction steps which we'll simplify
; without expanding any ppr1/ppr1-lst terms.  When the subgoal becomes stable,
; we'll explicitly :expand only the ppr1/ppr1-lst in the concluding literal.
; If it becomes stable again and ppr1/ppr1-lst still occur in the subgoal,
; we'll enable them and let the prover just do its job.

; Fns is the list of functions whose opening we're interested in, opened-conclp
; is a flag that tells us that we've already :expanded the calls in the
; conclusion, and enabledp is a flag that tells us that we've enabled the fns
; in question.

  (cond
   (stable-under-simplificationp
    (cond
     ((not opened-conclp)
      (let ((calls-in-concl (find-all-calls-of-any fns (car (last clause)) nil)))
        (cond (calls-in-concl
               (value
                `(:computed-hint-replacement
                  ((computed-hint
                    ',fns
                    t ,enabledp clause stable-under-simplificationp state))
                  :expand ,calls-in-concl)))
              ((not enabledp)
               (let ((fns-to-enable (all-fnnames-intersect-fns fns clause)))
                 (cond (fns-to-enable
                        (value `(:in-theory (enable ,fns-to-enable))))
                       (t (value nil)))))
              (t (value nil)))))
     ((not enabledp)
      (let ((fns-to-enable (all-fnnames-intersect-fns fns clause)))
        (cond (fns-to-enable
               (value `(:in-theory (enable ,fns-to-enable))))
              (t (value nil)))))
     (t (value nil))))
   (t (value nil))))

; Note that ppr1 and ppr1-lst will be globally disabled here, but the first two
; will eventually be enabled by the computed hint below, if an unproved subgoal
; involving ppr1 or ppr1-lst becomes stable after we've opened up ppr1 and/or
; ppr1-lst in the conclusion.

; Now we begin the tests.
; -----------------------------------------------------------------
; Scenario 1

(in-theory (enable ppr1 ppr1-lst))

; The following proof takes about 2200 seconds if allowed to proceed to
; completion.  But we don't want the ordinary user, who will probably do make
; regression at some point, to have to wait an extra 30 minutes to see that
; this proof takes a long time.  So in this version of the book, we just abort
; this proof attempt after 350,000 steps.  The successful proof takes on the
; order of 38 million steps.  To see the successful proof, certify
; ppr1-experiments-thm-1-ppr1.lisp.

; In September, 2023, it took 2165.19 seconds running the proto-Version 8.6 in
; CCL on a MacBook Pro.



(must-fail
(with-prover-step-limit 350000
(defthm-coarse-induction-scheme ; coarse, enabled, :expand
  (defthm thm-1-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-1-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints (("Goal"
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))))
))

; This proof times out after about 11 seconds.  The last few subgoals enumerated
; look like:

; Subgoal *1/63.9
; Subgoal *1/63.9'
; Subgoal *1/63.9.2
; Subgoal *1/63.9.1
; Subgoal *1/63.8
; Subgoal *1/63.8'
; Subgoal *1/63.8.4
; Subgoal *1/63.8.4.2
; Subgoal *1/63.8.4.2.3
; Subgoal *1/63.8.4.2.3.2
; Subgoal *1/63.8.4.2.3.1
; Subgoal *1/63.8.4.2.2
; Subgoal *1/63.8.4.2.2.3
; Subgoal *1/63.8.4.2.2.2

; -----------------------------------------------------------------
; Scenario 2

(in-theory (disable ppr1 ppr1-lst))

(defthm-coarse-induction-scheme ; coarse, disabled, computed
  (defthm thm-2-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-2-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints ((computed-hint '(ppr1 ppr1-lst) nil nil
                         clause stable-under-simplificationp state)))

; -----------------------------------------------------------------
; Scenario 3

(in-theory (enable ppr1 ppr1-lst))

(defthm-fine-induction-scheme ; fine, enabled, :expand
  (defthm thm-3-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-3-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints (("Goal"
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))))

; -----------------------------------------------------------------
; Scenario 4

(in-theory (disable ppr1 ppr1-lst))

(defthm-fine-induction-scheme ; fine, disabled, computed hint + :expand
  (defthm thm-4-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-4-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints ((computed-hint '(ppr1 ppr1-lst) nil nil
                         clause stable-under-simplificationp state)
          ("Goal"
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))
          ))

; -----------------------------------------------------------------
; Scenario 5

(in-theory (disable ppr1 ppr1-lst))

; Subgoal *1/255''' of the thm-5-ppr1-lst proof below fails because (PPR1-LST
; LST ...) in the conclusion becomes (PPR1-LST NIL ...), the :EXPAND hint
; doesn't catch that, and the TWEAK prevents the computed hint from detecting
; it.  But the following trivial lemma does the job.

(defthm ppr1-lst-nil
  (equal (PPR1-LST NIL PRINT-BASE PRINT-RADIX WIDTH
                   RPC PAIR-KEYWORDS-P STATE EVISCP)
         nil)
  :hints (("Goal"
           :expand (PPR1-LST NIL PRINT-BASE PRINT-RADIX WIDTH
                             RPC PAIR-KEYWORDS-P STATE EVISCP))))

(defthm-fine-induction-scheme ; fine, disabled, computed' + :expand + NIL lem
  (defthm thm-5-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-5-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints ((computed-hint '(ppr1 ppr1-lst) t nil ; <--- TWEAK!
                           clause stable-under-simplificationp state)
          ("Goal"
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))
          ))

(in-theory (disable ppr1-lst-nil))

; -----------------------------------------------------------------
; Scenario 6

(in-theory (disable ppr1 ppr1-lst))

(defthm-fine-induction-scheme ; fine, disabled, computed
  (defthm thm-6-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-6-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints ((computed-hint '(ppr1 ppr1-lst) nil nil
                         clause stable-under-simplificationp state)))

; -----------------------------------------------------------------
; Scenario 7

; Now we look at one other avenue: disabling MAX after proving a couple of
; useful lemmas about it.  We otherwise just use the fastest setup we've found
; above, namely a fine induction with the fns disabled and both the computed
; hint and the :expand hint.  Chances are that these MAX tweaks would help all
; the scenarios we've tried.

(defthm integerp-max
  (implies (and (integerp x)
                (integerp y))
           (integerp (max x y))))

(defthm nonneg-max
  (implies (and (<= 0 x)
                (<= 0 y))
           (<= 0 (max x y)))
  :rule-classes :linear)

(defthm max-upper-bound
  (and (<= x (max x y))
       (<= y (max x y)))
  :rule-classes :linear)

(in-theory (disable max))

(in-theory (disable ppr1 ppr1-lst))

(defthm-fine-induction-scheme ; fine, disabled, computed + :expand + MAX
  (defthm thm-7-ppr1
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-p (ppr1 x print-base print-radix width rpc state eviscp)))
    :flag ppr1
    :rule-classes nil)
  (defthm thm-7-ppr1-lst
    (implies (and
              (unsigned-byte-p #.*small-nat-bits* width)
              (unsigned-byte-p #.*small-nat-bits* rpc)
              (symbol-to-fixnat-alistp
               (table-alist 'ppr-special-syms (w state))))
             (ppr-tuple-lst-p (ppr1-lst lst print-base print-radix width rpc
                                        pair-keywords-p state eviscp)))
    :flag ppr1-lst
    :rule-classes nil)
  :hints ((computed-hint '(ppr1 ppr1-lst) nil nil
                         clause stable-under-simplificationp state)
          ("Goal"
           :expand ((:free (print-base print-radix width rpc state eviscp)
                           (ppr1 x print-base print-radix width rpc state eviscp))
                    (:free (print-base print-radix width rpc
                                       pair-keywords-p state eviscp)
                           (ppr1-lst lst print-base print-radix width rpc
                                     pair-keywords-p state eviscp))))))

; We now disable the lemmas we just proved about max and re-enable max to
; return the system to the state it was in before Scenario 7, in case we add
; more scenarios.

(in-theory (e/d (max)
                (integerp-max nonneg-max max-upper-bound)))

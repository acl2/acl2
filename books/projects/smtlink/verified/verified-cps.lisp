;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; ABSTRACTED VERIFIED CLAUSE PROCESSOR FOR SMTLINK
;;
;;   This verified clause processor decomposes the main goal
;;    into three subgoals. The clause processor is verified
;;    meaning it's proven that the three subgoals imply the
;;    original main clause. This is verified in theorem:
;;      "correctness-of-Smtlink-subgoals"
;;
;;   This higher order way of write proofs in ACL2 requires
;;     treating goals as program expressions (meaning they
;;     are quoted terms). Proving theorems on expressions
;;     instead of programs requires an evaluator that tells
;;     the theorem the ``meaning'' of the expressions.
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "misc/eval" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-please")
(include-book "hint-interface")
(include-book "goal-generator")

(defsection SMT-verified-clause-processors
  :parents (verified)
  :short "SMT verified clause processors"

  ;; -----------------------------------------------------------------
  ;;       Define evaluators

  (defevaluator ev-Smtlink-subgoals ev-lst-Smtlink-subgoals
    ((not x) (if x y z) (hint-please hint tag)))

  (def-join-thms ev-Smtlink-subgoals)


  ;; -----------------------------------------------------------------
  ;;       Define Smtlink subgoals.
  ;;

  ;;
  ;; Explanation for clause decomposition
  ;;
  ;; A -> G-prim
  ;; A \and G-prim -> G
  ;; A \or G
  ;;
  ;; A : The auxiliary hypothesis clauses
  ;; G-prim : The expanded original clause
  ;; G : The original clause

  (define preprocess-auxes ((hinted-As hint-pair-listp) (G pseudo-termp))
    :returns (mv (list-of-A-thm pseudo-term-list-listp)
                 (list-of-not-As pseudo-term-listp))
    :measure (len hinted-As)
    (b* ((hinted-As (hint-pair-list-fix hinted-As))
         (G (pseudo-term-fix G))
         ((unless (consp hinted-As)) (mv nil nil))
         ((cons first-hinted-A rest-hinted-As) hinted-As)
         (A (hint-pair->thm first-hinted-A))
         (A-hint (hint-pair->hints first-hinted-A))
         (first-A-thm `((hint-please ',A-hint 'A-hint) ,A ,G))
         (first-not-A-clause `(not ,A))
         ((mv rest-A-thms rest-not-A-clauses)
          (preprocess-auxes rest-hinted-As G)))
      (mv (cons first-A-thm rest-A-thms)
          (cons first-not-A-clause rest-not-A-clauses)))
    ///
    ;; For helping verify clause processor
    (defthm preprocess-auxes-corollary
      (implies (and (pseudo-term-listp cl)
                    (alistp b)
                    (hint-pair-listp hinted-As)
                    (ev-smtlink-subgoals
                     (disjoin (mv-nth 1 (preprocess-auxes hinted-As (disjoin cl)))) b)
                    (ev-smtlink-subgoals
                     (conjoin-clauses (mv-nth 0 (preprocess-auxes hinted-As (disjoin cl)))) b))
               (ev-smtlink-subgoals (disjoin cl) b))
      :hints (("Goal"
               :induct (preprocess-auxes hinted-As (disjoin cl)))))
    )

  (define generate-returns-auxes ((hinted-As-returns hint-pair-listp)
                                  (G pseudo-termp))
    :returns (list-of-A-thm pseudo-term-list-listp)
    :measure (len hinted-As-returns)
    (b* ((hinted-As-returns (hint-pair-list-fix hinted-As-returns))
         (G (pseudo-term-fix G))
         ((unless (consp hinted-As-returns)) nil)
         ((cons first-hinted-A rest-hinted-As) hinted-As-returns)
         (A (hint-pair->thm first-hinted-A))
         (A-hint (hint-pair->hints first-hinted-A))
         (first-A-thm `((hint-please ',A-hint 'A-hint) ,A ,G)))
      (cons first-A-thm (generate-returns-auxes rest-hinted-As G))))

  (define generate-types-auxes ((hinted-As-types decl-listp) (G pseudo-termp))
    :returns (list-of-A-thm pseudo-term-list-listp)
    :measure (len hinted-As-types)
    (b* ((hinted-As-types (decl-list-fix hinted-As-types))
         (G (pseudo-term-fix G))
         ((unless (consp hinted-As-types)) nil)
         ((cons first-hinted-A rest-hinted-As) hinted-As-types)
         (A-name (decl->name first-hinted-A))
         (A-hint-pair (decl->type first-hinted-A))
         (A-type (hint-pair->thm A-hint-pair))
         (A `(,A-type ,A-name))
         (A-hint (hint-pair->hints A-hint-pair))
         (first-A-thm `((hint-please ',A-hint 'A-hint) ,A ,G)))
      (cons first-A-thm (generate-types-auxes rest-hinted-As G))))

  (local
   (defthm pseudo-term-list-listp-of-append-2-pseudo-term-list-listp
     (implies (and (pseudo-term-list-listp x) (pseudo-term-list-listp y))
              (pseudo-term-list-listp (append x y)))))
  ;;
  ;; Constructing three type of clauses:
  ;;
  ;; 1. ((not A1) ... (not An) G-prim)
  ;; 2. ((not A1) ... (not An) (not G-prim) G)
  ;; 3. (A1 G)
  ;;    ...
  ;;    (An G)
  ;;
  ;; Adding hint-please:
  ;;
  ;; 1. ((hint-please smt-hint) (not A1) ... (not An) G-prim)
  ;; 2. ((hint-please main-hint) (not A1) ... (not An) (not G-prim) G)
  ;; 3. ((hint-please A1-hint) A1 G)
  ;;    ...
  ;;    ((hint-please An-hint) An G)
  ;;
  (local (in-theory (enable pseudo-term-list-listp pseudo-termp hint-pair-p
                            hint-pair-listp true-listp)))
  (define construct-smtlink-subgoals ((hinted-As hint-pair-listp)
                                      (hinted-As-returns hint-pair-listp)
                                      (hinted-As-types decl-listp)
                                      (hinted-G-prim hint-pair-p)
                                      (smt-hint true-listp)
                                      (G pseudo-termp))
    :returns (subgoals pseudo-term-list-listp)
    :guard-hints (("Goal" :in-theory (disable
                                      pseudo-term-list-listp-of-preprocess-auxes.list-of-a-thm)
                   :use ((:instance pseudo-term-list-listp-of-preprocess-auxes.list-of-a-thm))))
    (b* ((hinted-As (hint-pair-list-fix hinted-As))
         (hinted-As-returns (hint-pair-list-fix hinted-As-returns))
         (hinted-As-types (decl-list-fix hinted-As-types))
         (hinted-G-prim (hint-pair-fix hinted-G-prim))
         (smt-hint (true-list-fix smt-hint))
         (G (pseudo-term-fix G))
         ((mv aux-clauses list-of-not-As) (preprocess-auxes hinted-As G))
         (aux-clauses-returns (generate-returns-auxes hinted-As-returns G))
         (aux-clauses-types (generate-types-auxes hinted-As-types G))
         (G-prim (hint-pair->thm hinted-G-prim))
         (main-hint (hint-pair->hints hinted-G-prim))
         (cl0 `((hint-please ',smt-hint 'smt-hint) ,@list-of-not-As ,G-prim))
         (cl1 `((hint-please ',main-hint 'main-hint) ,@list-of-not-As (not ,G-prim) ,G))
         )
      `(,cl0 ,cl1 ,@aux-clauses ,@aux-clauses-types ,@aux-clauses-returns))
    ///
    (defthm construct-smtlink-subgoals-corollary
      (implies (and (pseudo-term-listp cl)
                    (alistp b)
                    (hint-pair-listp hinted-As)
                    (hint-pair-listp hinted-As-returns)
                    (decl-listp hinted-As-types)
                    (hint-pair-p hinted-G-prim)
                    (true-listp smt-hint)
                    (ev-smtlink-subgoals
                     (conjoin-clauses
                      (construct-smtlink-subgoals hinted-As
                                                  hinted-As-returns
                                                  hinted-As-types
                                                  hinted-G-prim
                                                  smt-hint
                                                  (disjoin cl)))
                     b))
               (ev-smtlink-subgoals (disjoin cl) b))
      :hints (("Goal"
               :in-theory (e/d (generate-returns-auxes
                                generate-types-auxes
                                preprocess-auxes)
                               ())
               ))))


  ;; If I give guard to smtlink-hint, then I get the error:

  ;; ACL2 Error in ( DEFTHM CORRECTNESS-OF-SMTLINK-SUBGOALS ...):  The clause-
  ;; processor of a :CLAUSE-PROCESSOR rule must have a guard that obviously
  ;; holds whenever its first argument is known to be a PSEUDO-TERM-LISTP
  ;; and any stobj arguments are assumed to satisfy their stobj predicates.
  ;; However, the guard for SMTLINK-SUBGOALS is
  ;; (AND (PSEUDO-TERM-LISTP CL) (SMTLINK-HINT-P SMTLINK-HINT)).  See :DOC
  ;; clause-processor.

  ;; (define Smtlink-subgoals ((cl pseudo-term-listp) (smtlink-hint smtlink-hint-p))
  ;;   :returns (subgoal-lst pseudo-term-list-listp)
  ;;   (b* ((cl (mbe :logic (pseudo-term-list-fix cl) :exec cl))
  ;;        (smtlink-hint (mbe :logic (smtlink-hint-fix smtlink-hint) :exec smtlink-hint))
  ;;        (hinted-As (smtlink-hint->aux-hint-list smtlink-hint))
  ;;        (hinted-G-prim (smtlink-hint->expanded-clause-w/-hint smtlink-hint))
  ;;        (smt-hint (smtlink-hint->smt-hint smtlink-hint)))
  ;;     (construct-smtlink-subgoals hinted-As hinted-G-prim smt-hint (disjoin cl))))

  (local (in-theory (enable smtlink-hint-p smtlink-hint->aux-hint-list
                            smtlink-hint->expanded-clause-w/-hint)))
  (define Smtlink-subgoals ((cl pseudo-term-listp) (smtlink-hint t))
    :returns (subgoal-lst
              pseudo-term-list-listp
              :hints (("Goal"
                       :in-theory (disable smtlink-hint-p))))
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint))
          (list (remove-hint-please cl)))
         ((smtlink-hint h) smtlink-hint)
         (cl (remove-hint-please cl))
         (hinted-As (smtlink-hint->aux-hint-list smtlink-hint))
         (hinted-As-returns (smtlink-hint->aux-thm-list smtlink-hint))
         (hinted-As-types (smtlink-hint->type-decl-list smtlink-hint))
         (hinted-G-prim (smtlink-hint->expanded-clause-w/-hint smtlink-hint))
         (smt-hint
          (if h.custom-p
              `(:clause-processor (SMT-trusted-cp-custom clause ',smtlink-hint state))
            `(:clause-processor (SMT-trusted-cp clause ',smtlink-hint state))))
         (full (construct-smtlink-subgoals hinted-As
                                           hinted-As-returns hinted-As-types
                                           hinted-G-prim smt-hint
                                           (disjoin cl)))
         )
      full))

  ;; ------------------------------------------------------------
  ;;         Prove correctness of clause processor
  ;;

  (local (in-theory (e/d () (smtlink-hint-p smtlink-hint->aux-hint-list
                                            smtlink-hint->expanded-clause-w/-hint))))
  (defthm correctness-of-Smtlink-subgoals-crock
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-Smtlink-subgoals
                   (conjoin-clauses (Smtlink-subgoals cl smtlink-hint))
                   b))
             (ev-Smtlink-subgoals (disjoin (remove-hint-please cl)) b))
    :hints (("Goal"
             :in-theory (e/d () (construct-smtlink-subgoals-corollary))
             :expand (Smtlink-subgoals cl smtlink-hint)
             :use ((:instance construct-smtlink-subgoals-corollary
                              (hinted-As (smtlink-hint->aux-hint-list
                                          smtlink-hint))
                              (hinted-As-returns
                               (smtlink-hint->aux-thm-list smtlink-hint))
                              (hinted-As-types
                               (smtlink-hint->type-decl-list smtlink-hint))
                              (hinted-G-prim
                               (smtlink-hint->expanded-clause-w/-hint
                                smtlink-hint))
                              (smt-hint
                               (if (smtlink-hint->custom-p smtlink-hint)
                                   `(:clause-processor (SMT-trusted-cp-custom
                                                        clause ',smtlink-hint
                                                        state))
                                 `(:clause-processor (SMT-trusted-cp
                                                      clause
                                                      ',smtlink-hint
                                                      state))))
                              (cl (remove-hint-please cl))))
             )))

  (defthm correctness-of-remove-hint-please-with-ev-Smtlink-subgoals
    (implies (and (pseudo-term-listp cl)
                  (alistp b))
             (iff (ev-Smtlink-subgoals (disjoin (remove-hint-please cl)) b)
                  (ev-Smtlink-subgoals (disjoin cl) b)))
    :hints (("Goal"
             :in-theory (enable hint-please remove-hint-please) )))

  (defthm correctness-of-Smtlink-subgoals
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-Smtlink-subgoals
                   (conjoin-clauses (Smtlink-subgoals cl smtlink-hint))
                   b))
             (ev-Smtlink-subgoals (disjoin cl) b))
    :rule-classes :clause-processor
    :hints (("Goal"
             :use ((:instance correctness-of-Smtlink-subgoals-crock)
                   (:instance correctness-of-remove-hint-please-with-ev-Smtlink-subgoals)))))

  ;; -------------------------------------------------------------
  (defmacro Smt-verified-cp (clause hint)
    `(Smtlink-subgoals clause
                       ;; A and G-prim and hints
                       (Smt-goal-generator (remove-hint-please ,clause) ,hint state)))
  )

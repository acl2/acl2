;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 6th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "basics")
(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")
(include-book "lambda-substitution")

;;-------------------------------------------------------------
;; (defsection add-hypo-cp
;;   :parents (verified)
;;   :short "Verified clause-processor for adding user hypotheses"

(local (in-theory (disable w)))

(local
 (defthm symbol-pseudo-term-alist-implies-pseudo-term-subst
   (implies (symbol-pseudo-term-alistp x)
            (acl2::pseudo-term-substp x))
   :hints (("Goal"
            :in-theory (enable acl2::pseudo-term-substp))))
 )

(define get-substed-hypo ((smt-hypo smt-hypo-p)
                          state)
  :returns (substed-hypo pseudo-termp)
  (b* ((smt-hypo (smt-hypo-fix smt-hypo))
       ((smt-hypo h) smt-hypo)
       (hypo-thm (acl2::meta-extract-formula-w h.thm (w state)))
       ((unless (pseudo-termp hypo-thm))
        (prog2$ (er hard? 'add-hypo-cp=>get-substed-hypo
                    "Formula returned by meta-extract ~p0 is not a pseudo-termp: ~p1~%"
                    h.thm hypo-thm)
                ''t))
       (hypo-thm-expanded (expand-lambda hypo-thm)))
    (acl2::substitute-into-term hypo-thm-expanded h.subst)))

(local (defthm crock (alistp (ev-smtcp-alist x a))))

(defthm correctness-of-get-substed-hypo
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (smt-hypo-p smt-hypo)
                (alistp a))
           (ev-smtcp (get-substed-hypo smt-hypo state) a))
  :hints (("Goal"
           :in-theory (e/d (get-substed-hypo) (w)))))

(define add-hypo ((cl pseudo-term-listp)
                  (smt-hypo-lst smt-hypo-list-p)
                  state)
  :returns (new-cl pseudo-term-listp)
  :measure (len smt-hypo-lst)
  (b* ((cl (pseudo-term-list-fix cl))
       (smt-hypo-lst (smt-hypo-list-fix smt-hypo-lst))
       ((unless (consp smt-hypo-lst)) cl)
       ((cons smt-hypo-hd smt-hypo-tl) smt-hypo-lst)
       (res-hd (get-substed-hypo smt-hypo-hd state)))
    (cons `(not ,res-hd) (add-hypo cl smt-hypo-tl state))))

(defthm correctness-of-add-hypo
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp (disjoin (add-hypo cl hypo-lst state)) a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :in-theory (enable add-hypo))))

(define add-hypo-cp ((cl pseudo-term-listp)
                     (hints t)
                     state)
  (b* (((unless (smtlink-hint-p hints)) (value (list cl)))
       (cl (pseudo-term-list-fix cl))
       (next-cp (cdr (assoc-equal 'add-hypo *SMT-architecture*)))
       ((if (null next-cp)) (value (list cl)))
       (the-hint `(:clause-processor (,next-cp clause ',hints state)))
       (new-cl (add-hypo cl (smtlink-hint->hypotheses hints) state)))
    (value (list `((hint-please ',the-hint) ,@new-cl)))))

(defthm correctness-of-add-hypos
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (add-hypo-cp cl smtlink-hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :in-theory (e/d (add-hypo-cp)
                           (correctness-of-add-hypo))
           :use ((:instance correctness-of-add-hypo
                            (a a)
                            (hypo-lst (smtlink-hint->hypotheses smtlink-hint))))))
  :rule-classes :clause-processor)
;; )

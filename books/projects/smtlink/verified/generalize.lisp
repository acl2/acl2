;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 9th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
;; for symbol-fix
(include-book "centaur/fty/basetypes" :dir :system)
;; for symbol-list-fix
(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
;; To be compatible with Arithmetic books
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
;; Meta-extract stuff
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/generalize" :dir :system)

;; Include SMT books
(include-book "hint-interface")
(include-book "basics")
(include-book "hint-please")
(include-book "computed-hints")
(include-book "type-hyp")
(include-book "return-type")
(include-book "evaluator")

(set-state-ok t)

;; Below functions and theorems are adapted from
;; clause-processors/generalize.lisp so that it works with the evaluator I
;; defined here.
(define replace-alist-to-bindings ((alist alistp) bindings)
  :returns (aa alistp)
  (if (atom alist)
      nil
    (cons (cons (cdar alist) (ev-smtcp (caar alist) bindings))
          (replace-alist-to-bindings (cdr alist) bindings)))
  ///
  (defthm assoc-equal-replace-alist-to-bindings
    (implies (not (member-equal x (strip-cdrs alist)))
             (not (assoc-equal x (replace-alist-to-bindings alist env)))))

  (defthm assoc-in-replace-alist-to-bindings
    (implies (and (assoc-equal x alist)
                  (no-duplicatesp-equal (strip-cdrs alist)))
             (equal (assoc-equal (cdr (assoc-equal x alist))
                                 (replace-alist-to-bindings alist env))
                    (cons (cdr (assoc-equal x alist))
                          (ev-smtcp x env))))
    :hints (("goal" :induct (assoc-equal x alist))))

  (defthm definition-of-replace-alist-to-bindings
    (and (implies (not (consp alist))
                  (not (replace-alist-to-bindings alist bindings)))
         (implies (consp alist)
                  (equal (replace-alist-to-bindings alist bindings)
                         (cons (cons (cdr (car alist))
                                     (ev-smtcp (car (car alist))
                                               bindings))
                               (replace-alist-to-bindings (cdr alist)
                                                          bindings))))))
  )

(defun generalize-termlist-alist (clause hint env)
  (b* (((unless (and (true-listp hint)
                     (<= (len hint) 2)
                     (pseudo-term-listp (car hint))
                     (symbolp (cadr hint))))
        env)
       ((list termlist basename) hint)
       (basename (or (and (symbolp basename) basename) 'acl2::x))
       (clause-vars (acl2::simple-term-vars-lst clause))
       (syms (acl2::new-symbols-from-base (len termlist) basename clause-vars))
       (alist (pairlis$ termlist syms)))
    (append (replace-alist-to-bindings alist env) env)))

(defthm generalize-termlist-cp-correct-expand
  (implies (and (pseudo-term-listp clause)
                (alistp acl2::env)
                (ev-smtcp (conjoin-clauses (acl2::generalize-termlist-cp clause acl2::hint))
                          (generalize-termlist-alist clause acl2::hint acl2::env)))
           (ev-smtcp (disjoin clause) acl2::env))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (ev-smtcp-of-fncall-args)
                           (acl2::generalize-termlist-cp-correct))
           :use ((:functional-instance
                  acl2::generalize-termlist-cp-correct
                  (acl2::gen-eval ev-smtcp)
                  (acl2::gen-eval-lst ev-smtcp-lst)
                  (acl2::replace-alist-to-bindings replace-alist-to-bindings)
                  (acl2::generalize-termlist-alist generalize-termlist-alist))
                 ))))

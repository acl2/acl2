; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "sublis-var-meaning")
(include-book "std/util/bstar" :dir :system)
(include-book "join-thms")
(include-book "meta/pseudo-termp-lemmas" :dir :system)

(def-join-thms cterm-ev)

(defun match-simple-equality-hyp (lit)
  (declare (xargs :guard (pseudo-termp lit)))
  (b* (((mv ok lhs rhs)
        (case-match lit
          (('not ('equal lhs rhs)) (mv t lhs rhs))
          (& (mv nil nil nil))))
       ((unless ok) (mv nil nil))
       ((mv ok var val)
        (cond ((and (symbolp lhs) lhs (quotep rhs))
               (mv t lhs rhs))
              ((and (symbolp rhs) rhs (quotep lhs))
               (mv t rhs lhs))
              (t (mv nil nil nil))))
       ((unless ok) (mv nil nil)))
    (mv t (cons var val))))

(defthm match-simple-equality-hyp-correct
  (b* (((mv ok (cons var val)) (match-simple-equality-hyp lit)))
    (implies (and ok (not (cterm-ev lit a)))
             (equal (cdr (assoc var a)) (cterm-ev val a)))))

(defun collect-simple-equality-hyps (clause)
  ;; returns (mv clause' subst-alist), where clause' is a subset of clause
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((when (atom clause)) nil)
       (rest-subst
        (collect-simple-equality-hyps (cdr clause)))
       (lit (car clause))
       ((mv matched pair) (match-simple-equality-hyp lit)))
    (if matched
        (cons pair rest-subst)
      rest-subst)))

(defun cterm-ev-subst-alistp (x a)
  (or (atom x)
      (and (consp (car x))
           (caar x)
           (symbolp (caar x))
           (equal (cdr (assoc (caar x) a))
                  (cterm-ev (cdar x) a))
           (cterm-ev-subst-alistp (cdr x) a))))

(defthm lookup-in-cterm-ev-subst-alistp
  (implies (and (cterm-ev-subst-alistp b a)
                (assoc k b))
           (equal (cterm-ev (cdr (assoc k b)) a)
                  (cterm-ev k a))))

(mutual-recursion
 (defun term-ind (x)
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         (t (termlist-ind (cdr x)))))
 (defun termlist-ind (x)
   (if (atom x)
       nil
     (cons (term-ind (car x))
           (termlist-ind (cdr x))))))

(flag::make-flag term-flg term-ind
                 :flag-mapping ((term-ind . term)
                                (termlist-ind . list)))

(local (defthm assoc-append-when-key
         (implies k
                  (equal (assoc k (append a b))
                         (or (assoc k a) (assoc k b))))))

(defthm-term-flg
  (defthm eval-under-append-cterm-ev-subst-alist
    (implies (and (cterm-ev-subst-alistp b a)
                  (pseudo-termp x))
             (equal (cterm-ev x (append (cterm-ev-alist b a) a))
                    (cterm-ev x a)))
    :hints ('(:in-theory (enable cterm-ev-of-fncall-args)))
    :flag term)
  (defthm eval-list-under-append-cterm-ev-subst-alist
    (implies (and (cterm-ev-subst-alistp b a)
                  (pseudo-term-listp x))
             (equal (cterm-ev-lst x (append (cterm-ev-alist b a) a))
                    (cterm-ev-lst x a)))
    :flag list))

(defun normalize-formals/actuals (formals actuals seen-formals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (symbol-listp seen-formals)
                              (equal (len formals) (len actuals)))))
  (if (atom formals)
      (mv nil nil)
    (if (or (member (car formals) seen-formals)
            (not (car formals)))
        (normalize-formals/actuals (cdr formals) (cdr actuals) seen-formals)
      (mv-let (rest-f rest-a)
        (normalize-formals/actuals (cdr formals) (cdr actuals)
                                   (cons (car formals) seen-formals))
        (mv (cons (car formals) rest-f)
            (cons (car actuals) rest-a))))))

(defthm normalize-formals/actuals-correct
  (mv-let (nformals nactuals)
    (normalize-formals/actuals formals actuals seen-formals)
    (implies (and k (not (member k seen-formals)))
             (equal (assoc k (pairlis$ nformals (cterm-ev-lst nactuals a)))
                    (assoc k (pairlis$ formals (cterm-ev-lst actuals a)))))))

(defthm-term-flg
  (defthm eval-under-normalize-formals/actuals
    (mv-let (nformals nactuals)
      (normalize-formals/actuals formals actuals nil)
      (implies (pseudo-termp x)
               (equal (cterm-ev x (pairlis$ nformals (cterm-ev-lst nactuals a)))
                      (cterm-ev x (pairlis$ formals (cterm-ev-lst actuals a))))))
    :hints ('(:in-theory (enable cterm-ev-of-fncall-args)))
    :flag term)
  (defthm eval-list-under-normalize-formals/actuals
    (mv-let (nformals nactuals)
      (normalize-formals/actuals formals actuals nil)
      (implies (pseudo-term-listp x)
               (equal (cterm-ev-lst x (pairlis$ nformals (cterm-ev-lst nactuals a)))
                      (cterm-ev-lst x (pairlis$ formals (cterm-ev-lst actuals a))))))
    :flag list))

(defthm normalize-formals/actuals-pseudo-term-listp
  (implies (pseudo-term-listp actuals)
           (pseudo-term-listp (mv-nth 1 (normalize-formals/actuals
                                         formals actuals seen-formals)))))

(defthm normalize-formals/actuals-symbol-listp
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (normalize-formals/actuals
                                    formals actuals seen-formals)))))

(defthm normalize-formals/actuals-type-0
  (true-listp (mv-nth 0 (normalize-formals/actuals formals actuals
                                                   seen-formals)))
  :rule-classes :type-prescription)

(defthm normalize-formals/actuals-type-1
  (true-listp (mv-nth 1 (normalize-formals/actuals formals actuals
                                                   seen-formals)))
  :rule-classes :type-prescription)

(defthm len-of-normalize-formals/actuals
  (equal (len (mv-nth 1 (normalize-formals/actuals formals actuals
                                                   seen-formals)))
         (len (mv-nth 0 (normalize-formals/actuals formals actuals
                                                   seen-formals)))))

(defthm normalize-formals/actuals-nonnil-symbols
  (not (member nil (mv-nth 0 (normalize-formals/actuals formals actuals
                                                        seen-formals)))))

(defthmd normalize-formals/actuals-no-members-of-seen-formals
  (implies (member k seen-formals)
           (not (member k (mv-nth 0 (normalize-formals/actuals formals actuals
                                                               seen-formals))))))

(defthm normalize-formals/actuals-no-duplicate-vars
  (no-duplicatesp-equal
   (mv-nth 0 (normalize-formals/actuals formals actuals seen-formals)))
  :hints(("Goal" :in-theory (enable normalize-formals/actuals-no-members-of-seen-formals))))

(local (defthm collect-simple-equality-hyps-subst-correct
         (b* ((subst (collect-simple-equality-hyps clause)))
           (implies (not (cterm-ev (disjoin clause) a))
                    (cterm-ev-subst-alistp subst a)))))

;; (defthm collect-simple-equality-hyps-clause-correct
;;   (b* (((mv ?new-clause ?subst) (collect-simple-equality-hyps clause)))
;;     (implies (not (cterm-ev (disjoin clause) a))
;;              (not (cterm-ev (disjoin new-clause) a)))))

(defun bindings-to-const-alist (formals actuals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (equal (len formals) (len actuals)))))
  (if (atom formals)
      nil
    (if (and (car formals)
             (not (member (car formals) (cdr formals)))
             (quotep (car actuals)))
        (cons (cons (car formals) (car actuals))
              (bindings-to-const-alist (cdr formals) (cdr actuals)))
      (bindings-to-const-alist (cdr formals) (cdr actuals)))))

(defthm cterm-ev-subst-alistp-cons-non-key
  (implies (and (cterm-ev-subst-alistp b a)
                (quote-listp (strip-cdrs b))
                (not (assoc k b)))
           (cterm-ev-subst-alistp b (cons (cons k v) a))))

(defthm quote-listp-strip-cdrs-of-bindings-to-const-alist
  (quote-listp (strip-cdrs (bindings-to-const-alist formals actuals))))

(defthm not-assoc-bindings-to-const-alist-when-not-member-formals
  (implies (not (member k formals))
           (not (assoc k (bindings-to-const-alist formals actuals)))))

(defthm not-assoc-bindings-to-const-alist-nil
  (not (assoc nil (bindings-to-const-alist formals actuals))))

(defthm bindings-to-const-alist-correct
  (implies (and (symbol-listp formals)
                (no-duplicatesp-equal formals)
                (not (member nil formals))
                (pseudo-term-listp actuals)
                (equal (len formals) (len actuals)))
           (cterm-ev-subst-alistp
            (bindings-to-const-alist formals actuals)
            (pairlis$ formals (cterm-ev-lst actuals a)))))

(mutual-recursion
 ;; returns (mv changedp x)
 (defun deep-substitute-term (x subst)
   (declare (xargs :guard (and (pseudo-termp x)
                               (pseudo-term-val-alistp subst))
                   :verify-guards nil))
   (b* (((when (variablep x))
         (if x
             (b* ((look (assoc x subst)))
               (if look
                   (mv t (cdr look))
                 (mv nil x)))
           (mv nil nil)))
        ((when (fquotep x)) (mv nil x))
        ((mv args-changedp args) (deep-substitute-term-list (cdr x) subst))
        (fn (car x))
        ((unless (consp fn))
         (b* (((when (quote-listp args)) (cons-term1-mv2 fn args x))
              ((when (and (eq fn 'if)
                          (eql (len args) 3)
                          (quotep (car args))))
               (if (unquote (car args))
                   (mv t (cadr args))
                 (mv t (caddr args))))
              ((when args-changedp) (mv t (cons-term fn args))))
           (mv nil x)))
        ((mv formals actuals) (normalize-formals/actuals (cadr fn) args nil))
        (subst1 (bindings-to-const-alist formals actuals))
        ((mv body-changedp body) (if subst1
                                     (deep-substitute-term (caddr fn) subst1)
                                   (mv nil (caddr fn)))))
     (if (or body-changedp args-changedp)
         (mv t `((lambda ,formals ,body) . ,actuals))
       (mv nil x))))

 (defun deep-substitute-term-list (x subst)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (pseudo-term-val-alistp subst))))
   (b* (((when (atom x))
         (mbe :logic (if (eq x nil)
                         (mv nil nil)
                       (mv t nil))
              :exec (mv nil nil)))
        ((mv changedp1 a) (deep-substitute-term (car x) subst))
        ((mv changedp2 b) (deep-substitute-term-list (cdr x) subst)))
     (if (or changedp1 changedp2)
         (mv t (cons a b))
       (mv nil x)))))




(flag::make-flag deep-substitute-flg deep-substitute-term
                 :flag-mapping ((deep-substitute-term . term)
                                (deep-substitute-term-list . list)))

(defthm-deep-substitute-flg
  (defthm true-listp-deep-substitute-term-list
    (and (true-listp (mv-nth 1 (deep-substitute-term-list x subst)))
         (implies (not (true-listp x))
                  (mv-nth 0 (deep-substitute-term-list x subst))))
    :rule-classes ((:type-prescription
                    :corollary
                    (true-listp (mv-nth 1 (deep-substitute-term-list x subst)))))
    :flag list)
  :skip-others t)

(defthm-deep-substitute-flg
  (defthm len-of-deep-substitute-term-list
    (equal (len (mv-nth 1 (deep-substitute-term-list x subst)))
           (len x))
    :flag list)
  :skip-others t)

(defthm bindings-to-const-alist-pseudo-term-val-alistp
  (implies (pseudo-term-listp actuals)
           (pseudo-term-val-alistp (bindings-to-const-alist formals actuals))))

(defthm pseudo-termp-of-cons-term1-mv2
  (implies (and (symbolp fn) (not (eq fn 'quote))
                (pseudo-term-listp args)
                (pseudo-termp form))
           (pseudo-termp (mv-nth 1 (cons-term1-mv2 fn args form))))
  :hints(("Goal" :in-theory (enable cons-term1-mv2))))

(defthm-deep-substitute-flg
  (defthm pseudo-termp-deep-substitute-term
    (implies (and (pseudo-termp x)
                  (pseudo-term-val-alistp subst))
             (pseudo-termp (mv-nth 1 (deep-substitute-term x subst))))
    :flag term)
  (defthm pseudo-term-listp-deep-substitute-term-list
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-val-alistp subst))
             (pseudo-term-listp (mv-nth 1 (deep-substitute-term-list x subst))))
    :flag list))

(local (defthm pseudo-term-val-alistp-impl-alistp
         (implies (pseudo-term-val-alistp x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable pseudo-term-val-alistp)))
         :rule-classes :forward-chaining))

(encapsulate nil
  (local (defthm unquote-guard-when-pseudo-term-listp
           (implies (and (pseudo-term-listp x)
                         (equal (caar x) 'quote))
                    (consp (cdar x)))))

  (verify-guards deep-substitute-term))

(encapsulate nil
  (set-irrelevant-formals-ok t)
  (mutual-recursion
   ;; returns (mv changedp x)
   (defun deep-substitute-term/alist (x subst alist)
     (b* (((when (variablep x))
           (if x
               (b* ((look (assoc x subst)))
                 (if look
                     (mv t (cdr look))
                   (mv nil x)))
             (mv nil nil)))
          ((when (fquotep x)) (mv nil x))
          ((mv args-changedp args) (deep-substitute-term-list/alist (cdr x) subst alist))
          (fn (car x))
          ((unless (consp fn))
           (b* (((when (quote-listp args)) (cons-term1-mv2 fn args x))
                ((when (and (eq fn 'if)
                            (eql (len args) 3)
                            (quotep (car args))))
                 (if (unquote (car args))
                     (mv t (cadr args))
                   (mv t (caddr args))))
                ((when args-changedp) (mv t (cons-term fn args))))
             (mv nil x)))
          ((mv formals actuals) (normalize-formals/actuals (cadr fn) args nil))
          (subst1 (bindings-to-const-alist formals actuals))
          ((mv body-changedp body) (if subst1
                                       (deep-substitute-term/alist
                                        (caddr fn) subst1
                                        (pairlis$ formals (cterm-ev-lst actuals alist)))
                                     (mv nil (caddr fn)))))
       (if (or body-changedp args-changedp)
           (mv t `((lambda ,formals ,body) . ,actuals))
         (mv nil x))))

   (defun deep-substitute-term-list/alist (x subst alist)
     (b* (((when (atom x))
           (mbe :logic (if (eq x nil)
                           (mv nil nil)
                         (mv t nil))
                :exec (mv nil nil)))
          ((mv changedp1 a) (deep-substitute-term/alist (car x) subst alist))
          ((mv changedp2 b) (deep-substitute-term-list/alist (cdr x) subst alist)))
       (if (or changedp1 changedp2)
           (mv t (cons a b))
         (mv nil x))))))

(flag::make-flag deep-substitute/alist-flg deep-substitute-term/alist
                 :flag-mapping ((deep-substitute-term/alist . term)
                                (deep-substitute-term-list/alist . list)))

(local
 (defthm-deep-substitute/alist-flg
   (defthm deep-substitute-term/alist-correct
     (equal (deep-substitute-term/alist x subst alist)
            (deep-substitute-term x subst))
     :flag term)
   (defthm deep-substitute-term-list/alist-correct
     (equal (deep-substitute-term-list/alist x subst alist)
            (deep-substitute-term-list x subst))
     :flag list)))

(defthm-deep-substitute/alist-flg
  (defthm deep-substitute-term-correct
    (implies (and (pseudo-termp x)
                  (pseudo-term-val-alistp subst)
                  (cterm-ev-subst-alistp subst alist))
             (equal (cterm-ev (mv-nth 1 (deep-substitute-term x subst)) alist)
                    (cterm-ev x alist)))
    :hints ('(:in-theory (enable cterm-ev-of-fncall-args)
              :expand ((deep-substitute-term x subst))))
    :flag term)
  (defthm deep-substitute-term-list-correct
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-val-alistp subst)
                  (cterm-ev-subst-alistp subst alist))
             (equal (cterm-ev-lst (mv-nth 1 (deep-substitute-term-list x subst)) alist)
                    (cterm-ev-lst x alist)))
    :hints ('(:expand ((deep-substitute-term-list x subst))))
    :flag list))

(defthm deep-substitute-term-disjoin-correct
  (implies (and (pseudo-term-listp x)
                (pseudo-term-val-alistp subst)
                (cterm-ev-subst-alistp subst alist))
           (iff (cterm-ev (disjoin (mv-nth 1 (deep-substitute-term-list x subst))) alist)
                (cterm-ev (disjoin x) alist)))
  :hints (("goal" :induct (len x)
           :in-theory (enable cterm-ev-disjoin-when-consp))))


(defthm pseudo-term-val-alistp-of-collect-simple-equality-hyps
  (implies (pseudo-term-listp clause)
           (pseudo-term-val-alistp (collect-simple-equality-hyps
                                    clause))))

;; (defthm pseudo-term-listp-of-collect-simple-equality-hyps
;;   (implies (pseudo-term-listp clause)
;;            (pseudo-term-listp (mv-nth 0 (collect-simple-equality-hyps clause)))))

(defun constant-prop-non-equality-hyps (clause subst)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (pseudo-term-val-alistp subst))))
  (b* (((when (atom clause)) nil)
       ((mv matched &) (match-simple-equality-hyp (car clause)))
       ((when matched)
        (cons (car clause)
              (constant-prop-non-equality-hyps (cdr clause) subst)))
       ((mv ?changedp lit)
        (deep-substitute-term (car clause) subst)))
    (cons lit
          (constant-prop-non-equality-hyps (cdr clause) subst))))

(defthm constant-prop-non-equality-hyps-correct
  (implies (and (pseudo-term-listp clause)
                (pseudo-term-val-alistp subst)
                (cterm-ev-subst-alistp subst alist))
           (iff (cterm-ev (disjoin (constant-prop-non-equality-hyps
                                    clause subst))
                          alist)
                (cterm-ev (disjoin clause) alist)))
  :hints(("Goal" :in-theory (disable deep-substitute-term match-simple-equality-hyp))))

(defun constant-prop-cp (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* ((subst-alist (collect-simple-equality-hyps clause))
       (new-clause
        (constant-prop-non-equality-hyps clause subst-alist)))
    (list new-clause)))

(defthm constant-prop-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (cterm-ev (conjoin-clauses (constant-prop-cp clause)) a))
           (cterm-ev (disjoin clause) a))
  :rule-classes :clause-processor)

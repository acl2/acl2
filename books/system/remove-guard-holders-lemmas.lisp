; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports remove-guard-holders.lisp.  Normally this book would
; therefore be called remove-guard-holders-support.lisp.  However, some of the
; lemmas in it may be useful; in fact, originally all of this work was
; contained in remove-guard-holders.lisp, but Eric Smith requested that we
; separate out such lemmas into this book.

(in-package "ACL2")

(include-book "subcor-var")
(local (include-book "tools/flag" :dir :system))
(local (include-book "pseudo-termp-lemmas"))
; Why again?
; (local (include-book "subcor-var"))

(verify-termination weak-badge-userfn-structure-alistp) ; and guards

(verify-termination ilks-plist-worldp) ; and guards

(local (defthm weak-badge-userfn-structure-alistp-forward-to-alistp
         (implies (weak-badge-userfn-structure-alistp x)
                  (alistp x))
         :rule-classes :forward-chaining))

; The following lemma is not really useful as a rewrite rule because both
; conjuncts in the conclusion ought to be expanded into their individual
; conjuncts.  So we store it with :rule-classes nil and just :use it when
; needed.

(local (defthm weak-badge-userfn-structure-alistp-gives-access
         (implies (and (weak-badge-userfn-structure-alistp x)
                       (assoc-equal fn x))
                  (and (weak-badge-userfn-structure-tuplep (assoc-equal fn x))
                       (weak-apply$-badge-p
                        (access-badge-userfn-structure-tuple-badge
                         (assoc-equal fn x)))))
         :rule-classes nil))

(verify-termination ilks-per-argument-slot
  (declare (xargs :guard-hints
                  (("Goal"
                    :use
                    (:instance
                     weak-badge-userfn-structure-alistp-gives-access
                     (x (CDR
                         (ASSOC-EQUAL :BADGE-USERFN-STRUCTURE
                                      (FGETPROP 'BADGE-TABLE
                                                'TABLE-ALIST
                                                NIL WRLD))))))))))

(verify-termination (remove-guard-holders1
                     (declare (xargs :verify-guards nil))))

(local (make-flag remove-guard-holders1))

(local (defthm equal-len-0-rewrite
         (equal (equal 0 (len x))
                (not (consp x)))))

(local (defun my-double-cdr-induction (lst ilks)
         (if (atom lst)
             (list lst ilks)
           (my-double-cdr-induction (cdr lst) (cdr ilks)))))

(defthm len-mv-nth-1-remove-guard-holders1-lst
  (equal (len (mv-nth 1 (remove-guard-holders1-lst lst lamp)))
         (len lst))
  :hints (("Goal" :induct (my-double-cdr-induction lst ilks))))

(local (defthm pseudo-termp-car-last
         (implies (pseudo-term-listp term)
                  (pseudo-termp (car (last term))))))

(local (defthm-flag-remove-guard-holders1
         (defthm pseudo-termp-remove-guard-holders1
           (implies (pseudo-termp term)
                    (pseudo-termp
                     (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
           :flag remove-guard-holders1)
         (defthm pseudo-term-listp-remove-guard-holders1-lst
           (implies (pseudo-term-listp lst)
                    (pseudo-term-listp
                     (mv-nth 1 (remove-guard-holders1-lst lst lamp))))
           :flag remove-guard-holders1-lst)))

(defthm pseudo-termp-remove-guard-holders1 ; redundant
  (implies (pseudo-termp term)
           (pseudo-termp
            (mv-nth 1 (remove-guard-holders1 changedp0 term lamp)))))

(defthm pseudo-term-listp-remove-guard-holders1-lst ; redundant
  (implies (pseudo-term-listp lst)
           (pseudo-term-listp
            (mv-nth 1 (remove-guard-holders1-lst lst lamp)))))

(local
 (defthm pseudo-term-listp-remove-guard-holders1-lst-forward
   (implies (pseudo-term-listp lst)
            (pseudo-term-listp
             (mv-nth 1 (remove-guard-holders1-lst lst lamp))))
   :rule-classes ((:forward-chaining
                   :trigger-terms
                   ((mv-nth 1 (remove-guard-holders1-lst lst lamp)))))))

; It was tempting to avoid the following, but the approach in the
; remove-guard-holders.lisp requires it.
(verify-guards remove-guard-holders1)


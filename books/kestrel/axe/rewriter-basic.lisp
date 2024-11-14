; A general-purpose Axe Rewriter
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in rewriter-basic-tests.lisp

(include-book "make-rewriter-simple")
(include-book "evaluator-basic")
(include-book "axe-syntaxp-evaluator-basic")
(include-book "axe-bind-free-evaluator-basic")

;; Create a "basic" rewriter.  Here, "basic" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-term-basic, simp-term-basic, simp-terms-basic, simplify-dag-basic,
;; and def-simplified-dag-basic.
(make-rewriter-simple basic
                      axe-evaluator-basic
                      basic
                      basic)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp new-conjuncts againp) where NEW-CONJUNCTS is a set of terms
;; whose conjunction is equal to the conjunction of the CONJUNCTS and the
;; DONE-CONJUNCTS.
(defund simplify-conjuncts-once-basic (conjuncts
                                       done-conjuncts ; an accumulator, also used as assumptions
                                       ;;print
                                       rule-alist
                                       known-booleans
                                       monitored-symbols
                                       memoizep
                                       warn-missingp
                                       againp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (pseudo-term-listp done-conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (booleanp warn-missingp)
                              (booleanp againp)
                              (symbol-listp known-booleans))
                  :measure (len conjuncts)))
  (if (endp conjuncts)
      (mv (erp-nil) (reverse done-conjuncts) againp)
    (b* ((term (first conjuncts))
         ((mv erp result-term)
          (simp-term-basic term ; todo: in theory, this could blow up
                           ;; Can assume all the other conjuncts, because, if any is false, the whole conjunction is false:
                           (append (rest conjuncts) done-conjuncts) ; the assumptions; note that we don't use the term to simplify itself!
                           rule-alist
                           nil ; interpreted-function-alist
                           monitored-symbols
                           nil
                           memoizep
                           nil nil nil known-booleans))
         ((when erp) (mv erp nil nil))
         )
      (if (equal result-term term) ;; no change: ; todo: flatten, as we do below?
          (simplify-conjuncts-once-basic (rest conjuncts) (cons term done-conjuncts) rule-alist known-booleans monitored-symbols memoizep warn-missingp againp)
        (if (equal *t* result-term) ;todo: also check for *nil*?
            ;; if the term became t, drop it:
            (simplify-conjuncts-once-basic (rest conjuncts) done-conjuncts rule-alist known-booleans monitored-symbols memoizep warn-missingp againp) ; we don't set againp here since the term got dropped and won't support further simplifications
          (let ((new-conjuncts (get-conjuncts-of-term2 result-term))) ;flatten any conjunction returned (some conjuncts may be needed to simplify others)
            (simplify-conjuncts-once-basic (rest conjuncts) (append new-conjuncts done-conjuncts) rule-alist known-booleans monitored-symbols memoizep warn-missingp t)))))))

(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local
  (defthm pseudo-term-listp-of-mv-nth-1-of-simplify-conjuncts-once-basic
    (implies (and (pseudo-term-listp conjuncts)
                  (pseudo-term-listp done-conjuncts)
                  (rule-alistp rule-alist)
                  (symbol-listp monitored-symbols)
                  (booleanp memoizep)
                  (booleanp warn-missingp)
                  (booleanp againp)
                  (symbol-listp known-booleans))
             (pseudo-term-listp (mv-nth 1 (simplify-conjuncts-once-basic conjuncts
                                                                         done-conjuncts ; an accumulator, also used as assumptions
                                                                         ;;print
                                                                         rule-alist
                                                                         known-booleans
                                                                         monitored-symbols
                                                                         memoizep
                                                                         warn-missingp
                                                                         againp))))
    :hints (("Goal" :in-theory (e/d (simplify-conjuncts-once-basic) (reverse-becomes-reverse-list-gen reverse-becomes-reverse-list))))))

;; Returns (mv erp new-conjuncts) where NEW-CONJUNCTS is a set of conjuncts
;; whose conjunction is equal to the conjunction of the CONJUNCTS.
(defun simplify-conjunction-basic-aux (passes-left conjuncts rule-alist known-booleans monitored-symbols memoizep warn-missingp)
  (declare (xargs :guard (and (natp passes-left)
                              (pseudo-term-listp conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (booleanp warn-missingp)
                              (symbol-listp known-booleans))))
  (if (zp passes-left)
      (prog2$ (cw "NOTE: Limit reached when simplifying conjuncts repeatedly.~%")
              (mv (erp-nil) conjuncts))
    (b* (((mv erp new-conjuncts againp)
          (simplify-conjuncts-once-basic conjuncts nil rule-alist known-booleans monitored-symbols memoizep warn-missingp nil))
         ((when erp) (mv erp nil)))
      (if againp
          (simplify-conjunction-basic-aux (+ -1 passes-left) new-conjuncts rule-alist known-booleans monitored-symbols memoizep warn-missingp)
        (mv (erp-nil) new-conjuncts)))))

;; Returns (mv erp new-conjuncts) where NEW-CONJUNCTS is a set of conjuncts
;; whose conjunction is equal to the conjunction of the CONJUNCTS.
(defund simplify-conjunction-basic (conjuncts rule-alist known-booleans monitored-symbols memoizep warn-missingp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (booleanp warn-missingp)
                              (symbol-listp known-booleans))))
  (progn$ (and monitored-symbols (cw "(Monitoring: ~x0)~%" monitored-symbols)) ; todo: make optional
          (and warn-missingp (print-missing-rules monitored-symbols rule-alist)) ; we do this just once, here
          (let ((len (len conjuncts)))
            ;; We add 1 so that if len=1 we get at least 2 passes:
            (simplify-conjunction-basic-aux (+ 1 (* len len)) conjuncts rule-alist known-booleans
                                            monitored-symbols memoizep
                                            nil ; don't warn again about missing monitored rules
                                            ))))

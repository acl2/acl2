; A general-purpose Axe Rewriter
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; Create a "basic" rewriter.  Here, "basic" refers to the set of functions to
;; evaluate and to the sets of axe-syntaxp and axe-bind-free functions that the
;; rewriter "knows" about.  To understand what gets generated, see
;; make-rewriter-simple-fn.  The main interface functions are
;; simplify-dag-basic, simplify-term-basic, simplify-term-to-term-basic,
;; simplify-terms-to-terms-basic, and def-simplified-basic.
(make-rewriter-simple basic
                      axe-evaluator-basic
                      basic
                      basic
                      :smt nil ; don't use SMT (but see rewriter-basic-smt.lisp)
                      )

;dup
(local
 (defthm pseudo-term-listp-of-reverse-list
   (equal (pseudo-term-listp (reverse-list acc))
          (pseudo-term-listp (true-list-fix acc)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp reverse-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp new-conjuncts againp) where NEW-CONJUNCTS is a set of terms
;; whose conjunction is equal to the conjunction of the CONJUNCTS and the
;; DONE-CONJUNCTS.
(defund simplify-conjuncts-basic (conjuncts
                                  done-conjuncts ; an accumulator, also used as assumptions
                                  ;;print
                                  rule-alist
                                  known-booleans
                                  monitored-symbols
                                  memoizep
                                  count-hits
                                  warn-missingp
                                  againp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (pseudo-term-listp done-conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp known-booleans)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (count-hits-argp count-hits)
                              (booleanp warn-missingp)
                              (booleanp againp))
                  :measure (len conjuncts)))
  (if (endp conjuncts)
      (mv (erp-nil) (reverse done-conjuncts) againp)
    (b* ((term (first conjuncts))
         ((mv erp result-term)
          (simplify-term-to-term-basic term ; todo: in theory, this could blow up
                                       ;; Can assume all the other conjuncts, because, if any is false, the whole conjunction is false:
                                       (append (rest conjuncts) done-conjuncts) ; the assumptions; note that we don't use the term to simplify itself!
                                       rule-alist
                                       nil ; interpreted-function-alist
                                       known-booleans
                                       nil ; normalize-xors
                                       nil ; limits
                                       memoizep
                                       count-hits
                                       nil ; print
                                       monitored-symbols
                                       nil ; fns-to-elide
                                       ))
         ((when erp) (mv erp nil nil))
         )
      (if (equal result-term term) ;; no change: ; todo: flatten, as we do below?
          (simplify-conjuncts-basic (rest conjuncts) (cons term done-conjuncts) rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp againp)
        (if (equal *t* result-term) ;todo: also check for *nil*?
            ;; if the term became t, drop it:
            (simplify-conjuncts-basic (rest conjuncts) done-conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp againp) ; we don't set againp here since the term got dropped and won't support further simplifications
          (let ((new-conjuncts (get-conjuncts-of-term2 result-term))) ;flatten any conjunction returned (some conjuncts may be needed to simplify others)
            (simplify-conjuncts-basic (rest conjuncts) (append new-conjuncts done-conjuncts) rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp t)))))))

(local
  (defthm pseudo-term-listp-of-mv-nth-1-of-simplify-conjuncts-basic
    (implies (and (pseudo-term-listp conjuncts)
                  (pseudo-term-listp done-conjuncts)
                  (rule-alistp rule-alist)
                  ;; (symbol-listp known-booleans)
                  ;; (symbol-listp monitored-symbols)
                  ;; (booleanp memoizep)
                  ;; (booleanp warn-missingp)
                  ;; (booleanp againp)
                  )
             (pseudo-term-listp (mv-nth 1 (simplify-conjuncts-basic conjuncts
                                                                    done-conjuncts ; an accumulator, also used as assumptions
                                                                    ;;print
                                                                    rule-alist
                                                                    known-booleans
                                                                    monitored-symbols
                                                                    memoizep
                                                                    count-hits
                                                                    warn-missingp
                                                                    againp))))
    :hints (("Goal" :in-theory (enable simplify-conjuncts-basic)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp new-conjuncts) where NEW-CONJUNCTS is a set of conjuncts
;; whose conjunction is equal to the conjunction of the CONJUNCTS.
(defun simplify-conjunction-basic-aux (passes-left conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp)
  (declare (xargs :guard (and (natp passes-left)
                              (pseudo-term-listp conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (count-hits-argp count-hits)
                              (booleanp warn-missingp)
                              (symbol-listp known-booleans))))
  (if (zp passes-left)
      (prog2$ (cw "NOTE: Limit reached when simplifying conjuncts repeatedly.~%")
              (mv (erp-nil) conjuncts))
    (b* (((mv erp new-conjuncts againp)
          (simplify-conjuncts-basic conjuncts nil rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp nil))
         ((when erp) (mv erp nil)))
      (if againp
          (simplify-conjunction-basic-aux (+ -1 passes-left) new-conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp)
        (mv (erp-nil) new-conjuncts)))))

(local
  (defthm pseudo-term-listp-of-mv-nth-1-of-simplify-conjunction-basic-aux
    (implies (and ;; (natp passes-left)
                  (pseudo-term-listp conjuncts)
                  (rule-alistp rule-alist)
                  ;; (symbol-listp known-booleans)
                  ;; (symbol-listp monitored-symbols)
                  ;; (booleanp memoizep)
                  ;; (booleanp warn-missingp)
                  )
             (pseudo-term-listp (mv-nth 1 (simplify-conjunction-basic-aux passes-left conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Repeatedly simplifies the CONJUNCTS using the RULE-ALIST.
;; Returns (mv erp new-conjuncts) where NEW-CONJUNCTS is a set of conjuncts
;; whose conjunction is equal to the conjunction of the CONJUNCTS.
(defund simplify-conjunction-basic (conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (rule-alistp rule-alist)
                              (symbol-listp known-booleans)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (count-hits-argp count-hits)
                              (booleanp warn-missingp))))
  (progn$ (and monitored-symbols (cw "(Monitoring: ~x0)~%" monitored-symbols)) ; todo: make optional
          (and warn-missingp (print-missing-rules monitored-symbols rule-alist)) ; we do this just once, here
          (let ((len (len conjuncts)))
            ;; We add 1 so that if len=1 we get at least 2 passes:
            (simplify-conjunction-basic-aux (+ 1 (* len len)) conjuncts rule-alist known-booleans
                                            monitored-symbols memoizep count-hits
                                            nil ; don't warn again about missing monitored rules
                                            ))))

(defthm pseudo-term-listp-of-mv-nth-1-of-simplify-conjunction-basic
  (implies (and (pseudo-term-listp conjuncts)
                (rule-alistp rule-alist)
                ;; (symbol-listp known-booleans)
                ;; (symbol-listp monitored-symbols)
                ;; (booleanp memoizep)
                ;; (booleanp warn-missingp)
                )
           (pseudo-term-listp (mv-nth 1 (simplify-conjunction-basic conjuncts rule-alist known-booleans monitored-symbols memoizep count-hits warn-missingp))))
  :hints (("Goal" :in-theory (enable simplify-conjunction-basic))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simplifies fully using each of the RULE-ALISTS in turn.
;; Returns (mv erp new-conjuncts) where NEW-CONJUNCTS is a set of conjuncts
;; whose conjunction is equal to the conjunction of the CONJUNCTS.
;; TODO call print-missing-rules and suppress further such printing by passing nil for warn-missingp
(defund simplify-conjunction-with-rule-alists-basic (conjuncts rule-alists known-booleans monitored-symbols memoizep count-hits warn-missingp)
  (declare (xargs :guard (and (pseudo-term-listp conjuncts)
                              (rule-alistsp rule-alists)
                              (symbol-listp known-booleans)
                              (symbol-listp monitored-symbols)
                              (booleanp memoizep)
                              (count-hits-argp count-hits)
                              (booleanp warn-missingp))
                  :measure (len rule-alists)))
  (if (endp rule-alists)
      (mv (erp-nil) conjuncts)
    (b* (((mv erp conjuncts)
          (simplify-conjunction-basic conjuncts (first rule-alists) known-booleans monitored-symbols memoizep count-hits warn-missingp))
         ((when erp) (mv erp conjuncts)))
      (simplify-conjunction-with-rule-alists-basic conjuncts (rest rule-alists) known-booleans monitored-symbols memoizep count-hits warn-missingp))))

(defthm pseudo-term-listp-of-mv-nth-1-of-simplify-conjunction-with-rule-alists-basic
  (implies (and (pseudo-term-listp conjuncts)
                (rule-alistsp rule-alists)
                ;; (symbol-listp known-booleans)
                ;; (symbol-listp monitored-symbols)
                ;; (booleanp memoizep)
                ;; (booleanp warn-missingp)
                )
           (pseudo-term-listp (mv-nth 1 (simplify-conjunction-with-rule-alists-basic conjuncts rule-alists known-booleans monitored-symbols memoizep count-hits warn-missingp))))
  :hints (("Goal" :in-theory (enable simplify-conjunction-with-rule-alists-basic))))

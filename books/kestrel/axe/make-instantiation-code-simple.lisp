; A tool to generate hyp instantiation code that calls a given evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book provides a tool that, given the name of an evaluator, makes a
;; version of instantiate-hyp that uses it.

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "all-dargp-less-than")
(include-book "axe-trees")

(defun make-instantiation-code-simple-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((instantiate-hyp-name (pack$ 'instantiate-hyp- suffix))
        (instantiate-hyp-lst-name (pack$ 'instantiate-hyp- suffix '-lst))
        (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args)))
    `(encapsulate ()
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/lists-light/cons" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

       ;; TERM is from a hyp of a rule and so has quoteps and vars at the leaves.
       ;; ALIST binds vars to dargs (nodenums/ quoteps).
       ;; Returns (mv instantiated-hyp free-vars-flg).
       (mutual-recursion
        ;; Returns (mv term free-vars-flg) where TERM has been instantiated with ALIST and FREE-VARS-FLG indicates whether any variables remain in TERM.
        (defund ,instantiate-hyp-name (term alist interpreted-function-alist)
          (declare (xargs :verify-guards nil ;done below
                          :guard (and (pseudo-termp term)
                                      (symbol-alistp alist)
                                      (all-dargp (strip-cdrs alist))
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (variablep term)
              (let ((match (assoc-eq term alist)))
                (if match
                    (mv (cdr match) nil) ;the var has a binding in the alist and so is not free
                  (mv term t)            ;no match for the var, so it is free
                  ))
            (let ((fn (ffn-symb term)))
              (if (eq 'quote fn)
                  (mv term nil) ; no free vars
                ;;a function call (previously, we handled IFs specially but that didn't seem worth it):
                (mv-let (all-quotep args free-vars-in-args-flg)
                  (,instantiate-hyp-lst-name (fargs term) alist interpreted-function-alist)
                  (if all-quotep
                      ;; Try to evaluate the ground term:
                      (mv-let (erp res)
                        (,apply-axe-evaluator-to-quoted-args-name fn args interpreted-function-alist)
                        (if erp ;; May be :unknown-function
                            (progn$
                             ;; If this message is printed a lot, we could suppress it:
                             ;; (cw "(Note: In instantiate-hyp: Failed to apply ~x0 to constant args.  Consider adding it to the evaluator, adding it to the interpreted-function-alist, or adding a constant-opener rule.)~%" fn)
                             (mv (cons fn args) ;; Return the ground term unevaluated
                                 nil ; no free vars since it's a ground term (even though we couldn't evaluate it)
                                 ))
                          (mv (if (eq res t)
                                  *t* ;saves a cons in this common case
                                (enquote res))
                              nil ; no free vars
                              )))
                    ;; The term has free vars iff the args did:
                    ;; TODO: Consider cons-with-hint here:
                    (mv (cons fn args) free-vars-in-args-flg)))))))

        ;; Returns (mv all-quotep args free-vars-flg).
        (defund ,instantiate-hyp-lst-name (terms alist interpreted-function-alist)
          (declare (xargs :guard (and (pseudo-term-listp terms)
                                      (symbol-alistp alist)
                                      (all-dargp (strip-cdrs alist))
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (endp terms)
              (mv t nil nil)
            (mv-let (instantiated-first first-term-free-vars-flg)
              (,instantiate-hyp-name (first terms) alist interpreted-function-alist)
              (mv-let (rest-all-quotep instantiated-rest rest-terms-free-vars-flg)
                (,instantiate-hyp-lst-name (rest terms) alist interpreted-function-alist)
                (mv (and rest-all-quotep (quotep instantiated-first))
                    (cons instantiated-first instantiated-rest)
                    (or first-term-free-vars-flg rest-terms-free-vars-flg)))))))

       (make-flag ,instantiate-hyp-name)

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- instantiate-hyp-lst-name)
           (true-listp (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist)))
           :flag ,instantiate-hyp-lst-name)
         :skip-others t
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'len-of-mv-nth-1-of- instantiate-hyp-lst-name)
           (equal (len (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist)))
                  (len terms))
           :flag ,instantiate-hyp-lst-name)
         :skip-others t
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'booleanp-of-mv-nth-1-of- instantiate-hyp-name)
           (booleanp (mv-nth 1 (,instantiate-hyp-name term alist interpreted-function-alist)))
           :flag ,instantiate-hyp-name)
         (defthm ,(pack$ 'booleanp-of-mv-nth-2-of- instantiate-hyp-lst-name)
           (booleanp (mv-nth 2 (,instantiate-hyp-lst-name terms alist interpreted-function-alist)))
           :flag ,instantiate-hyp-lst-name)
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
           (implies (and (pseudo-termp term)
                         (all-dargp (strip-cdrs alist)))
                    (axe-treep (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist))))
           :flag ,instantiate-hyp-name)
         (defthm ,(pack$ 'all-axe-treep-of-mv-nth-1-of- instantiate-hyp-lst-name)
           (implies (and (pseudo-term-listp terms)
                         (all-dargp (strip-cdrs alist)))
                    (all-axe-treep (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))))
           :flag ,instantiate-hyp-lst-name)
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'bounded-axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
           (implies (and (pseudo-termp term)
                         (all-dargp-less-than (strip-cdrs alist) dag-len))
                    (bounded-axe-treep (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist))
                                       dag-len))
           :flag ,instantiate-hyp-name)
         (defthm ,(pack$ 'all-bounded-axe-treep-of-mv-nth-1-of- instantiate-hyp-lst-name)
           (implies (and (pseudo-term-listp terms)
                         (all-dargp-less-than (strip-cdrs alist) dag-len))
                    (all-bounded-axe-treep (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))
                                           dag-len))
           :flag ,instantiate-hyp-lst-name)
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- instantiate-hyp-lst-name)
           (implies (and (mv-nth 0 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))
                         (pseudo-term-listp terms)
                         (all-dargp (strip-cdrs alist)))
                    (all-myquotep (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))))
           :flag ,instantiate-hyp-lst-name)
         :skip-others t
         :hints (("Goal" :in-theory (e/d (,instantiate-hyp-name ,instantiate-hyp-lst-name) (myquotep)))))

       (verify-guards ,instantiate-hyp-name :hints (("Goal" :in-theory (enable pseudo-termp))))

       (defthm ,(pack$ 'consp-of-mv-nth-0-of- instantiate-hyp-name)
         (implies (consp term)
                  (consp (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist))))
         :hints (("Goal" :expand ((,instantiate-hyp-name term alist interpreted-function-alist)))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
         (defthm ,(pack$ 'true-listp-of-mv-nth-0-of- instantiate-hyp-name)
           (implies (and (pseudo-termp term)
                         (consp term))
                    (true-listp (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist))))
           :flag ,instantiate-hyp-name)
         :skip-others t
         :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (defthm ,(pack$ 'not-equal-of-quote-and-car-of-mv-nth-0-of- instantiate-hyp-name)
         (implies (and ;; free vars remain in the term:
                   (mv-nth 1 (,instantiate-hyp-name term alist interpreted-function-alist))
                   ; (consp term)
                   ; (not (equal 'quote (car term)))
                   )
                  (not (equal 'quote (car (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist))))))
         :hints (("Goal" :expand ((,instantiate-hyp-name term alist interpreted-function-alist)))))

       (defthm ,(pack$ 'all-axe-treep-of-cdr-of-mv-nth-0-of- instantiate-hyp-name)
         (implies (and (pseudo-termp term)
                       (all-dargp (strip-cdrs alist))
                       (consp term) ;guarantees that the result is a consp
                       (not (equal 'quote (car (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist)))))
                       ;; ;; free vars remain in the term:
                       ;; (mv-nth 1 (,instantiate-hyp-name term alist interpreted-function-alist))
                       )
                  (all-axe-treep (cdr (mv-nth 0 (,instantiate-hyp-name term alist interpreted-function-alist)))))
         :hints (("Goal" :use ,(pack$ 'axe-treep-of-mv-nth-0-of- instantiate-hyp-name)
                  :in-theory (disable ,(pack$ 'axe-treep-of-mv-nth-0-of- instantiate-hyp-name)))))
       )))
(defmacro make-instantiation-code-simple (suffix
                                         evaluator-base-name)
  (make-instantiation-code-simple-fn suffix
                                    evaluator-base-name))

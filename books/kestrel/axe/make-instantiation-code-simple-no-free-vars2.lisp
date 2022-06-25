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

;; This book contains a variant of the main tool that skips a check by taking
;; advantage of a stronger guard: that all vars are bound in the alist.

;; This book provides a tool that, given the name of an evaluator, makes a hyp
;; instantiation function that uses it.  This book is for the case where the
;; hyp has no free vars (vars not bound in the alist).

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "bounded-darg-listp")
(include-book "axe-trees")

(defun make-instantiation-code-simple-no-free-vars2-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((instantiate-hyp-no-free-vars-name (pack$ 'instantiate-hyp- suffix '-no-free-vars2))
        (instantiate-hyp-no-free-vars-lst-name (pack$ 'instantiate-hyp- suffix '-no-free-vars-lst2))
        (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args)))
    `(encapsulate ()
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/lists-light/cons" :dir :system))
       (local (include-book "kestrel/alists-light/alistp" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
       (local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

       (local (in-theory (disable alistp symbol-alistp myquotep dargp)))

       ;; TERM is from a hyp of a rule and so is a pseudo-term (quoteps and vars at the leaves).
       ;; ALIST binds vars to dargs (nodenums/ quoteps).
       (mutual-recursion
        ;; Returns the instantiation of TERM with ALIST.
        (defund ,instantiate-hyp-no-free-vars-name (term alist interpreted-function-alist)
          (declare (xargs :guard (and (pseudo-termp term)
                                      (symbol-alistp alist)
                                      (all-dargp (strip-cdrs alist))
                                      (subsetp-equal (free-vars-in-term term) (strip-cars alist))
                                      (interpreted-function-alistp interpreted-function-alist))
                          :verify-guards nil ;done below
                          ))
          (if (variablep term)
              (let ((match (assoc-eq term alist))) ; since all vars are bound, we know this is not nil
                (cdr match))
            (let ((fn (ffn-symb term)))
              (if (eq 'quote fn)
                  term
                ;;a function call (previously, we handled IFs specially but that didn't seem worth it):
                (mv-let (all-quotep args)
                  (,instantiate-hyp-no-free-vars-lst-name (fargs term) alist interpreted-function-alist)
                  (if all-quotep
                      ;; Try to evaluate the ground term:
                      (mv-let (erp res)
                        (,apply-axe-evaluator-to-quoted-args-name fn args interpreted-function-alist)
                        (if erp ;; May be an :unknown-function form
                            (progn$
                             ;; If this message is printed a lot, we could suppress it:
                             ;; (cw "(Note: In instantiate-hyp: Failed to apply ~x0 to constant args.  Consider adding it to the evaluator, adding it to the interpreted-function-alist, or adding a constant-opener rule.)~%" fn)
                             (cons fn args) ;; Return the ground term unevaluated
                             )
                          (enquote res)))
                    ;; Not a ground term:
                    ;; TODO: Consider cons-with-hint here:
                    (cons fn args)))))))

        ;; Returns (mv all-quotep args).
        (defund ,instantiate-hyp-no-free-vars-lst-name (terms alist interpreted-function-alist)
          (declare (xargs :guard (and (pseudo-term-listp terms)
                                      (symbol-alistp alist)
                                      (all-dargp (strip-cdrs alist))
                                      (subsetp-equal (free-vars-in-terms terms) (strip-cars alist))
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (endp terms)
              (mv t nil)
            (let ((instantiated-first (,instantiate-hyp-no-free-vars-name (first terms) alist interpreted-function-alist)))
              (mv-let (rest-all-quotep instantiated-rest)
                (,instantiate-hyp-no-free-vars-lst-name (rest terms) alist interpreted-function-alist)
                (mv (and rest-all-quotep (quotep instantiated-first))
                    (cons instantiated-first instantiated-rest) ;todo: consider cons-with-hint here
                    ))))))

       (make-flag ,instantiate-hyp-no-free-vars-name)

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- instantiate-hyp-no-free-vars-lst-name)
          (true-listp (mv-nth 1 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist)))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'len-of-mv-nth-1-of- instantiate-hyp-no-free-vars-lst-name)
          (equal (len (mv-nth 1 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist)))
                 (len terms))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'booleanp-of-mv-nth-0-of- instantiate-hyp-no-free-vars-lst-name)
          (booleanp (mv-nth 0 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist)))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'axe-treep-of- instantiate-hyp-no-free-vars-name)
          (implies (and (pseudo-termp term)
                        (subsetp-equal (free-vars-in-term term) (strip-cars alist))
                        (all-dargp (strip-cdrs alist))
                        (alistp alist))
                   (axe-treep (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))
          :flag ,instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'axe-tree-listp-of-mv-nth-1-of- instantiate-hyp-no-free-vars-lst-name)
          (implies (and (pseudo-term-listp terms)
                        (subsetp-equal (free-vars-in-terms terms) (strip-cars alist))
                        (all-dargp (strip-cdrs alist))
                        (alistp alist))
                   (axe-tree-listp (mv-nth 1 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist))))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name
                                           ,instantiate-hyp-no-free-vars-lst-name
                                           assoc-equal-iff))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-no-free-vars-name)
          (implies (and (pseudo-termp term)
                        (bounded-darg-listp (strip-cdrs alist) dag-len))
                   (bounded-axe-treep (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)
                                      dag-len))
          :flag ,instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'bounded-axe-tree-listp-of-mv-nth-1-of- instantiate-hyp-no-free-vars-lst-name)
          (implies (and (pseudo-term-listp terms)
                        (bounded-darg-listp (strip-cdrs alist) dag-len))
                   (bounded-axe-tree-listp (mv-nth 1 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist))
                                          dag-len))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- instantiate-hyp-no-free-vars-lst-name)
          (implies (and (mv-nth 0 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist))
                        (pseudo-term-listp terms)
                        (subsetp-equal (free-vars-in-terms terms) (strip-cars alist))
                        (all-dargp (strip-cdrs alist))
                        (alistp alist))
                   (all-myquotep (mv-nth 1 (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist))))
          :flag ,instantiate-hyp-no-free-vars-lst-name)
        :skip-others t
        :hints (("Goal" :expand (,instantiate-hyp-no-free-vars-lst-name terms alist interpreted-function-alist)
                 :in-theory (e/d (,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name) (myquotep)))))

       (verify-guards ,instantiate-hyp-no-free-vars-name :hints (("Goal" :expand (free-vars-in-term term)
                                                     :in-theory (enable pseudo-termp)
                                                     :do-not-induct t)))

       (defthm ,(pack$ 'consp-of- instantiate-hyp-no-free-vars-name)
         (implies (consp term)
                  (consp (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))
         :hints (("Goal" :expand ((,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))))

       (,(pack$ 'defthm-flag- instantiate-hyp-no-free-vars-name)
        (defthm ,(pack$ 'true-listp-of- instantiate-hyp-no-free-vars-name)
          (implies (and (pseudo-termp term)
                        (consp term))
                   (true-listp (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))
          :flag ,instantiate-hyp-no-free-vars-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-no-free-vars-name ,instantiate-hyp-no-free-vars-lst-name))))

       ;; (defthm ,(pack$ 'not-equal-of-quote-and-car-of- instantiate-hyp-no-free-vars-name)
       ;;   (implies (and ;; free vars remain in the term:
       ;;             ;(mv-nth 1 (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist))
       ;;             ; (consp term)
       ;;             ; (not (equal 'quote (car term)))
       ;;             )
       ;;            (not (equal 'quote (car (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))))
       ;;   :hints (("Goal" :expand ((,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist)))))

       (defthm ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-no-free-vars-name)
         (implies (and (pseudo-termp term)
                       (subsetp-equal (free-vars-in-term term) (strip-cars alist))
                       (alistp alist)
                       (all-dargp (strip-cdrs alist))
                       (consp term) ;guarantees that the result is a consp
                       (not (equal 'quote (car (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist))))
                       ;; ;; free vars remain in the term:
                       ;; (mv-nth 1 (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist))
                       )
                  (axe-tree-listp (cdr (,instantiate-hyp-no-free-vars-name term alist interpreted-function-alist))))
         :hints (("Goal" :use ,(pack$ 'axe-treep-of- instantiate-hyp-no-free-vars-name)
                  :in-theory (disable ,(pack$ 'axe-treep-of- instantiate-hyp-no-free-vars-name))))))))

(defmacro make-instantiation-code-simple-no-free-vars2 (suffix
                                                       evaluator-base-name)
  (make-instantiation-code-simple-no-free-vars2-fn suffix
                                                  evaluator-base-name))

; A tool to generate hyp instantiation code that calls a given evaluator
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

;; This book provides a tool that, given the name of an evaluator, makes a hyp
;; instantiation function that uses it.  This book is for the case where the
;; hyp has free vars (vars not bound in the alist).

(include-book "kestrel/alists-light/maybe-replace-var" :dir :system)
(include-book "bounded-darg-listp")
(include-book "axe-tree-vars")
(include-book "alist-suitable-for-hypsp")
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

;dup, needed for the proofs?
(defthmd assoc-equal-iff-member-equal-of-strip-cars
  (implies (or (alistp alist)
               key)
           (iff (assoc-equal key alist)
                (member-equal key (strip-cars alist))))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defun make-instantiation-code-simple-free-vars-fn (suffix evaluator-base-name)
  (declare (xargs :guard (and (symbolp suffix)
                              (symbolp evaluator-base-name))))
  (let ((instantiate-hyp-name (pack$ 'instantiate-hyp- suffix '-free-vars))
        (instantiate-hyp-lst-name (pack$ 'instantiate-hyp- suffix '-free-vars-lst))
        (apply-axe-evaluator-to-quoted-args-name (pack$ 'apply- evaluator-base-name '-to-quoted-args)))
    `(encapsulate ()
       (local (include-book "kestrel/lists-light/len" :dir :system))
       (local (include-book "kestrel/lists-light/cons" :dir :system))
       (local (include-book "kestrel/lists-light/list-sets" :dir :system))
       (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
       (local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

       ;; TERM is from a hyp of a rule and so is a pseudo-term (quoteps and vars at the leaves).
       ;; ALIST binds vars to dargs (nodenums/ quoteps).
       (mutual-recursion
        ;; Returns the instantiation of TERM with ALIST.
        (defund ,instantiate-hyp-name (term alist interpreted-function-alist)
          (declare (xargs :verify-guards nil ;done below
                          :guard (and (pseudo-termp term)
                                      (symbol-alistp alist)
                                      (darg-listp (strip-cdrs alist))
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (variablep term) ;todo: we could mark the var as free or not free
              (let ((match (assoc-eq term alist)))
                (if match
                    (cdr match) ;the var has a binding in the alist
                  term          ;no match for the var, so it is free
                  ))
            (let ((fn (ffn-symb term)))
              (if (eq 'quote fn)
                  term
                ;;a function call (previously, we handled IFs specially but that didn't seem worth it):
                (mv-let (all-quotep args)
                  (,instantiate-hyp-lst-name (fargs term) alist interpreted-function-alist)
                  ;; todo: consider not doing this for this function, which deals with free vars!
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
        (defund ,instantiate-hyp-lst-name (terms alist interpreted-function-alist)
          (declare (xargs :guard (and (pseudo-term-listp terms)
                                      (symbol-alistp alist)
                                      (darg-listp (strip-cdrs alist))
                                      (interpreted-function-alistp interpreted-function-alist))))
          (if (endp terms)
              (mv t nil)
            (let ((instantiated-first (,instantiate-hyp-name (first terms) alist interpreted-function-alist)))
              (mv-let (rest-all-quotep instantiated-rest)
                (,instantiate-hyp-lst-name (rest terms) alist interpreted-function-alist)
                (mv (and rest-all-quotep (quotep instantiated-first))
                    (cons instantiated-first instantiated-rest) ;todo: consider cons-with-hint here
                    ))))))

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
        (defthm ,(pack$ 'booleanp-of-mv-nth-0-of- instantiate-hyp-lst-name)
          (booleanp (mv-nth 0 (,instantiate-hyp-lst-name terms alist interpreted-function-alist)))
          :flag ,instantiate-hyp-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'axe-treep-of- instantiate-hyp-name)
          (implies (and (pseudo-termp term)
                        (darg-listp (strip-cdrs alist)))
                   (axe-treep (,instantiate-hyp-name term alist interpreted-function-alist)))
          :flag ,instantiate-hyp-name)
        (defthm ,(pack$ 'axe-tree-listp-of-mv-nth-1-of- instantiate-hyp-lst-name)
          (implies (and (pseudo-term-listp terms)
                        (darg-listp (strip-cdrs alist)))
                   (axe-tree-listp (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))))
          :flag ,instantiate-hyp-lst-name)
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'bounded-axe-treep-of- instantiate-hyp-name)
          (implies (and (pseudo-termp term)
                        (bounded-darg-listp (strip-cdrs alist) dag-len))
                   (bounded-axe-treep (,instantiate-hyp-name term alist interpreted-function-alist)
                                      dag-len))
          :flag ,instantiate-hyp-name)
        (defthm ,(pack$ 'bounded-axe-tree-listp-of-mv-nth-1-of- instantiate-hyp-lst-name)
          (implies (and (pseudo-term-listp terms)
                        (bounded-darg-listp (strip-cdrs alist) dag-len))
                   (bounded-axe-tree-listp (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))
                                          dag-len))
          :flag ,instantiate-hyp-lst-name)
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'all-myquotep-of-mv-nth-1-of- instantiate-hyp-lst-name)
          (implies (and (mv-nth 0 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))
                        (pseudo-term-listp terms)
                        (darg-listp (strip-cdrs alist)))
                   (all-myquotep (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))))
          :flag ,instantiate-hyp-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (e/d (,instantiate-hyp-name ,instantiate-hyp-lst-name myquotep-when-axe-treep)
                                        (myquotep)))))

       (verify-guards ,instantiate-hyp-name :hints (("Goal" :in-theory (enable pseudo-termp))))

       (defthm ,(pack$ 'consp-of- instantiate-hyp-name)
         (implies (consp term)
                  (consp (,instantiate-hyp-name term alist interpreted-function-alist)))
         :hints (("Goal" :expand ((,instantiate-hyp-name term alist interpreted-function-alist)))))

       ;; hyps match exactly what we know when this is used
       ;; todo: disable?
       (defthm ,(pack$ 'symbol-of-car-of- instantiate-hyp-name)
         (implies (and (pseudo-termp term)
                       (lambda-free-termp term)
                       (consp term))
                  (symbolp (car (,instantiate-hyp-name term alist interpreted-function-alist))))
         :hints (("Goal" :expand ((,instantiate-hyp-name term alist interpreted-function-alist)))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'true-listp-of- instantiate-hyp-name)
          (implies (and (pseudo-termp term)
                        (consp term))
                   (true-listp (,instantiate-hyp-name term alist interpreted-function-alist)))
          :flag ,instantiate-hyp-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name))))

       ;; (defthm ,(pack$ 'not-equal-of-quote-and-car-of- instantiate-hyp-name)
       ;;   (implies (and ;; free vars remain in the term:
       ;;             ;(mv-nth 1 (,instantiate-hyp-name term alist interpreted-function-alist))
       ;;             ; (consp term)
       ;;             ; (not (equal 'quote (car term)))
       ;;             )
       ;;            (not (equal 'quote (car (,instantiate-hyp-name term alist interpreted-function-alist)))))
       ;;   :hints (("Goal" :expand ((,instantiate-hyp-name term alist interpreted-function-alist)))))

       (defthm ,(pack$ 'axe-tree-listp-of-cdr-of- instantiate-hyp-name)
         (implies (and (pseudo-termp term)
                       (darg-listp (strip-cdrs alist))
                       (consp term) ;guarantees that the result is a consp
                       (not (equal 'quote (car (,instantiate-hyp-name term alist interpreted-function-alist))))
                       ;; ;; free vars remain in the term:
                       ;; (mv-nth 1 (,instantiate-hyp-name term alist interpreted-function-alist))
                       )
                  (axe-tree-listp (cdr (,instantiate-hyp-name term alist interpreted-function-alist))))
         :hints (("Goal" :use ,(pack$ 'axe-treep-of- instantiate-hyp-name)
                  :in-theory (disable ,(pack$ 'axe-treep-of- instantiate-hyp-name)))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'mv-nth-0-of- instantiate-hyp-lst-name)
          (iff (mv-nth 0 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))
               (all-quotep (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist))))
          :flag ,instantiate-hyp-lst-name)
        :skip-others t
        :hints (("Goal" :in-theory (enable ,instantiate-hyp-name ,instantiate-hyp-lst-name
                                           all-quotep))))

       (,(pack$ 'defthm-flag- instantiate-hyp-name)
        (defthm ,(pack$ 'axe-tree-vars-of- instantiate-hyp-name)
          (implies (and (pseudo-termp term)
                        (darg-listp (strip-cdrs alist))
                        (alistp alist))
                   (equal (axe-tree-vars (,instantiate-hyp-name term alist interpreted-function-alist))
                          (set-difference-equal (free-vars-in-term term)
                                                (strip-cars alist))))
          :flag ,instantiate-hyp-name)
        (defthm ,(pack$ 'axe-tree-vars-lst-of-mv-nth-1-of- instantiate-hyp-lst-name)
          (implies (and (pseudo-term-listp terms)
                        (darg-listp (strip-cdrs alist))
                        (alistp alist))
                   (equal (axe-tree-vars-lst (mv-nth 1 (,instantiate-hyp-lst-name terms alist interpreted-function-alist)))
                          (set-difference-equal (free-vars-in-terms terms)
                                                (strip-cars alist))))
          :flag ,instantiate-hyp-lst-name)
        :hints (("Goal" :expand ((free-vars-in-terms terms))
                 :in-theory (enable ,instantiate-hyp-name
                                           ,instantiate-hyp-lst-name
                                           assoc-equal-iff-member-equal-of-strip-cars
                                           axe-tree-vars))))

       ;; ;; All the vars in the alist get replaced when we instantiate
       ;; (defthm ,(pack$ 'not-intersection-equal-of-strip-cars-and-axe-tree-vars-of- instantiate-hyp-name)
       ;;   (implies (and (darg-listp (strip-cdrs alist))
       ;;                 (symbol-alistp alist)
       ;;                 (pseudo-termp term))
       ;;            (not (intersection-equal (strip-cars alist)
       ;;                              (axe-tree-vars (,instantiate-hyp-name term alist interpreted-function-alist)))))
       ;;   :hints (("Goal" :in-theory (enable axe-tree-vars))))

       (defthm ,(pack$ 'axe-tree-vars-lst-of-cdr-of- instantiate-hyp-name)
         (implies (and (consp (,instantiate-hyp-name TERM ALIST INTERPRETED-FUNCTION-ALIST))
                       (not (equal 'quote (car (,instantiate-hyp-name term alist interpreted-function-alist))))
                       (darg-listp (strip-cdrs alist))
                       (symbol-alistp alist)
                       (pseudo-termp term))
                  (equal (axe-tree-vars-lst (cdr (,instantiate-hyp-name term alist interpreted-function-alist)))
                         (set-difference-equal (free-vars-in-term term)
                                               (strip-cars alist))))
         :hints (("Goal" :use (:instance ,(pack$ 'axe-tree-vars-of- instantiate-hyp-name))
                  :in-theory (e/d (axe-tree-vars)
                                  ( ,(pack$ 'axe-tree-vars-of- instantiate-hyp-name))))))

       (defthm ,(pack$ 'alist-suitable-for-hyp-args-and-hypsp-after- instantiate-hyp-name)
         (implies (and (alist-suitable-for-hypsp alist hyps)
                       (bounded-darg-listp (strip-cdrs alist) dag-len)
                       (symbol-alistp alist)
                       (equal :free-vars (car (car hyps)))
                       (consp (cdr (car hyps)))
                       (not (equal 'quote (cadr (car hyps))))
                       (pseudo-termp (cdr (car hyps)))
                       (lambda-free-termp (cdr (car hyps)))
                       (axe-rule-hyp-listp (cdr hyps))
                       ;; (consp hyps)
                       (not (equal 'quote (car (,instantiate-hyp-name (cdr (car hyps)) alist interpreted-function-alist)))))
                  (alist-suitable-for-hyp-args-and-hypsp alist
                                                         (cdr (,instantiate-hyp-name (cdr (car hyps)) alist interpreted-function-alist))
                                                         (cdr hyps)))
         :hints (("Goal" :expand (bound-vars-suitable-for-hypsp (strip-cars alist)
                                                                hyps)
                  :in-theory (enable alist-suitable-for-hyp-args-and-hypsp
                                     alist-suitable-for-hypsp
                                     bound-vars-suitable-for-hypsp
                                     bound-vars-suitable-for-hypp
                                     bound-vars-after-hyp))))


       )))

(defmacro make-instantiation-code-simple-free-vars (suffix
                                                    evaluator-base-name)
  (make-instantiation-code-simple-free-vars-fn suffix
                                               evaluator-base-name))

; A tool to apply a substitution to terms and evaluate function calls as it goes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also sublis-var-and-eval-basic.lisp.

(include-book "evaluator") ;; Brings in skip-proofs
(include-book "dag-arrays")
(include-book "axe-trees")
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable member-equal symbol-listp pseudo-termp axe-treep)))

;dup
;; (defthmd bounded-axe-treep-when-dargp-less-than
;;   (implies (dargp-less-than tree bound)
;;            (bounded-axe-treep tree bound))
;;   :hints (("Goal" :in-theory (enable bounded-axe-treep dargp-less-than))))

;; ;dup
;; (defthm axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
;;   (implies (and (all-dargp (strip-cdrs alist))
;;                 ;; (assoc-equal form alist)
;;                 )
;;            (axe-treep (cdr (assoc-equal form alist))))
;;   :hints (("Goal" :in-theory (enable all-dargp assoc-equal))))

;this one evaluates applications of known functions on constant arguments
;todo: try cons-with-hint here?
;; This handles lambda applications correctly (by handling their args) but does not beta reduce.
(mutual-recursion
 (defund sublis-var-and-eval (alist ;maps vars to nodenums/quoteps
                                 form interpreted-function-alist)
   (declare (xargs :verify-guards nil ;done below
                   :guard (and (symbol-alistp alist)
                               (all-dargp (strip-cdrs alist))
                               (pseudo-termp form)
                               (interpreted-function-alistp interpreted-function-alist))))
   (cond ((variablep form)
          (let ((a (assoc-eq form alist)))
            (cond (a (cdr a))
                  (t form) ;TODO: can we drop this case and the check above for some uses of this function (e.g., no free vars in a rule RHS or lambda body)
                  )))
         ((fquotep form) form)
         (t (let ((fn (ffn-symb form)))
              (if (and (eq fn 'if) ;bozo, consider also handling bvif, boolif, myif, maybe boolor and booland...
                       (= 3 (len (fargs form))))
                  (let* ((test (second form))
                         (test-result (sublis-var-and-eval alist test interpreted-function-alist)))
                    (if (quotep test-result)
                        (sublis-var-and-eval alist (if (unquote test-result) ;if the test is not nil
                                                          (third form) ;then part
                                                        (fourth form) ;else part
                                                        )
                                                interpreted-function-alist)
                      ;;couldn't resolve if-test:
                      (list 'if
                            test-result
                            (sublis-var-and-eval alist (third form) interpreted-function-alist) ;then part
                            (sublis-var-and-eval alist (fourth form) interpreted-function-alist) ;else part
                            )))
                ;;regular function call or lambda
                (mv-let (ground-termp args)
                  (sublis-var-and-eval-lst alist (fargs form) interpreted-function-alist)
                  (if (and ground-termp
                           (symbolp fn) ;todo: drop
                           (or ;; (consp fn) ; we evaluate ground lambda applications ;; TODO: Would like to put this in but unsupported functions in the lambda body can cause problems
                               (member-eq fn *axe-evaluator-functions*) ;switched these..
                               (assoc-eq fn interpreted-function-alist) ;ffffffixme
                               )
                           ;; (not (eq fn 'repeat))     ;Wed Feb 16 22:21:47 2011
                           (not (eq 'th fn)))        ;fffixme gross!
                      ;;ffixme, call something different here depending on whether it's an ifn (could get the body of the ifn by doing an assoc-eq above):
                      (enquote (apply-axe-evaluator-to-quoted-args fn args interpreted-function-alist 0))
                    ;; (let ((possible-val (eval-fn-if-possible fn (unquote-list args))))
                    ;; (if possible-val ;possible-val is quoted (or is nil if we can't eval the fn)
                    ;; possible-val
                    ;; (cons fn args)))
                    (cons fn args))))))))

 ;;returns (mv ground-termp args)
 (defund sublis-var-and-eval-lst (alist l interpreted-function-alist)
   (declare (xargs
             :verify-guards nil
             :guard (and (symbol-alistp alist)
                         (all-dargp (strip-cdrs alist)) ;gen?  really just need that things whose cars are 'quote are myquoteps
                         (pseudo-term-listp l)
                         (interpreted-function-alistp interpreted-function-alist))))
   (if (atom l)
       (mv t nil)
     (let ((new-car (sublis-var-and-eval alist (car l) interpreted-function-alist)))
       (mv-let (cdr-ground-termp new-cdr)
         (sublis-var-and-eval-lst alist (cdr l) interpreted-function-alist)
         (mv (and cdr-ground-termp (quotep new-car))
             (cons new-car new-cdr)))))))

(make-flag sublis-var-and-eval)

(defthm len-of-mv-nth-1-of-sublis-var-and-eval-lst
  (equal (len (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist)))
         (len l))
  :hints (("Goal" :induct (len l) :in-theory (enable sublis-var-and-eval-lst (:i len)))))

(defthm true-listp-of-mv-nth-1-of-sublis-var-and-eval-lst
  (true-listp (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist)))
  :hints (("Goal" :induct (len l) :in-theory (enable sublis-var-and-eval-lst (:i len)))))

;; maybe we should prove that it returns an axe-tree...
;; (defthm-flag-sublis-var-and-eval
;;   (defthm pseudo-termp-of-sublis-var-and-eval
;;     (implies (and (pseudo-termp form)
;;                   (symbol-alistp alist)
;;                   ;(pseudo-term-listp (strip-cdrs alist))
;;                   (alistp interpreted-function-alist))
;;              (pseudo-termp (sublis-var-and-eval alist form interpreted-function-alist)))
;;     :flag sublis-var-and-eval)
;;   (defthm pseudo-term-listp-of-sublis-var-and-eval-lst
;;     (implies (and (pseudo-term-listp l)
;;                   (symbol-alistp alist)
;;                   ;(pseudo-term-listp (strip-cdrs alist))
;;                   (alistp interpreted-function-alist))
;;              (pseudo-term-listp (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist))))
;;     :flag sublis-var-and-eval-lst)
;;   :hints (("Goal" :in-theory (disable list::memberp-of-cons))))

(defthm-flag-sublis-var-and-eval
  (defthm myquotep-of-sublis-var-and-eval
    (implies (and (eq 'quote (car (sublis-var-and-eval alist form interpreted-function-alist)))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-termp form)
                  )
             (myquotep (sublis-var-and-eval alist form interpreted-function-alist)))
    :flag sublis-var-and-eval)
  (defthm all-myquotep-of-mv-nth-1-of-sublis-var-and-eval-lst
    (implies (and (mv-nth 0 (sublis-var-and-eval-lst alist l interpreted-function-alist))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-term-listp l))
             (all-myquotep (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist))))
    :flag sublis-var-and-eval-lst)
  :hints (("Goal" :in-theory (e/d (sublis-var-and-eval sublis-var-and-eval-lst)
                                  (myquotep)))))

(verify-guards sublis-var-and-eval
  :hints (("Goal"
           :use (:instance myquotep-of-sublis-var-and-eval
                           (form (CADR FORM)))
           :in-theory (e/d ()
                           (;list::memberp-of-cons
                            myquotep SYMBOL-ALISTP STRIP-CDRS myquotep-of-sublis-var-and-eval)))))

(defthm-flag-sublis-var-and-eval
  (defthm axe-treep-of-sublis-var-and-eval
    (implies (and ;(eq 'quote (car (sublis-var-and-eval alist form interpreted-function-alist)))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-termp form)
                  )
             (axe-treep (sublis-var-and-eval alist form interpreted-function-alist)))
    :flag sublis-var-and-eval)
  (defthm all-axe-treep-of-mv-nth-1-of-sublis-var-and-eval-lst
    (implies (and ;(mv-nth 0 (sublis-var-and-eval-lst alist l interpreted-function-alist))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-term-listp l))
             (all-axe-treep (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist))))
    :flag sublis-var-and-eval-lst)
  :hints (("Goal" :in-theory (e/d (axe-treep sublis-var-and-eval sublis-var-and-eval-lst)
                                  (myquotep MYQUOTEP-OF-SUBLIS-VAR-AND-EVAL)))))

(defthm-flag-sublis-var-and-eval
  (defthm bounded-axe-treep-of-sublis-var-and-eval
    (implies (and ;(eq 'quote (car (sublis-var-and-eval alist form interpreted-function-alist)))
                  (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-termp form)
                  )
             (bounded-axe-treep (sublis-var-and-eval alist form interpreted-function-alist) dag-len))
    :flag sublis-var-and-eval)
  (defthm all-bounded-axe-treep-of-mv-nth-1-of-sublis-var-and-eval-lst
    (implies (and ;(mv-nth 0 (sublis-var-and-eval-lst alist l interpreted-function-alist))
                  (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-term-listp l))
             (all-bounded-axe-treep (mv-nth 1 (sublis-var-and-eval-lst alist l interpreted-function-alist)) dag-len))
    :flag sublis-var-and-eval-lst)
  :hints (("Goal" :in-theory (e/d (sublis-var-and-eval
                                   sublis-var-and-eval-lst
                                   bounded-axe-treep-when-dargp-less-than
                                   ;bounded-axe-treep-when-natp
                                   ;bounded-axe-treep-when-not-consp
                                   )
                                  (myquotep MYQUOTEP-OF-SUBLIS-VAR-AND-EVAL
                                            BOUNDED-AXE-TREEP
                                            natp
                                            )))))

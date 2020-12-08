; A variant of my-sublis-var-and-eval that uses the basic evaluator.
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

;; Similar to instantiate-hyp-basic?

(include-book "dags")
(include-book "evaluator-basic")
(include-book "axe-trees")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

;move
(defthmd bounded-axe-treep-when-dargp-less-than
  (implies (dargp-less-than tree bound)
           (bounded-axe-treep tree bound))
  :hints (("Goal" :in-theory (enable bounded-axe-treep dargp-less-than))))

;(local (in-theory (disable memberp-of-cons)))

;; some of these are bad rules that come in via deflist:
;; (local (in-theory (disable member-of-cons ;todo
;;                            subsetp-car-member
;;                            subsetp-cons-2 ;also bad?
;;                            all-consp-when-not-consp
;;                            use-all-consp-for-car)))ee

(defthm axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (all-dargp (strip-cdrs alist))
                (assoc-equal form alist))
           (axe-treep (cdr (assoc-equal form alist))))
  :hints (("Goal" :use (:instance dargp-of-cdr-of-assoc-equal (var form))
           :in-theory (disable dargp-of-cdr-of-assoc-equal))))

;this one evaluates applications of known functions on constant arguments
;todo: try cons-with-hint here?
;; This handles lambda applications correctly (by handling their args) but does not beta reduce.
(mutual-recursion
 ;; Returns a new term.
 (defund my-sublis-var-and-eval-basic (alist ;maps vars to nodenums/quoteps
                                       term interpreted-function-alist)
   (declare (xargs :verify-guards nil ;done below
                   :guard (and (symbol-alistp alist)
                               (all-dargp (strip-cdrs alist))
                               (pseudo-termp term)
                               (interpreted-function-alistp interpreted-function-alist))))
   (cond ((variablep term)
          (let ((a (assoc-eq term alist)))
            (cond (a (cdr a))
                  (t term) ;TODO: can we drop this case and the check above for some uses of this function (e.g., no free vars in a rule RHS or lambda body)
                  )))
         ((fquotep term) term)
         (t (let ((fn (ffn-symb term)))
              (if (and (eq fn 'if) ;bozo, consider also handling bvif, boolif, myif, maybe boolor and booland...
                       (= 3 (len (fargs term))))
                  (let* ((test (second term))
                         (test-result (my-sublis-var-and-eval-basic alist test interpreted-function-alist)))
                    (if (quotep test-result)
                        (my-sublis-var-and-eval-basic alist (if (unquote test-result) ;if the test is not nil
                                                                (third term) ;then part
                                                              (fourth term) ;else part
                                                              )
                                                      interpreted-function-alist)
                      ;;couldn't resolve if-test:
                      (list 'if
                            test-result
                            (my-sublis-var-and-eval-basic alist (third term) interpreted-function-alist) ;then part
                            (my-sublis-var-and-eval-basic alist (fourth term) interpreted-function-alist) ;else part
                            )))
                ;;regular function call or lambda
                (mv-let (ground-termp args)
                  (my-sublis-var-and-eval-basic-lst alist (fargs term) interpreted-function-alist)
                  (if ground-termp
                      ;;ffixme, call something different here depending on whether it's an ifn (could get the body of the ifn by doing an assoc-eq above):
                      (mv-let (erp res)
                        (apply-axe-evaluator-basic-to-quoted-args fn args interpreted-function-alist)
                        (if erp
                            (progn$ ;; This failure can be due to a sub-function not being in the interpreted-function-alist
                             (cw "Failed to apply ~x0 to constant args.~%" fn) ;; Shows messages about ground calls that we cannot evaluate
                             ;; (cw "sub: Failed to apply ~x0 to constant args (er:~x1,ifns:~x2).~%" fn erp (strip-cars interpreted-function-alist) ;(len interpreted-function-alist))
                             (cons fn args))
                          (enquote res)))
                    ;; (let ((possible-val (eval-fn-if-possible fn (unquote-list args))))
                    ;; (if possible-val ;possible-val is quoted (or is nil if we can't eval the fn)
                    ;; possible-val
                    ;; (cons fn args)))
                    (cons fn args))))))))

 ;; Returns (mv ground-termp args).
 (defund my-sublis-var-and-eval-basic-lst (alist terms interpreted-function-alist)
   (declare (xargs
             :verify-guards nil
             :guard (and (symbol-alistp alist)
                         (all-dargp (strip-cdrs alist)) ;gen?  really just need that things whose cars are 'quote are myquoteps
                         (pseudo-term-listp terms)
                         (interpreted-function-alistp interpreted-function-alist))))
   (if (atom terms)
       (mv t nil)
     (let ((new-car (my-sublis-var-and-eval-basic alist (first terms) interpreted-function-alist)))
       (mv-let (cdr-ground-termp new-cdr)
         (my-sublis-var-and-eval-basic-lst alist (rest terms) interpreted-function-alist)
         (mv (and cdr-ground-termp (quotep new-car))
             (cons new-car new-cdr)))))))

(make-flag my-sublis-var-and-eval-basic)

(defthm len-of-mv-nth-1-of-my-sublis-var-and-eval-basic-lst
  (equal (len (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist)))
         (len terms))
  :hints (("Goal" :induct (len terms) :in-theory (enable my-sublis-var-and-eval-basic-lst (:i len)))))

(defthm true-listp-of-mv-nth-1-of-my-sublis-var-and-eval-basic-lst
  (true-listp (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist)))
  :hints (("Goal" :induct (len terms) :in-theory (enable my-sublis-var-and-eval-basic-lst (:i len)))))

;; maybe we should prove that it returns an axe-tree...
;; (defthm-flag-my-sublis-var-and-eval-basic
;;   (defthm pseudo-termp-of-my-sublis-var-and-eval-basic
;;     (implies (and (pseudo-termp term)
;;                   (symbol-alistp alist)
;;                   ;(pseudo-term-listp (strip-cdrs alist))
;;                   (alistp interpreted-function-alist))
;;              (pseudo-termp (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
;;     :flag my-sublis-var-and-eval-basic)
;;   (defthm pseudo-term-listp-of-my-sublis-var-and-eval-basic-lst
;;     (implies (and (pseudo-term-listp terms)
;;                   (symbol-alistp alist)
;;                   ;(pseudo-term-listp (strip-cdrs alist))
;;                   (alistp interpreted-function-alist))
;;              (pseudo-term-listp (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))))
;;     :flag my-sublis-var-and-eval-basic-lst)
;;   :hints (("Goal" :in-theory (disable list::memberp-of-cons))))

(defthm-flag-my-sublis-var-and-eval-basic
  (defthm myquotep-of-my-sublis-var-and-eval-basic
    (implies (and (eq 'quote (car (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-termp term)
                  )
             (myquotep (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
    :flag my-sublis-var-and-eval-basic)
  (defthm all-myquotep-of-mv-nth-1-of-my-sublis-var-and-eval-basic-lst
    (implies (and (mv-nth 0 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-term-listp terms))
             (all-myquotep (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))))
    :flag my-sublis-var-and-eval-basic-lst)
  :hints (("Goal" :in-theory (e/d (my-sublis-var-and-eval-basic my-sublis-var-and-eval-basic-lst)
                                  (myquotep)))))

(verify-guards my-sublis-var-and-eval-basic
  :hints (("Goal"
           :use (:instance myquotep-of-my-sublis-var-and-eval-basic
                           (term (CADR TERM)))
           :in-theory (e/d ()
                           (myquotep SYMBOL-ALISTP STRIP-CDRS myquotep-of-my-sublis-var-and-eval-basic)))))

(defthm-flag-my-sublis-var-and-eval-basic
  (defthm axe-treep-of-my-sublis-var-and-eval-basic
    (implies (and ;(eq 'quote (car (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-termp term)
                  )
             (axe-treep (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
    :flag my-sublis-var-and-eval-basic)
  (defthm all-axe-treep-of-mv-nth-1-of-my-sublis-var-and-eval-basic-lst
    (implies (and ;(mv-nth 0 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))
                  (all-dargp (strip-cdrs alist))
                  (pseudo-term-listp terms))
             (all-axe-treep (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))))
    :flag my-sublis-var-and-eval-basic-lst)
  :hints (("Goal" :in-theory (e/d (my-sublis-var-and-eval-basic my-sublis-var-and-eval-basic-lst)
                                  (myquotep MYQUOTEP-OF-MY-SUBLIS-VAR-AND-EVAL-BASIC)))))

(defthm-flag-my-sublis-var-and-eval-basic
  (defthm bounded-axe-treep-of-my-sublis-var-and-eval-basic
    (implies (and ;(eq 'quote (car (my-sublis-var-and-eval-basic alist term interpreted-function-alist)))
                  (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-termp term)
                  )
             (bounded-axe-treep (my-sublis-var-and-eval-basic alist term interpreted-function-alist) dag-len))
    :flag my-sublis-var-and-eval-basic)
  (defthm all-bounded-axe-treep-of-mv-nth-1-of-my-sublis-var-and-eval-basic-lst
    (implies (and ;(mv-nth 0 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist))
                  (all-dargp-less-than (strip-cdrs alist) dag-len)
                  (pseudo-term-listp terms))
             (all-bounded-axe-treep (mv-nth 1 (my-sublis-var-and-eval-basic-lst alist terms interpreted-function-alist)) dag-len))
    :flag my-sublis-var-and-eval-basic-lst)
  :hints (("Goal" :in-theory (e/d (my-sublis-var-and-eval-basic
                                   my-sublis-var-and-eval-basic-lst
                                   bounded-axe-treep-when-dargp-less-than
                                   ;bounded-axe-treep-when-natp
                                   ;bounded-axe-treep-when-not-consp
                                   )
                                  (myquotep MYQUOTEP-OF-MY-SUBLIS-VAR-AND-EVAL-BASIC
                                            BOUNDED-AXE-TREEP
                                            natp
                                            )))))

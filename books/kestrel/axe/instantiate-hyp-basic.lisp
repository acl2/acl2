; A variant of instantiate-hyp that uses the basic evaluator.
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

;; Similar to my-sublis-var-and-eval-basic, but this one also has a free-vars flag.

;; This tool uses the basic evaluator.  TODO: Create a tool to generate
;; variants of this tool, each for a given evaluator.

(include-book "dags")
(include-book "evaluator-basic")
(include-book "axe-trees")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))

;(local (in-theory (disable memberp-of-cons)))

;; some of these are bad rules that come in via deflist:
;; (local (in-theory (disable member-of-cons ;todo
;;                            subsetp-car-member
;;                            subsetp-cons-2 ;also bad?
;;                            all-consp-when-not-consp
;;                            use-all-consp-for-car)))ee

;; ;move
;; (defthm pseudo-lambdap-of-car
;;   (implies (pseudo-termp form)
;;            (equal (pseudo-lambdap (car form))
;;                   (not (symbolp (car form)))))
;;   :hints (("Goal" :expand ((pseudo-termp form))
;;            :in-theory (enable pseudo-termp pseudo-lambdap))))

;dup
(defthm axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (all-dargp (strip-cdrs alist))
                (assoc-equal form alist))
           (axe-treep (cdr (assoc-equal form alist))))
  :hints (("Goal" :use (:instance dargp-of-cdr-of-assoc-equal (var form))
           :in-theory (disable dargp-of-cdr-of-assoc-equal))))

(defthm bounded-axe-treep-when-dargp-less-than-cheap
  (implies (dargp-less-than item bound)
           (bounded-axe-treep item bound))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bounded-axe-treep dargp-less-than))))

(defthm bounded-axe-treep-of-cdr-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (all-dargp-less-than (strip-cdrs alist) dag-len)
                (assoc-equal form alist))
           (bounded-axe-treep (cdr (assoc-equal form alist)) dag-len))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

;;;
;;; instantiate-hyp-basic
;;;

;TERM is from a hyp of a rule and so has quoteps and vars at the leaves.
;ALIST binds vars to quoteps and/or nodenums
;this one does *not* wrap remaining free vars in :free
;; Returns (mv instantiated-hyp free-vars-flg).
(mutual-recursion
 ;; Returns (mv term free-vars-flg) where TERM has been instantiated with ALIST and FREE-VARS-FLG indicates whether any variables remain in TERM.
 (defund instantiate-hyp-basic (term alist interpreted-function-alist)
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
           (instantiate-hyp-basic-lst (fargs term) alist interpreted-function-alist)
           (if all-quotep
               ;; Try to evaluate the ground term:
               (mv-let (erp res)
                 (apply-axe-evaluator-basic-to-quoted-args fn args interpreted-function-alist)
                 (if erp ;; May be :unknown-function
                     (progn$
                      ;; If this message is printed a lot, we could suppress it:
                      (cw "(Note: In instantiate-hyp-basic: Failed to apply ~x0 to constant args.  Consider adding it to the evaluator, adding it to the interpreted-function-alist, or adding a constant-opener rule.)~%" fn)
                      (mv (cons fn args) ;; Return the ground term unevaluated
                          nil ; no free vars since it's a ground term (even though we couldn't evaluate it)
                          ))
                   (mv (enquote res)
                       nil ; no free vars
                       )))
             ;; The term has free vars iff the args did:
             ;; TODO: Consider cons-with-hint here:
             (mv (cons fn args) free-vars-in-args-flg)))))))

 ;; Returns (mv all-quotep args free-vars-flg).
 (defund instantiate-hyp-basic-lst (terms alist interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp alist)
                               (all-dargp (strip-cdrs alist))
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp terms)
       (mv t nil nil)
     (mv-let (instantiated-first first-term-free-vars-flg)
       (instantiate-hyp-basic (first terms) alist interpreted-function-alist)
       (mv-let (rest-all-quotep instantiated-rest rest-terms-free-vars-flg)
         (instantiate-hyp-basic-lst (rest terms) alist interpreted-function-alist)
         (mv (and rest-all-quotep (quotep instantiated-first))
             (cons instantiated-first instantiated-rest)
             (or first-term-free-vars-flg rest-terms-free-vars-flg)))))))

(make-flag instantiate-hyp-basic)

(defthm-flag-instantiate-hyp-basic
  (defthm true-listp-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (true-listp (mv-nth 1 (instantiate-hyp-basic-lst terms alist interpreted-function-alist)))
    :flag instantiate-hyp-basic-lst)
  :skip-others t
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm len-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (equal (len (mv-nth 1 (instantiate-hyp-basic-lst terms alist interpreted-function-alist)))
           (len terms))
    :flag instantiate-hyp-basic-lst)
  :skip-others t
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm booleanp-of-mv-nth-1-of-instantiate-hyp-basic
    (booleanp (mv-nth 1 (instantiate-hyp-basic term alist interpreted-function-alist)))
    :flag instantiate-hyp-basic)
  (defthm booleanp-of-mv-nth-2-of-instantiate-hyp-basic-lst
    (booleanp (mv-nth 2 (instantiate-hyp-basic-lst terms alist interpreted-function-alist)))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm axe-treep-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp term)
                  (all-dargp (strip-cdrs alist)))
             (axe-treep (mv-nth 0 (instantiate-hyp-basic term alist interpreted-function-alist))))
    :flag instantiate-hyp-basic)
  (defthm all-axe-treep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (pseudo-term-listp terms)
                  (all-dargp (strip-cdrs alist)))
             (all-axe-treep (mv-nth 1 (instantiate-hyp-basic-lst terms alist interpreted-function-alist))))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm bounded-axe-treep-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp term)
                  (all-dargp-less-than (strip-cdrs alist) dag-len))
             (bounded-axe-treep (mv-nth 0 (instantiate-hyp-basic term alist interpreted-function-alist))
                                dag-len))
    :flag instantiate-hyp-basic)
  (defthm all-bounded-axe-treep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (pseudo-term-listp terms)
                  (all-dargp-less-than (strip-cdrs alist) dag-len))
             (all-bounded-axe-treep (mv-nth 1 (instantiate-hyp-basic-lst terms alist interpreted-function-alist))
                                    dag-len))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm all-myquotep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (mv-nth 0 (instantiate-hyp-basic-lst terms alist interpreted-function-alist))
                  (pseudo-term-listp terms)
                  (all-dargp (strip-cdrs alist)))
             (all-myquotep (mv-nth 1 (instantiate-hyp-basic-lst terms alist interpreted-function-alist))))
    :flag instantiate-hyp-basic-lst)
  :skip-others t
  :hints (("Goal" :in-theory (e/d (instantiate-hyp-basic instantiate-hyp-basic-lst) (myquotep)))))

(verify-guards instantiate-hyp-basic :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthm consp-of-mv-nth-0-of-instantiate-hyp-basic
  (implies (consp term)
           (consp (mv-nth 0 (instantiate-hyp-basic term alist interpreted-function-alist))))
  :hints (("Goal" :expand ((instantiate-hyp-basic term alist interpreted-function-alist)))))

(defthm-flag-instantiate-hyp-basic
  (defthm true-listp-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp term)
                  (consp term))
             (true-listp (mv-nth 0 (instantiate-hyp-basic term alist interpreted-function-alist))))
    :flag instantiate-hyp-basic)
  :skip-others t
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm not-equal-of-quote-and-car-of-mv-nth-0-of-instantiate-hyp-basic
  (implies (and ;; free vars remain in the term:
                (mv-nth 1 (instantiate-hyp-basic term alist interpreted-function-alist)))
           (not (equal 'quote (car (mv-nth 0 (instantiate-hyp-basic term alist interpreted-function-alist))))))
  :hints (("Goal" :expand ((instantiate-hyp-basic term alist interpreted-function-alist)))))

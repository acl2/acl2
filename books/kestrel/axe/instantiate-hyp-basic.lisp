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

;; TODO: Create a tool to generate this, given an evaluator.

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

;move
(defthm pseudo-lambdap-of-car
  (implies (pseudo-termp form)
           (equal (pseudo-lambdap (car form))
                  (not (symbolp (car form)))))
  :hints (("Goal" :expand ((pseudo-termp form))
           :in-theory (enable pseudo-termp pseudo-lambdap))))

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
  :hints (("Goal" :in-theory (enable ASSOC-EQUAL strip-cdrs))))

;;;
;;; instantiate-hyp-basic
;;;

;FORM is a tree (from the hyp of a rule) with quoteps and vars at the leaves
;ALIST binds vars to quoteps and/or nodenums
;this one does *not* wrap remaining free vars in :free
;; Returns (mv form free-vars-flg) where FORM has been instantiated with ALIST and FREE-VARS-FLG indicates whether any variables remain in FORM.
(mutual-recursion
 (defund instantiate-hyp-basic (form alist free-vars-flg interpreted-function-alist)
   (declare (xargs :verify-guards nil ;done below
                   :guard (and (pseudo-termp form)
                               (symbol-alistp alist)
                               (all-dargp (strip-cdrs alist))
                               (booleanp free-vars-flg)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (variablep form)
       (let ((match (assoc-eq form alist)))
         (if match
             (mv (cdr match) free-vars-flg) ;the var has a binding in the alist and so is not free
           (mv form t)                      ;the var is free
           ))
     (let ((fn (ffn-symb form)))
       (if (eq 'quote fn)
           (mv form free-vars-flg)
         ;;a function call (used to handle IFs specially but that didn't seem worth it):
         (mv-let (ground-termp args free-vars-flg)
           (instantiate-hyp-basic-lst (fargs form) alist free-vars-flg interpreted-function-alist)
           (if ground-termp
               (mv-let (erp res)
                 (apply-axe-evaluator-basic-to-quoted-args fn args interpreted-function-alist)
                 (if erp ;; May be :unknown-function
                     ;; If this message is printed a lot, we could suppress it:
                     (progn$ ;; (cw "(Note: Failed to apply ~x0 to constant args.  Consider adding it to the evaluator or adding a constant-opener rule.)~%" fn)
                             (mv (cons fn args) ;; Return the ground term unevaluated
                                 free-vars-flg))
                   (mv (enquote res)
                       free-vars-flg)))
             (mv (cons fn args) free-vars-flg)))))))

 ;; Returns (mv ground-termp args free-vars-flg).
 (defund instantiate-hyp-basic-lst (forms alist free-vars-flg interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-term-listp forms)
                               (symbol-alistp alist)
                               (all-dargp (strip-cdrs alist))
                               (booleanp free-vars-flg)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp forms)
       (mv t nil free-vars-flg)
     (mv-let (new-first free-vars-flg)
       (instantiate-hyp-basic (first forms) alist free-vars-flg interpreted-function-alist)
       (mv-let (rest-ground-termp new-rest free-vars-flg)
         (instantiate-hyp-basic-lst (rest forms) alist free-vars-flg interpreted-function-alist)
         (mv (and rest-ground-termp (quotep new-first))
             (cons new-first new-rest)
             free-vars-flg))))))

(make-flag instantiate-hyp-basic)

(defthm-flag-instantiate-hyp-basic
  (defthm theorem-for-instantiate-hyp-basic
    t
    :rule-classes nil
    :flag instantiate-hyp-basic)
  (defthm true-listp-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (true-listp (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg interpreted-function-alist)))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm theorem-for-instantiate-hyp-basic3
    t
    :rule-classes nil
    :flag instantiate-hyp-basic)
  (defthm len-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (equal (len (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg interpreted-function-alist)))
           (len forms))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm booleanp-of-mv-nth-1-of-instantiate-hyp-basic
    (implies (booleanp free-vars-flg)
             (booleanp (mv-nth 1 (instantiate-hyp-basic form alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-basic)
  (defthm booleanp-of-mv-nth-2-of-instantiate-hyp-basic-lst
    (implies (booleanp free-vars-flg)
             (booleanp (mv-nth 2 (instantiate-hyp-basic-lst forms alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm axe-treep-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp form)
                  (all-dargp (strip-cdrs alist)))
             (axe-treep (mv-nth 0 (instantiate-hyp-basic form alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-basic)
  (defthm all-axe-treep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (pseudo-term-listp forms)
                  (all-dargp (strip-cdrs alist)))
             (all-axe-treep (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg
                                                                  interpreted-function-alist))))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm bounded-axe-treep-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp form)
                  (all-dargp-less-than (strip-cdrs alist) dag-len))
             (bounded-axe-treep (mv-nth 0 (instantiate-hyp-basic form alist free-vars-flg interpreted-function-alist))
                                dag-len))
    :flag instantiate-hyp-basic)
  (defthm all-bounded-axe-treep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (pseudo-term-listp forms)
                  (all-dargp-less-than (strip-cdrs alist) dag-len))
             (all-bounded-axe-treep (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg
                                                                          interpreted-function-alist))
                                    dag-len))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

(defthm-flag-instantiate-hyp-basic
  (defthm theorem-for-instantiate-hyp-basic4
    t
    :rule-classes nil
    :flag instantiate-hyp-basic)
  (defthm all-myquotep-of-mv-nth-1-of-instantiate-hyp-basic-lst
    (implies (and (mv-nth 0 (instantiate-hyp-basic-lst forms alist free-vars-flg interpreted-function-alist))
                  (pseudo-term-listp forms)
                  (all-dargp (strip-cdrs alist)))
             (all-myquotep (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (e/d (instantiate-hyp-basic instantiate-hyp-basic-lst) (myquotep)))))

(verify-guards instantiate-hyp-basic :otf-flg t :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthm consp-of-mv-nth-0-of-instantiate-hyp-basic
  (implies (consp form)
           (consp (mv-nth 0 (instantiate-hyp-basic form alist free-vars-flg interpreted-function-alist))))
  :hints (("Goal" :expand ((instantiate-hyp-basic form alist free-vars-flg
                                                   interpreted-function-alist)))))

(defthm-flag-instantiate-hyp-basic
  (defthm true-listp-of-mv-nth-0-of-instantiate-hyp-basic
    (implies (and (pseudo-termp form)
                  (consp form))
             (true-listp (mv-nth 0 (instantiate-hyp-basic form alist free-vars-flg interpreted-function-alist))))
    :flag instantiate-hyp-basic)
  (defthm true-listp-of-mv-nth-1-of-instantiate-hyp-basic-lst-2 ;todo clash
    (true-listp (mv-nth 1 (instantiate-hyp-basic-lst forms alist free-vars-flg
                                                      interpreted-function-alist)))
    :flag instantiate-hyp-basic-lst)
  :hints (("Goal" :in-theory (enable instantiate-hyp-basic instantiate-hyp-basic-lst))))

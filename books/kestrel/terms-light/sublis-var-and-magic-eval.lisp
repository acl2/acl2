; Applying a substitution to a term and evaluating ground terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; (include-book "all-quotep")
(include-book "kestrel/utilities/symbol-term-alistp" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system) ;for unquote-list
(include-book "tools/flag" :dir :system)

;; TODO: Consider getting rid of (if x 't 'nil) when x is boolean.  Or take an iff flag?

;; See also the function sublis-var-simple.

(local (in-theory (disable myquotep mv-nth)))

;; Apply ALIST to replace free variables in TERM, evaluating ground terms and
;; resolving IFs as much as possible.  Free variables not bound in ALIST are
;; left alone.
(mutual-recursion
 (defund sublis-var-and-magic-eval (alist term state) ;todo: call this 'term'?
   (declare (xargs :measure (acl2-count term)
                   :guard (and (symbol-alistp alist) ; usually a symbol-term-alistp
                               (pseudo-termp term))
                   :stobjs state))
   (if (variablep term)
       (let ((res (assoc-eq term alist)))
         (if res (cdr res) term))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         ;; it's a function call:
         (let* ((new-args (sublis-var-and-magic-eval-lst alist (fargs term) state)))
           (if (eq 'if fn)
               (if (myquotep (first new-args)) ;test was resolved ; todo: weaken check to myquotep?
                   (if (unquote (first new-args))
                       (second new-args) ;then branch
                     (third new-args)    ;else branch
                     )
                 ;; test was not resolved:
                 `(if ,@new-args))
             (if (and (symbolp fn) ;todo: handle lambdas?
                      (all-myquotep new-args) ;weaken to all-quotep?
                      )
                 (b* (((mv erp res)
                       (magic-ev-fncall fn (unquote-list new-args) state nil t))
                      ((when erp)
                       (er hard? 'sublis-var-and-magic-eval "Error evaluating ~x0 applied to ~x1." fn new-args)))
                   (enquote res))
               `(,fn ,@new-args))))))))

 (defund sublis-var-and-magic-eval-lst (alist terms state)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp terms))
                   :stobjs state))
   (if (endp terms) ;(null terms)
       nil
     (cons (sublis-var-and-magic-eval alist (car terms) state)
           (sublis-var-and-magic-eval-lst alist (cdr terms) state)))))

(make-flag sublis-var-and-magic-eval)

;; (defthm-flag-sublis-var-and-magic-eval
;;   (defthm sublis-var-and-magic-eval-of-nil
;;     (implies (pseudo-termp term)
;;              (equal (sublis-var-and-magic-eval nil term state)
;;                     term))
;;     :flag sublis-var-and-magic-eval)
;;   (defthm sublis-var-and-magic-eval-lst-of-nil
;;     (implies (pseudo-term-listp terms)
;;              (equal (sublis-var-and-magic-eval-lst nil terms state)
;;                     terms))
;;     :flag sublis-var-and-magic-eval-lst)
;;   :hints (("Goal" :in-theory (enable sublis-var-and-magic-eval
;;                                      sublis-var-and-magic-eval-lst))))

(defthm true-listp-of-sublis-var-and-magic-eval-lst
  (true-listp (sublis-var-and-magic-eval-lst alist terms state)))

(defthm len-of-sublis-var-and-magic-eval-lst
  (equal (len (sublis-var-and-magic-eval-lst alist terms state))
         (len terms))
  :hints (("Goal" :in-theory (enable sublis-var-and-magic-eval-lst))))

(defthm-flag-sublis-var-and-magic-eval
  (defthm pseudo-termp-of-sublis-var-and-magic-eval
    (implies (and (pseudo-termp term)
                  (symbol-term-alistp alist))
             (pseudo-termp (sublis-var-and-magic-eval alist term state)))
    :flag sublis-var-and-magic-eval)
  (defthm pseudo-term-listp-of-sublis-var-and-magic-eval-lst
    (implies (and (pseudo-term-listp terms)
                  (symbol-term-alistp alist))
             (pseudo-term-listp (sublis-var-and-magic-eval-lst alist terms state)))
    :flag sublis-var-and-magic-eval-lst)
  :hints (("Goal" :in-theory (enable sublis-var-and-magic-eval
                                     sublis-var-and-magic-eval-lst)
           :expand ((pseudo-termp (cons (car term) (sublis-var-and-magic-eval-lst alist (cdr term) state)))))))

;; (defthm car-of-sublis-var-and-magic-eval
;;   (equal (car (sublis-var-and-magic-eval alist term state))
;;          (if (variablep term)
;;              (if (assoc-eq term alist)
;;                  (cadr (assoc-eq term alist))
;;                nil)
;;            (car term)))
;;   :hints (("Goal" :in-theory (enable sublis-var-and-magic-eval))))

;; (defthm consp-of-sublis-var-and-magic-eval
;;   (implies (consp term)
;;            (consp (sublis-var-and-magic-eval alist term state)))
;;   :hints (("Goal" :expand ((sublis-var-and-magic-eval alist term state)))))

;; (defthm cdr-of-sublis-var-and-magic-eval
;;   (equal (cdr (sublis-var-and-magic-eval alist term state))
;;          (if (variablep term)
;;              (if (assoc-eq term alist)
;;                  (cddr (assoc-eq term alist))
;;                nil)
;;            (if (equal 'quote (car term))
;;                (cdr term)
;;              (sublis-var-and-magic-eval-lst alist (cdr term) state))))
;;   :hints (("Goal" :in-theory (enable sublis-var-and-magic-eval))))

(defthm car-of-sublis-var-and-magic-eval-lst
  (implies (consp terms)
           (equal (car (sublis-var-and-magic-eval-lst alist terms state))
                  (sublis-var-and-magic-eval alist (car terms) state)))
  :hints (("Goal" :expand (sublis-var-and-magic-eval-lst alist terms state)
           :in-theory (enable sublis-var-and-magic-eval-lst))))

;; (defthm-flag-sublis-var-and-magic-eval
;;   (defthm sublis-var-and-magic-eval-of-nil
;;     (implies (pseudo-termp term)
;;              (equal (sublis-var-and-magic-eval nil term state)
;;                     term))
;;     :flag sublis-var-and-magic-eval)
;;   (defthm sublis-var-and-magic-eval-lst-of-nil
;;     (implies (pseudo-term-listp terms)
;;              (equal (sublis-var-and-magic-eval-lst nil terms state)
;;                     terms))
;;     :flag sublis-var-and-magic-eval-lst))

; Utilities for manipulating declares (e.g., in xargs of defuns)
;
; Copyright (C) 2015-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains utilities about declares (of the sort that appear in
;; defuns).  These utilities depend on more books than the utilities in
;; declares0.lisp.

(include-book "kestrel/utilities/declares0" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/untranslated-terms" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system) ;for replace-in-term
(include-book "kestrel/utilities/make-and-nice" :dir :system)

;;; Applying a substitution to a measure:

(defun substitute-measure-in-xargs (xargs alist state)
  (declare (xargs :guard (and (alistp alist)
                              (xargsp xargs))
                  :mode :program ;because of the call to translate-term
                  :stobjs state))
  (if (endp xargs)
      nil
    (if (eq :measure (first xargs))
        (let* ((measure (second xargs))
               (measure (translate-term measure 'substitute-measure-in-xargs (w state)))) ;ensures replace-in-term is given a pseudo-term
          `(:measure ,(replace-in-term measure alist) ,@(cddr xargs))) ;can only be one measure...
      `(,(first xargs) ,(second xargs) ,@(substitute-measure-in-xargs (cddr xargs) alist state)))))

(defun substitute-measure-in-declare-args (declare-args alist state)
  (declare (xargs :guard (all-declare-argp declare-args)
                  :mode :program
                  :stobjs state))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(substitute-measure-in-xargs (fargs arg) alist state))
                (substitute-measure-in-declare-args (rest declare-args) alist state))
        (cons arg (substitute-measure-in-declare-args (rest declare-args) alist state))))))

(defun substitute-measure-in-declares (declares alist state)
  (declare (xargs :guard (all-declarep declares)
                  :mode :program
                  :stobjs state))
  (if (atom declares)
      nil
    (cons `(declare ,@(substitute-measure-in-declare-args (fargs (first declares)) alist state))
          (substitute-measure-in-declares (rest declares) alist state))))

;;; Applying a substitution to a measure without translating it (TODO: Compare to the routines just above):

(defun substitute-vars-in-measure-in-xargs (xargs alist wrld)
  (declare (xargs :guard (and (xargsp xargs)
                              (symbol-alistp alist)
                              (plist-worldp wrld))
                  :mode :program ;todo
                  ))
  (if (endp xargs)
      nil
    (if (eq :measure (first xargs))
        (let* ((measure (second xargs))
               (new-measure (sublis-var-untranslated-term alist measure)))
          `(:measure ,new-measure ,@(cddr xargs))) ;can only be one measure so no need to recur
      `(,(first xargs) ,(second xargs) ,@(substitute-vars-in-measure-in-xargs (cddr xargs) alist wrld)))))

(defun substitute-vars-in-measure-in-declare-args (declare-args alist wrld)
  (declare (xargs :guard (and (all-declare-argp declare-args)
                              (symbol-alistp alist)
                              (plist-worldp wrld))
                  :mode :program))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(substitute-vars-in-measure-in-xargs (fargs arg) alist wrld))
                (substitute-vars-in-measure-in-declare-args (rest declare-args) alist wrld))
        (cons arg (substitute-vars-in-measure-in-declare-args (rest declare-args) alist wrld))))))

(defun substitute-vars-in-measure-in-declares (declares alist wrld)
  (declare (xargs :guard (and (all-declarep declares)
                              (symbol-alistp alist)
                              (plist-worldp wrld))
                  :mode :program))
  (if (atom declares)
      nil
    (cons `(declare ,@(substitute-vars-in-measure-in-declare-args (fargs (first declares)) alist wrld))
          (substitute-vars-in-measure-in-declares (rest declares) alist wrld))))


;;; Dropping conjuncts from a guard that mention the given var

(defun untranslated-nilp (term)
  (declare (xargs :guard t))
  (or (equal term 'nil)
      (equal term ''nil)))

(mutual-recursion
 (defun get-conjuncts-of-untranslated-term (term)
   (declare (xargs :guard t))
   (if (and (call-of 'if term)
            (= 3 (len (fargs term)))
            (untranslated-nilp (farg3 term)))
       ;; (if x y nil) is (and x y)
       (append (get-conjuncts-of-untranslated-term (farg1 term))
               (get-conjuncts-of-untranslated-term (farg2 term)))
     (if (call-of 'and term)
         (get-conjuncts-of-untranslated-terms (fargs term))
       (list term))))

 (defun get-conjuncts-of-untranslated-terms (terms)
   (declare (xargs :guard t))
   (if (atom terms)
       nil
     (append (get-conjuncts-of-untranslated-term (first terms))
             (get-conjuncts-of-untranslated-terms (rest terms))))))

;; (get-conjuncts-of-untranslated-term '(and x y (if z w 'nil) (if foo bar nil)))

;; (make-flag get-conjuncts-of-untranslated-term)

;; (defthm-flag-get-conjuncts-of-untranslated-term
;;   (defthm theorem-for-get-conjuncts-of-untranslated-term
;;     (true-listp (get-conjuncts-of-untranslated-term term))
;;     :flag get-conjuncts-of-untranslated-term)
;;   (defthm theorem-for-get-conjuncts-of-untranslated-terms
;;     (true-listp (get-conjuncts-of-untranslated-terms terms))
;;     :flag get-conjuncts-of-untranslated-terms))

(defun drop-untranslated-terms-that-mention-vars (terms vars)
  (declare (xargs :guard (and ;(pseudo-term-listp terms)
                          (true-listp terms)
                          (untranslated-term-listp terms)
                          (symbol-listp vars))))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (intersection-eq (get-vars-in-untranslated-term term)
                           vars)
          (drop-untranslated-terms-that-mention-vars (rest terms)
                                                     vars)
        (cons term
              (drop-untranslated-terms-that-mention-vars (rest terms)
                                                         vars))))))


;; TERM is an untranslated term
(defun drop-guard-conjuncts-that-mention-vars (term vars)
  (declare (xargs :guard (and ;(pseudo-termp term)
                          (symbol-listp vars))))
  (let* ((conjuncts (get-conjuncts-of-untranslated-term term)))
    (if (not (untranslated-term-listp conjuncts)) ;todo, for guards
        (er hard? 'drop-guard-conjuncts-that-mention-vars "Unsupported conjuncts: ~x0" conjuncts)
      (make-and-nice (drop-untranslated-terms-that-mention-vars conjuncts vars)))))

(defun drop-guard-conjuncts-that-mention-vars-in-xargs (xargs vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (xargsp xargs)))) ;TODO: need to know that guards are pseudo-terms?  switch to untranslated-term utilities
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        `(:guard ,(drop-guard-conjuncts-that-mention-vars (second xargs) vars) ,@(drop-guard-conjuncts-that-mention-vars-in-xargs (cddr xargs) vars)) ;there may be more guards
      `(,(first xargs) ,(second xargs) ,@(drop-guard-conjuncts-that-mention-vars-in-xargs (cddr xargs) vars)))))

;returns a list of new declare-args
(defun drop-guard-conjuncts-that-mention-vars-in-declare-args (declare-args vars)
  ; (declare (xargs :guard (and (all-declare-argp declare-args)
  ;;                             (symbol-listp vars))))
  (if (atom declare-args)
      nil
    (let* ((arg (first declare-args))
           ;;args has to be a list because it may be nil:
           (args (if (eq 'xargs (ffn-symb arg))
                     `((xargs ,@(drop-guard-conjuncts-that-mention-vars-in-xargs (fargs arg) vars)))
                   (if (eq 'type (ffn-symb arg)) ;(type <type-spec> term)
                       (if (eq vars (farg2 arg))
                           nil ;drop this declare because it is about vars
                         `((type ,(farg1 arg) ,(replace-in-term (farg2 arg) vars))))
                     (list arg)))))
      (append args
              (drop-guard-conjuncts-that-mention-vars-in-declare-args (rest declare-args) vars)))))

(defun drop-guard-conjuncts-that-mention-vars-in-declares (declares vars)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(drop-guard-conjuncts-that-mention-vars-in-declare-args (fargs (first declares)) vars))
          (drop-guard-conjuncts-that-mention-vars-in-declares (rest declares) vars))))

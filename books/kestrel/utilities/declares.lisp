; Utilities for manipulating declares (e.g., in xargs of defuns)
;
; Copyright (C) 2015-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This book includes utilities about declares that also need to manipulate untranslated terms.

(include-book "declares0")
(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)
(include-book "hints")

;;; Applying a substitution to a guard

(defun substitute-guard-in-xargs (xargs alist)
  (declare (xargs :guard (and (alistp alist)
                              (keyword-value-listp xargs) ;(xargsp xargs)
                              (untranslated-term-listp (strip-cdrs alist))
                              )))
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        (let* ((guard (second xargs))
               (guard (if (not (untranslated-termp guard))
                          (er hard? 'substitute-guard-in-xargs "Unsupported untranslated term: ~x0." guard)
                        (replace-in-untranslated-term guard alist))))
          `(:guard ,guard ,@(substitute-guard-in-xargs (cddr xargs) alist))) ;there may be more guards
      `(,(first xargs) ,(second xargs) ,@(substitute-guard-in-xargs (cddr xargs) alist)))))

(defun substitute-guard-in-declare-args (declare-args alist)
  ;; (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let* ((arg (first declare-args))
           (arg (if (eq 'xargs (ffn-symb arg))
                    `(xargs ,@(substitute-guard-in-xargs (fargs arg) alist))
                  (if (eq 'type (ffn-symb arg)) ;(type <type-spec> term)
                      `(type ,(farg1 arg) ,(replace-in-term (farg2 arg) alist))
                    arg))))
      (cons arg
            (substitute-guard-in-declare-args (rest declare-args) alist)))))

(defun substitute-guard-in-declares (declares alist)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(substitute-guard-in-declare-args (fargs (first declares)) alist))
          (substitute-guard-in-declares (rest declares) alist))))


;; Fixup the ignore declarations to ignore exactly those formals not mentioned in the body.
;; Note that irrelevant params may have to be dealt with separately.
(defun fixup-ignores (declares formals body)
  (declare (xargs :guard (and (symbol-listp formals)
                              (untranslated-termp body) ;TODO: relax this
                              (all-declarep declares))))
  (let* ((formals-mentioned (get-vars-in-untranslated-term body))
         (ignored-formals (set-difference-eq formals formals-mentioned))
         (declares (remove-declares 'ignore declares))
         ;; Also remove any ignorable declares, since we are setting the ignore to be exactly what we need:
         (declares (remove-declares 'ignorable declares))
         (declares (if ignored-formals
                       (add-declare-arg `(ignore ,@ignored-formals) declares)
                     declares)))
    declares))

;;; Rename the functions in a guard

(defun apply-function-renaming-to-guard-in-xargs (xargs function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        (if (not (untranslated-termp (second xargs))) ;todo: drop this once we strengthen xargsp
            (hard-error 'apply-function-renaming-to-guard-in-xargs "Guard is not an (untranslated) term." nil)
          `(:guard ,(rename-fns-in-untranslated-term (second xargs) function-renaming)
                   ,@(apply-function-renaming-to-guard-in-xargs (cddr xargs) function-renaming))) ;there may be more guards
      `(,(first xargs) ,(second xargs) ,@(apply-function-renaming-to-guard-in-xargs (cddr xargs) function-renaming)))))

(defun apply-function-renaming-to-guard-in-declare-args (declare-args function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      nil
    (let* ((arg (first declare-args))
           (arg (if (eq 'xargs (ffn-symb arg))
                    `(xargs ,@(apply-function-renaming-to-guard-in-xargs (fargs arg) function-renaming))
                  (if (eq 'type (ffn-symb arg)) ;(type <type-spec> term)
                      (if (not (untranslated-termp (farg2 arg))) ;todo: drop this once we strengthen xargsp
                          (prog2$ (hard-error 'apply-function-renaming-to-guard-in-declare-args "Type decl is not an (untranslated) term." nil)
                                  arg)
                        `(type ,(farg1 arg) ,(rename-fns-in-untranslated-term (farg2 arg) function-renaming)))
                    arg))))
      (cons arg
            (apply-function-renaming-to-guard-in-declare-args (rest declare-args) function-renaming)))))

(defun apply-function-renaming-to-guard-in-declare (declare function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (declarep declare))))
  `(declare ,@(apply-function-renaming-to-guard-in-declare-args (fargs declare) function-renaming)))

(defun apply-function-renaming-to-guard-in-declares (declares function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declarep declares))))
  (if (atom declares)
      nil
    (cons (apply-function-renaming-to-guard-in-declare (first declares) function-renaming)
          (apply-function-renaming-to-guard-in-declares (rest declares) function-renaming))))



(defun simplify-nth-of-cons-in-untranslated-guard (xargs)
   ;; (declare (xargs :guard (and ;(p )
   ;;                             (xargsp xargs)))) ;; need to strengthen xargsp to guarantee that the guard is a term
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        `(:guard ,(clean-up-nth-of-cons-in-untranslated-term (second xargs)) ,@(simplify-nth-of-cons-in-untranslated-guard (cddr xargs)))
      `(,(first xargs) ,(second xargs) ,@(simplify-nth-of-cons-in-untranslated-guard (cddr xargs))))))

(defun simplify-nth-of-cons-in-untranslated-guard-in-declare-args (declare-args)
  ;; (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(simplify-nth-of-cons-in-untranslated-guard (fargs arg)))
                (simplify-nth-of-cons-in-untranslated-guard-in-declare-args (rest declare-args)))
        (cons arg (simplify-nth-of-cons-in-untranslated-guard-in-declare-args (rest declare-args)))))))

(defun simplify-nth-of-cons-in-untranslated-guard-in-declares (declares)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(simplify-nth-of-cons-in-untranslated-guard-in-declare-args (fargs (first declares))))
          (simplify-nth-of-cons-in-untranslated-guard-in-declares (rest declares)))))




(defun simplify-true-listp-of-cons-in-untranslated-guard (xargs)
   ;; (declare (xargs :guard (and ;(p )
   ;;                             (xargsp xargs)))) ;; need to strengthen xargsp to guarantee that the guard is a term
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        `(:guard ,(clean-up-true-listp-of-cons-in-untranslated-term (second xargs)) ,@(simplify-true-listp-of-cons-in-untranslated-guard (cddr xargs)))
      `(,(first xargs) ,(second xargs) ,@(simplify-true-listp-of-cons-in-untranslated-guard (cddr xargs))))))

(defun simplify-true-listp-of-cons-in-untranslated-guard-in-declare-args (declare-args)
  ;; (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(simplify-true-listp-of-cons-in-untranslated-guard (fargs arg)))
                (simplify-true-listp-of-cons-in-untranslated-guard-in-declare-args (rest declare-args)))
        (cons arg (simplify-true-listp-of-cons-in-untranslated-guard-in-declare-args (rest declare-args)))))))

(defun simplify-true-listp-of-cons-in-untranslated-guard-in-declares (declares)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(simplify-true-listp-of-cons-in-untranslated-guard-in-declare-args (fargs (first declares))))
          (simplify-true-listp-of-cons-in-untranslated-guard-in-declares (rest declares)))))


(defun simplify-and-of-t-in-untranslated-guard (xargs)
   ;; (declare (xargs :guard (and ;(p )
   ;;                             (xargsp xargs)))) ;; need to strengthen xargsp to guarantee that the guard is a term
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        `(:guard ,(clean-up-and-of-t-in-untranslated-term (second xargs)) ,@(simplify-and-of-t-in-untranslated-guard (cddr xargs)))
      `(,(first xargs) ,(second xargs) ,@(simplify-and-of-t-in-untranslated-guard (cddr xargs))))))

(defun simplify-and-of-t-in-untranslated-guard-in-declare-args (declare-args)
  ;; (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(simplify-and-of-t-in-untranslated-guard (fargs arg)))
                (simplify-and-of-t-in-untranslated-guard-in-declare-args (rest declare-args)))
        (cons arg (simplify-and-of-t-in-untranslated-guard-in-declare-args (rest declare-args)))))))

(defun simplify-and-of-t-in-untranslated-guard-in-declares (declares)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(simplify-and-of-t-in-untranslated-guard-in-declare-args (fargs (first declares))))
          (simplify-and-of-t-in-untranslated-guard-in-declares (rest declares)))))


(defun simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard (xargs)
   ;; (declare (xargs :guard (and ;(p )
   ;;                             (xargsp xargs)))) ;; need to strengthen xargsp to guarantee that the guard is a term
  (if (endp xargs)
      nil
    (if (eq :guard (first xargs))
        `(:guard ,(clean-up-equal-of-len-of-cons-nest-and-number-in-untranslated-term (second xargs)) ,@(simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard (cddr xargs)))
      `(,(first xargs) ,(second xargs) ,@(simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard (cddr xargs))))))

(defun simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declare-args (declare-args)
  ;; (declare (xargs :guard (all-declare-argp declare-args)))
  (if (atom declare-args)
      nil
    (let ((arg (first declare-args)))
      (if (eq 'xargs (ffn-symb arg))
          (cons `(xargs ,@(simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard (fargs arg)))
                (simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declare-args (rest declare-args)))
        (cons arg (simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declare-args (rest declare-args)))))))

(defun simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declares (declares)
  ;; (declare (xargs :guard (all-declarep declares)))
  (if (atom declares)
      nil
    (cons `(declare ,@(simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declare-args (fargs (first declares))))
          (simplify-equal-of-len-of-cons-nest-and-number-in-untranslated-guard-in-declares (rest declares)))))


;;;
;;; Rename the functions in :guard-hints
;;;

(defund apply-function-renaming-to-guard-hints-in-xargs (xargs function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq :guard-hints (first xargs))
        (if (not (true-listp (second xargs)))
            (er hard? 'apply-function-renaming-to-guard-hints-in-xargs "Ill-formed hints: ~x0." (second xargs))
          `(:guard-hints ,(apply-renaming-to-hints (second xargs) function-renaming)
                         ,@(cddr xargs))) ;there can only be one occurence of :guard-hints
      `(,(first xargs) ,(second xargs) ,@(apply-function-renaming-to-guard-hints-in-xargs (cddr xargs) function-renaming)))))

(defund apply-function-renaming-to-guard-hints-in-declare-args (declare-args function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      nil
    (let* ((arg (first declare-args))
           (arg (if (eq 'xargs (ffn-symb arg))
                    `(xargs ,@(apply-function-renaming-to-guard-hints-in-xargs (fargs arg) function-renaming))
                  arg)))
      (cons arg
            (apply-function-renaming-to-guard-hints-in-declare-args (rest declare-args) function-renaming)))))

(defund apply-function-renaming-to-guard-hints-in-declare (declare function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (declarep declare))))
  `(declare ,@(apply-function-renaming-to-guard-hints-in-declare-args (fargs declare) function-renaming)))

(defund apply-function-renaming-to-guard-hints-in-declares (declares function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declarep declares))))
  (if (atom declares)
      nil
    (cons (apply-function-renaming-to-guard-hints-in-declare (first declares) function-renaming)
          (apply-function-renaming-to-guard-hints-in-declares (rest declares) function-renaming))))


;;;
;;; Rename the functions in :hints
;;;

(defund apply-function-renaming-to-hints-in-xargs (xargs function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (xargsp xargs))))
  (if (endp xargs)
      nil
    (if (eq :hints (first xargs))
        (if (not (true-listp (second xargs)))
            (er hard? 'apply-function-renaming-to-hints-in-xargs "Ill-formed hints: ~x0." (second xargs))
          `(:hints ,(apply-renaming-to-hints (second xargs) function-renaming)
                   ,@(cddr xargs))) ;there can only be one occurence of :hints
      `(,(first xargs) ,(second xargs) ,@(apply-function-renaming-to-hints-in-xargs (cddr xargs) function-renaming)))))

(defund apply-function-renaming-to-hints-in-declare-args (declare-args function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declare-argp declare-args))))
  (if (atom declare-args)
      nil
    (let* ((arg (first declare-args))
           (arg (if (eq 'xargs (ffn-symb arg))
                    `(xargs ,@(apply-function-renaming-to-hints-in-xargs (fargs arg) function-renaming))
                  arg)))
      (cons arg
            (apply-function-renaming-to-hints-in-declare-args (rest declare-args) function-renaming)))))

(defund apply-function-renaming-to-hints-in-declare (declare function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (declarep declare))))
  `(declare ,@(apply-function-renaming-to-hints-in-declare-args (fargs declare) function-renaming)))

(defund apply-function-renaming-to-hints-in-declares (declares function-renaming)
  (declare (xargs :guard (and (symbol-alistp function-renaming)
                              (all-declarep declares))))
  (if (atom declares)
      nil
    (cons (apply-function-renaming-to-hints-in-declare (first declares) function-renaming)
          (apply-function-renaming-to-hints-in-declares (rest declares) function-renaming))))

(in-theory (disable declarep)) ;move

(in-theory (disable xargsp)) ;move

(defthm declare-of-cons
  (equal (declarep (cons a x))
         (and (equal 'declare a)
              (all-declare-argp x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable declarep))))

(defthm keyword-value-listp-of-apply-function-renaming-to-guard-hints-in-xargs
  (implies (xargsp xargs)
           (keyword-value-listp (apply-function-renaming-to-guard-hints-in-xargs xargs function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-hints-in-xargs xargsp))))

(defthm all-declare-argp-of-apply-function-renaming-to-guard-hints-in-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (apply-function-renaming-to-guard-hints-in-declare-args declare-args function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-hints-in-declare-args))))

(defthm declarep-of-apply-function-renaming-to-guard-hints-in-declare-args
  (implies (declarep declare)
           (declarep (apply-function-renaming-to-guard-hints-in-declare declare function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-hints-in-declare declarep))))

(defthm keyword-value-listp-of-apply-function-renaming-to-hints-in-xargs
  (implies (xargsp xargs)
           (keyword-value-listp (apply-function-renaming-to-hints-in-xargs xargs function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-hints-in-xargs xargsp))))

(defthm all-declare-argp-of-apply-function-renaming-to-hints-in-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (apply-function-renaming-to-hints-in-declare-args declare-args function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-hints-in-declare-args))))

(defthm declarep-of-apply-function-renaming-to-hints-in-declare-args
  (implies (declarep declare)
           (declarep (apply-function-renaming-to-hints-in-declare declare function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-hints-in-declare declarep))))

(defthm keyword-value-listp-of-apply-function-renaming-to-guard-in-xargs
  (implies (xargsp xargs)
           (keyword-value-listp (apply-function-renaming-to-guard-in-xargs xargs function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-in-xargs xargsp keyword-value-listp))))

(defthm all-declare-argp-of-apply-function-renaming-to-guard-in-declare-args
  (implies (all-declare-argp declare-args)
           (all-declare-argp (apply-function-renaming-to-guard-in-declare-args declare-args function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-in-declare-args))))

(defthm declarep-of-apply-function-renaming-to-guard-in-declare-args
  (implies (declarep declare)
           (declarep (apply-function-renaming-to-guard-in-declare declare function-renaming)))
  :hints (("Goal" :in-theory (enable apply-function-renaming-to-guard-in-declare declarep))))

; A tool to make an evaluator for a set of functions.
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

;; A tool to make an evaluator for a set of functions.  Does not handle
;; embedded dags and does not know how to evaluate itself.  Uses a count to
;; ensure termination.  Returns an error flag as well as the result.

(include-book "std/util/bstar" :dir :system) ; todo: move to generated event
(include-book "kestrel/utilities/fixnums" :dir :system)
(include-book "make-evaluator-common")
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/utilities/unquote-list" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system) ;for erp-nil
(include-book "kestrel/utilities/myif" :dir :system) ;since we give it special treatment below
(include-book "kestrel/alists-light/pairlis-dollar-fast" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/alists-light/acons-unique" :dir :system)
(include-book "kestrel/typed-lists-light/all-alistp" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))

;; TODO: Consider adding special handling for BOOLIF and BVIF.

(local
 (defthm symbol-alistp-of-lookup-equal
   (implies (symbol-alist-listp (strip-cdrs alist))
            (symbol-alistp (lookup-equal key alist)))
   :hints (("Goal" :in-theory (enable lookup-equal)))))

(local
 (defthm symbol-alist-listp-of-strip-cdrs-of-acons-unique
   (implies (and (symbol-alistp val)
                 (symbol-alist-listp (strip-cdrs alist)))
            (symbol-alist-listp (strip-cdrs (acons-unique key val alist))))
   :hints (("Goal" :in-theory (enable acons-unique)))))

(local
 (defthm nat-listp-of-strip-cdars-of-acons-unique
   (implies (and (natp key)
                 (nat-listp (strip-cars alist)))
            (nat-listp (strip-cars (acons-unique key val alist))))
   :hints (("Goal" :in-theory (enable acons-unique)))))

;move?
;dup
;; (defthm alistp-of-lookup-equal
;;   (implies (all-alistp (strip-cdrs alist))
;;            (alistp (lookup-equal key alist)))
;;   :hints (("Goal" :in-theory (enable lookup-equal))))

;; (defthm all-alistp-of-strip-cdrs-of-acons-unique
;;   (implies (and (alistp val)
;;                 (all-alistp (strip-cdrs alist)))
;;            (all-alistp (strip-cdrs (acons-unique key val alist))))
;;   :hints (("Goal" :in-theory (enable acons-unique))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a list where each element is either a symbol (representing a
;; function) or a pair of symbols (representing a function and an "unguarded"
;; alias of that function [i.e., a logically equivalent function with a guard
;; of t]).
(defun fns-and-aliasesp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((entry (first x)))
      (and (or (symbolp entry)
               (and (symbol-listp entry)
                    (= 2 (len entry))))
           (fns-and-aliasesp (rest x))))))

(local
  (defthm fns-and-aliasesp-of-reverse-list
    (implies (fns-and-aliasesp x)
             (fns-and-aliasesp (reverse-list x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-fns-from-fns-and-aliases (fns-and-aliases)
  (declare (xargs :guard (fns-and-aliasesp fns-and-aliases)))
  (if (endp fns-and-aliases)
      nil
    (let ((entry (first fns-and-aliases)))
      (cons (if (consp entry)
                (car entry)
              entry)
            (get-fns-from-fns-and-aliases (rest fns-and-aliases))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return a list of the symbols arg1, arg2, ..., argn.
(defun numbered-args (n acc)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (natp n)))
  (if (zp n)
      acc
    (numbered-args (+ -1 n)
                   (cons (pack$ 'arg (nat-to-string n))
                         acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-arity-fn-call-alist-alist-aux (fns-and-aliases wrld acc)
  (declare (xargs :guard (and (fns-and-aliasesp fns-and-aliases)
                              (plist-worldp wrld)
                              (alistp acc)
                              (symbol-alist-listp (strip-cdrs acc)))))
  (if (endp fns-and-aliases)
      acc
    (let* ((entry (first fns-and-aliases))
           (fn (if (consp entry)
                   (car entry)
                 entry))
           (arity (fn-arity fn wrld))
           (call-args (numbered-args arity nil))
           (call (if (consp entry)
                     `(,(cadr entry) ,@call-args)
                   `(,fn ,@call-args)))
           (entry-for-arity (lookup-equal arity acc)) ;consider just assoc
           (new-entry-for-arity (acons fn call entry-for-arity)))
      (make-arity-fn-call-alist-alist-aux (rest fns-and-aliases)
                                          wrld
                                          (acons-unique arity new-entry-for-arity acc)))))

(local
 (defthm symbol-alist-listp-of-strip-cdrs-of-make-arity-fn-call-alist-alist-aux
   (implies (and (fns-and-aliasesp fns-and-aliases)
                 (plist-worldp wrld)
                 (alistp acc)
                 (symbol-alist-listp (strip-cdrs acc)))
            (symbol-alist-listp (strip-cdrs (make-arity-fn-call-alist-alist-aux fns-and-aliases wrld acc))))))

(local
 (defthm nat-listp-of-strip-cars-of-make-arity-fn-call-alist-alist-aux
   (implies (and (fns-and-aliasesp fns-and-aliases)
                 (plist-worldp wrld)
                 (alistp acc)
                 (nat-listp (strip-cars acc)))
            (nat-listp (strip-cars (make-arity-fn-call-alist-alist-aux fns-and-aliases wrld acc))))))

(local
 (defthm alistp-of-strip-cdrs-of-make-arity-fn-call-alist-alist-aux
   (implies (and (fns-and-aliasesp fns-and-aliases)
                 (plist-worldp wrld)
                 (alistp acc)
                 (symbol-alist-listp (strip-cdrs acc)))
            (alistp (make-arity-fn-call-alist-alist-aux fns-and-aliases wrld acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-arity-fn-call-alist-alist (fns-and-aliases wrld)
  (declare (xargs :guard (and (fns-and-aliasesp fns-and-aliases)
                              (plist-worldp wrld))))
  (make-arity-fn-call-alist-alist-aux (reverse-list fns-and-aliases) wrld nil))

(local
  (defthm nat-listp-of-strip-cars-of-make-arity-fn-call-alist-alist
    (implies (and (fns-and-aliasesp fns-and-aliases)
                  (plist-worldp wrld))
             (nat-listp (strip-cars (make-arity-fn-call-alist-alist fns-and-aliases wrld))))
    :hints (("Goal" :in-theory (enable make-arity-fn-call-alist-alist)))))

(local
  (defthm alistp-of-make-arity-fn-call-alist-alist
    (implies (and (fns-and-aliasesp fns-and-aliases)
                  (plist-worldp wrld))
             (alistp (make-arity-fn-call-alist-alist fns-and-aliases wrld)))
    :hints (("Goal" :in-theory (enable make-arity-fn-call-alist-alist)))))

(local
  (defthm consp-of-make-arity-fn-call-alist-alist
    (implies (and (fns-and-aliasesp fns-and-aliases)
                  (plist-worldp wrld))
             (equal (consp (make-arity-fn-call-alist-alist fns-and-aliases wrld))
                    (consp fns-and-aliases)))
    :hints (("Goal" :in-theory (enable make-arity-fn-call-alist-alist)))))

(local
 (defthm symbol-alist-listp-of-strip-cdrs-of-make-arity-fn-call-alist-alist
   (implies (and (fns-and-aliasesp fns-and-aliases)
                 (plist-worldp wrld))
            (symbol-alist-listp (strip-cdrs (make-arity-fn-call-alist-alist fns-and-aliases wrld))))
   :hints (("Goal" :in-theory (enable make-arity-fn-call-alist-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-alias-checking-theorems (fns-and-aliases wrld)
  (declare (xargs :guard (and (fns-and-aliasesp fns-and-aliases)
                              (plist-worldp wrld))))
  (if (endp fns-and-aliases)
      nil
    (let ((entry (first fns-and-aliases)))
      (if (consp entry)
          (let* ((fn (first entry))
                 (alias (second entry))
                 (formals (fn-formals fn wrld)))
            (cons `(thm
                    (equal (,fn ,@formals)
                           (,alias ,@formals)))
                  (make-alias-checking-theorems (rest fns-and-aliases) wrld)))
        (make-alias-checking-theorems (rest fns-and-aliases) wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;dup
(local
  (defthm not-<-of-maxelem-and--1-when-nat-listp
    (implies (and (nat-listp vals)
                  (consp vals))
             (not (< (maxelem vals) -1)))
    :hints (("Goal" :in-theory (enable nat-listp)))))

;dup
(local
  (defthm integerp-of-maxelem-and--1-when-nat-listp
    (implies (and (nat-listp vals)
                  (consp vals))
             (integerp (maxelem vals)))
    :hints (("Goal" :in-theory (enable nat-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns an encapsulate event.
;; TODO: Add a function to eval a dag.  See evaluate-test-case-aux.
;; TODO: Strengthen guards to require the interpreted-function-alist to always be complete wrt the built-in functions of the evaluator.
;; perhaps always include all the primitives - since we can't interpret them!
;; TODO: Disallow duplicates among the fns-and-aliases (ignoring any unguarded aliases).
(defun make-evaluator-simple-fn (suffix
                                 fns-and-aliases
                                 extra-guards-apply
                                 extra-guards-eval
                                 extra-guards-eval-list
                                 verify-guards
                                 wrld)
  (declare (xargs :guard (and (symbolp suffix)
                              (fns-and-aliasesp fns-and-aliases)
                              (consp fns-and-aliases)
                              ;; the extra-guards-XXX are translated terms
                              (booleanp verify-guards)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable rational-listp-when-nat-listp)))))
  (let* ((base-name (pack$ 'axe-evaluator- suffix))
         ;;maps arities to fn-call-alists.  a fn-call-alist maps fns to the expressions by which to evaluate them:
         (arity-fn-call-alist-alist (make-arity-fn-call-alist-alist fns-and-aliases wrld))
         (max-arity (maxelem (strip-cars arity-fn-call-alist-alist)))
         (apply-function-name (pack$ 'apply- base-name))
         (apply-function-to-quoted-args-name (pack$ 'apply- base-name '-to-quoted-args))
         (eval-function-name (pack$ 'eval- base-name))
         (eval-list-function-name (pack$ 'eval-list- base-name)))
    `(encapsulate ()

       (local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
       ;; These just check the correctness of the aliases:
       (local (progn ,@(make-alias-checking-theorems fns-and-aliases wrld)))

       ;; These speed up the proofs, by avoid the need for destructor elimination:
       (local (in-theory (enable consp-of-cdr-of-nth-when-all-myquotep
                                 consp-of-nth-when-all-myquotep)))

       (mutual-recursion

        ;; Returns (mv erp result) where RESULT is the result of applying FN to ARGS (not quoted unless by chance).
        ;; The ARGS are not expected to be quoted (unless they happen to be, by chance).
        ;; FN must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is returned.
        ;; WARNING: Keep in sync with ,apply-function-to-quoted-args-name.
        (defund ,apply-function-name (fn args interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :guard (and (or (symbolp fn)
                                          (pseudo-lambdap fn) ; should be closed
                                          )
                                      (true-listp args)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-apply)
                          :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 2 0))
                          :verify-guards nil ; optionally done below
                          ))
          (if (flambdap fn)
              (let* ((formals (lambda-formals fn))
                     (body (lambda-body fn))
                     (alist (pairlis$-fast formals args)))
                (,eval-function-name alist body interpreted-function-alist count))
            (let ((args-to-walk-down args)) ;why??
              (mv-let (known-functionp val)
                ;; Here we build in all the known functions:
                ,(make-apply-cases-for-arities-simple max-arity
                                                      arity-fn-call-alist-alist
                                                      nil ;quoted-argsp
                                                      t   ;innermost-callp
                                                      nil ;not tracing
                                                      ;;acc:
                                                      '(mv nil ;no known-functionp
                                                        nil))
                (if known-functionp
                    (mv (erp-nil) val)
                  ;;fn isn't one of the built-in functions, so try to interpret it
                  (let ((match (assoc-eq fn interpreted-function-alist)))
                    (if (not match)
                        (progn$ ;; (cw "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)~%" fn args ',base-name)
                                (mv `(:unknown-function ,fn) nil))
                      (let* ((fn-info (cdr match))
                             (formals (first fn-info))
                             (body (second fn-info))
                             (alist (pairlis$-fast formals args)) ;todo: optimize by passing two lists to walk down in parallel
                             )
                        ;; Evaluate the function's body with its formals bound to the actuals:
                        (,eval-function-name alist body interpreted-function-alist count)))))))))

        ;; Returns (mv erp result).
        ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is returned
        ;; the cdrs of the alist are never quoted?
        ;; all the variables in form must have bindings in alist -- TODO: Add to guard
        ;; returns the (unquoted) value
        (defund ,eval-function-name (alist form interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :guard (and (symbol-alistp alist) ;todo: must bind all free vars in form?
                                      (pseudo-termp form)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-eval)
                          :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form)))))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded nil)
            (cond ((variablep form) (mv (erp-nil) (lookup-eq form alist))) ;; TODO: Error if the var is not bound?
                  ((fquotep form) (mv (erp-nil) (unquote form))) ;the value returned is unquoted
                  (t (let ((fn (ffn-symb form)))
                       ;;special handling for if (TODO: Consider adding support for boolif, bvif, maybe booland/boolor)
                       (if (and (or (eq fn 'if)
                                    (eq fn 'myif))
                                (consp (cdr (cdr (fargs form)))))
                           ;; Evaluate the test and then either the then-branch or the else-branch, according to the test:
                           (b* ((test-form (second form))
                                ((mv erp test-result)
                                 (,eval-function-name alist test-form interpreted-function-alist count))
                                ((when erp) (mv erp nil)))
                             (,eval-function-name alist
                                                  (if test-result ;if the test is not nil
                                                      (third form) ;then part
                                                    (fourth form)  ;else part
                                                    )
                                                  interpreted-function-alist
                                                  count))
                         ;; not an if, so evalate all arguments and then apply the function (which may be a lambda):
                         (b* (((mv erp args)
                               (,eval-list-function-name alist (fargs form) interpreted-function-alist count))
                              ((when erp) (mv erp nil)))
                           (,apply-function-name fn args interpreted-function-alist (+ -1 count)))))))))

        ;; Returns (mv erp result).
        ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is returned
        ;; the cdrs of the alist are never quoted?
        ;; all the variables in form-lst must have bindings in alist
        ;; returns the (unquoted) list of values
        (defund ,eval-list-function-name (alist form-lst interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :guard (and (symbol-alistp alist)
                                      (pseudo-term-listp form-lst)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-eval-list)
                          :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form-lst)))))
          (if (endp form-lst) ; todo: could use null but would complicate rules?
              (mv (erp-nil) nil)
            (b* (((mv erp car-res)
                  (,eval-function-name alist (car form-lst) interpreted-function-alist count))
                 ((when erp) (mv erp nil))
                 ((mv erp cdr-res)
                  (,eval-list-function-name alist (cdr form-lst) interpreted-function-alist count))
                 ((when erp) (mv erp nil)))
              (mv (erp-nil)
                  (cons car-res cdr-res)))))
        ) ;end mutual-recursion


       (defthm ,(pack$ 'true-listp-of-mv-nth-1-of- eval-list-function-name)
         (true-listp (mv-nth 1 (,eval-list-function-name alist forms interpreted-function-alist count)))
         :hints (("Goal" :induct (true-listp forms) :in-theory (enable true-listp ,eval-list-function-name))))

       ,@(and verify-guards
              `((verify-guards ,apply-function-name
                  :hints (("Goal" :in-theory (enable pseudo-termp-of-caddr-of-assoc-equal-when-interpreted-function-alistp
                                                     symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                                     cddr-of-assoc-equal-when-interpreted-function-alistp
                                                     true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                                     consp-of-cdr-of-assoc-equal-when-interpreted-function-alistp
                                                     consp-of-cddr-of-assoc-equal-when-interpreted-function-alistp))))))

       ;; Returns (mv erp result).
       ;; The ARGS passed in to this version must all be quoted.
       ;; fn must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is returned
       ;; returns the (unquoted) value.
       ;; WARNING: Keep in sync with ,apply-function-name.
       (defund ,apply-function-to-quoted-args-name (fn args interpreted-function-alist)
         (declare (xargs :guard (and (or (symbolp fn)
                                         (pseudo-lambdap fn))
                                     (true-listp args)
                                     (all-myquotep args)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     ,@extra-guards-apply)
                         :verify-guards nil ; maybe done below
                         ))
         (if (flambdap fn)
             (let* ((formals (lambda-formals fn))
                    (body (lambda-body fn))
                    (alist (pairlis$-fast formals (unquote-list args))))
               (,eval-function-name alist body interpreted-function-alist *max-fixnum*))
           (let ((args-to-walk-down args)) ;why??
             (mv-let (known-functionp val)
               ;; Here we build in all the known functions:
               ,(make-apply-cases-for-arities-simple max-arity
                                              arity-fn-call-alist-alist
                                              t        ;quoted-argsp
                                              t        ;innermost-callp
                                              nil      ;not tracing
                                              ;;acc:
                                              '(mv nil ;no known-functionp
                                                   nil))
               (if known-functionp
                   (mv (erp-nil) val)
                 ;;fn isn't one of the built-in functions, so try to interpret it
                 (let ((match (assoc-eq fn interpreted-function-alist)))
                   (if (not match)
                       (progn$ ;; (cw "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)~%" fn args ',base-name)
                               (mv `(:unknown-function ,fn) nil))
                     (let* ((fn-info (cdr match))
                            (formals (first fn-info))
                            (body (second fn-info))
                            (alist (pairlis$-fast formals (unquote-list args))) ;could pass two lists to walk down in parallel?
                            )
                       ;; Evaluate the function's body with its formals bound to the actuals:
                       (,eval-function-name alist body interpreted-function-alist *max-fixnum*)))))))))

       ,@(and verify-guards
              `((verify-guards ,apply-function-to-quoted-args-name
                  :hints (("Goal" :in-theory (enable pseudo-termp-of-caddr-of-assoc-equal-when-interpreted-function-alistp
                                                     symbol-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                                     cddr-of-assoc-equal-when-interpreted-function-alistp
                                                     true-listp-of-cadr-of-assoc-equal-when-interpreted-function-alistp
                                                     consp-of-cdr-of-assoc-equal-when-interpreted-function-alistp
                                                     consp-of-cddr-of-assoc-equal-when-interpreted-function-alistp))))))

       ;; The list of all functions this evaluator knows about
       (defconst ,(pack$ '* base-name '-fns*)
         (append '(if myif) ;always built-in
                 ',(get-fns-from-fns-and-aliases fns-and-aliases))))))

(defmacro make-evaluator-simple (suffix ;a symbol
                                 fns-and-aliases
                                 &key
                                 (extra-guards-apply 'nil)
                                 (extra-guards-eval 'nil)
                                 (extra-guards-eval-list 'nil)
                                 (verify-guards 't))
  `(make-event
    (make-evaluator-simple-fn ',suffix
                              ,fns-and-aliases
                              ',extra-guards-apply
                              ',extra-guards-eval
                              ',extra-guards-eval-list
                              ',verify-guards
                              (w state))))

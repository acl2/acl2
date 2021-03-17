; A tool to make an evaluator for a set of functions.
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

;; A tool to make an evaluator for a set of functions.  Does not handle
;; embedded dags and does not know how to evaluate itself.  Uses a count to
;; ensure termination.  Returns an error flag as well as the result.

(include-book "make-evaluator-common")
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system) ;for unquote-list
(include-book "kestrel/utilities/erp" :dir :system) ;for erp-nil
(include-book "kestrel/utilities/myif" :dir :system) ;since we give it special treatment below
(include-book "kestrel/alists-light/pairlis-dollar-fast" :dir :system)
(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/alists-light/acons-unique" :dir :system)
(include-book "all-alistp")
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))

;; TODO: Consider adding special handling for BOOLIF and BVIF.

(defconst *max-fixnum* (+ -1 (expt 2 60)))

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

(defthm fns-and-aliasesp-of-reverse-list
  (implies (fns-and-aliasesp x)
           (fns-and-aliasesp (reverse-list x))))

(defun get-fns-from-fns-and-aliases (fns-and-aliases)
  (declare (xargs :guard (fns-and-aliasesp fns-and-aliases)))
  (if (endp fns-and-aliases)
      nil
    (let ((entry (first fns-and-aliases)))
      (cons (if (consp entry)
                (car entry)
              entry)
            (get-fns-from-fns-and-aliases (rest fns-and-aliases))))))

;; return a list of the symbols arg1, arg2, ..., argn.
(defun numbered-args (n acc)
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (natp n)))
  (if (zp n)
      acc
    (numbered-args (+ -1 n)
                   (cons (pack$ 'arg (nat-to-string n))
                         acc))))

;move?
;dup
(defthm alistp-of-lookup-equal
  (implies (all-alistp (strip-cdrs alist))
           (alistp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm all-alistp-of-strip-cdrs-of-acons-unique
  (implies (and (alistp val)
                (all-alistp (strip-cdrs alist)))
           (all-alistp (strip-cdrs (acons-unique key val alist))))
  :hints (("Goal" :in-theory (enable acons-unique))))

(defun make-arity-fn-call-alist-alist-aux (fns-and-aliases wrld acc)
  (declare (xargs :guard (and (fns-and-aliasesp fns-and-aliases)
                              (plist-worldp wrld)
                              (alistp acc)
                              (all-alistp (strip-cdrs acc)))))
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

(defun make-arity-fn-call-alist-alist (fns-and-aliases wrld)
  (declare (xargs :guard (and (fns-and-aliasesp fns-and-aliases)
                              (plist-worldp wrld))))
  (make-arity-fn-call-alist-alist-aux (reverse-list fns-and-aliases) wrld nil))

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

;; Returns an event.
;;this generates a mutually recursive set of defuns that evaluates functions and dags
;fixme make a simple version that doesn't use arrays or have any built-in functions other than the primitives?
;;we use that expression when we call the corresponding function
;i guess if we pass an interpreted fn we must also pass in any supporting fns - perhaps always include all the primitives - since we can't interpret them!
;ffixme since this no longer takes state we could use a macro instead of make-event
(defun make-evaluator-simple-fn (base-name ;a symbol
                                 fns-and-aliases
                                 extra-guards-apply
                                 extra-guards-eval
                                 extra-guards-eval-list
                                 verify-guards
                                 wrld)
  (declare (xargs :guard (fns-and-aliasesp fns-and-aliases)
                  :verify-guards nil ;todo
                  ))
  (let* ( ;;maps arities to fn-call-alists.  a fn-call-alist maps fns to the expressions by which to evaluate them:
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

        ;; Returns (mv erp result).
        ;; The ARGS passed in to this version are not expected to be quoted (unless they happen to be, by chance).
        ;; fn must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
        ;; returns the (unquoted) value
        (defund ,apply-function-name (fn args interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 2 0))
                          :verify-guards nil
                          :guard (and (or (symbolp fn)
                                          (pseudo-lambdap fn))
                                      (true-listp args)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-apply)))
          (if (consp fn) ;test for lambda
              (let* ((formals (second fn))
                     (body (third fn))
                     (alist ;(extend-alist formals args alist) ;i think this was overkill, since the
                      ;;formals for lambdas in ACL2 bind all the variables in the body.
                      ;;fffixme - but is that guaranteed?
                      (pairlis$-fast formals args)))
                (,eval-function-name alist body interpreted-function-alist count))
            (let ((args-to-walk-down args)) ;why??
              (mv-let (hit val)
                ,(make-apply-cases-for-arities max-arity
                                               arity-fn-call-alist-alist
                                               nil      ;quoted-argsp
                                               t        ;innermost-callp
                                               nil      ;not tracing
                                               ;;acc:
                                               '(mv nil ;no hit
                                                    nil))
                (if hit
                    (mv (erp-nil) val)
                  ;;fn isn't one of the built-in functions, so try to interpret it
                  (let ((match (assoc-eq fn interpreted-function-alist)))
                    (if (not match)
                        (progn$ ;; (cw "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)" fn args ',base-name)
                                (mv :unknown-function nil))
                      (let* ((fn-info (cdr match))
                             (formals (first fn-info))
                             (body (second fn-info))
                             (alist (pairlis$-fast formals args)) ;could pass two lists to walk down in parallel?
                             )
                        (,eval-function-name alist body interpreted-function-alist count)))))))))

        ;; Returns (mv erp result).
        ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
        ;; the cdrs of the alist are never quoted?
        ;; all the variables in form must have bindings in alist -- TODO: Add to guard
        ;; returns the (unquoted) value
        (defund ,eval-function-name (alist form interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form)))
                          :guard (and (symbol-alistp alist)
                                      (pseudo-termp form)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-eval)))
          (if (or (not (mbt (natp count)))
                  (= 0 count))
              (mv :count-exceeded nil)
            (cond ((variablep form) (mv (erp-nil) (lookup-eq form alist))) ;; TODO: Error if the var is not bound?
                  ((fquotep form)(mv (erp-nil) (unquote form))) ;the value returned is unquoted
                  (t (let ((fn (ffn-symb form)))
                       ;;special handling for if: fixme other kinds of if?!
                       (if (and (or (eq fn 'if)
                                    (eq fn 'myif)) ;bozo, consider handling bvif (different arity) as well? also boolif?
                                (= 3 (len (fargs form))))
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
                         ;;not an if, so evalate all arguments:
                         (b* (((mv erp args)
                               (,eval-list-function-name alist (fargs form) interpreted-function-alist count))
                              ((when erp) (mv erp nil)))
                           ;;regular function call:
                           (,apply-function-name fn
                                                 args
                                                 interpreted-function-alist (+ -1 count)))))))))

        ;; Returns (mv erp result).
        ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
        ;; the cdrs of the alist are never quoted?
        ;; all the variables in form-lst must have bindings in alist
        ;; returns the (unquoted) list of values
        (defund ,eval-list-function-name (alist form-lst interpreted-function-alist count)
          (declare (type (unsigned-byte 60) count)
                   (xargs :measure (make-ord 2 (+ 1 (nfix count)) (make-ord 1 1 (acl2-count form-lst)))
                          :guard (and (symbol-alistp alist)
                                      (pseudo-term-listp form-lst)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp count)
                                      ,@extra-guards-eval-list)))
          (if (endp form-lst) ;fixme could use null but would complicate rules?
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

       ;; Returns (mv erp result).
       ;; The ARGS passed in to this version must all be quoted.
       ;; fn must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
       ;; returns the (unquoted) value.
       (defund ,apply-function-to-quoted-args-name (fn args interpreted-function-alist)
         (declare (xargs :guard (and (or (symbolp fn)
                                         (pseudo-lambdap fn))
                                     (true-listp args)
                                     (all-myquotep args)
                                     (interpreted-function-alistp interpreted-function-alist)
                                     ,@extra-guards-apply)
                         :verify-guards nil))
         (if (consp fn) ;test for lambda
             (let* ((formals (second fn))
                    (body (third fn))
                    (alist ;(extend-alist formals args alist) ;i think this was overkill, since the
                     ;;formals for lambdas in ACL2 bind all the variables in the body.
                     ;;fffixme - but is that guaranteed?
                     (pairlis$-fast formals (unquote-list args))))
               (,eval-function-name alist body interpreted-function-alist *max-fixnum*))
           (let ((args-to-walk-down args)) ;why??
             (mv-let (hit val)
               ,(make-apply-cases-for-arities max-arity
                                              arity-fn-call-alist-alist
                                              t        ;quoted-argsp
                                              t        ;innermost-callp
                                              nil      ;not tracing
                                              ;;acc:
                                              '(mv nil ;no hit
                                                   nil))
               (if hit
                   (mv (erp-nil) val)
                 ;;fn isn't one of the built-in functions, so try to interpret it
                 (let ((match (assoc-eq fn interpreted-function-alist)))
                   (if (not match)
                       ;; Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call).
                       (mv :unknown-function nil)
                     (let* ((fn-info (cdr match))
                            (formals (first fn-info))
                            (body (second fn-info))
                            (alist (pairlis$-fast formals (unquote-list args))) ;could pass two lists to walk down in parallel?
                            )
                       (,eval-function-name alist body interpreted-function-alist *max-fixnum*)))))))))

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
                                                     consp-of-cddr-of-assoc-equal-when-interpreted-function-alistp
                                                     unsigned-byte-p ;todo
                                                     ))))


                (verify-guards ,apply-function-to-quoted-args-name
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

(defmacro make-evaluator-simple (base-name ;a symbol
                                 arity-fn-call-alist-alist
                                 &key
                                 (verify-guards 't)
                                 (extra-guards-apply 'nil)
                                 (extra-guards-eval 'nil)
                                 (extra-guards-eval-list 'nil))
  `(make-event
    (make-evaluator-simple-fn ',base-name
                              ,arity-fn-call-alist-alist
                              ',extra-guards-apply
                              ',extra-guards-eval
                              ',extra-guards-eval-list
                              ',verify-guards
                              (w state))))

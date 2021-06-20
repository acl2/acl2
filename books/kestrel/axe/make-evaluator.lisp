; A tool for making (non-simple) evaluators
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

;; This book defines the make-evaluator tool, which produces a custom evaluator
;; for terms with a given set of functions and perhaps with embedded DAGs.

;; See tests in evaluator-tests.lisp.

;; TODO: Consider calling magic-ev-fncall when the function is not one that is
;; known to the evaluator (I guess we would have to pass in state).  That could
;; let some of the more exotic functions be dropped from the list of functions
;; built in to the Axe evaluator.  Maybe even try just using magic-ev-fncall
;; and see how much it slows things down.  Note, however, that the evaluator is
;; also used to embed DAGs in terms, and we won't want to pass in state there...

;; TODO: Consider splitting the interpreted-function-alist by arities.
;; TODO: Consider not returning (mv hit val).  Instead, duplicate the code after the mv-let in each branch?

(include-book "kestrel/alists-light/acons-unique" :dir :system)
(include-book "dags")
(include-book "dag-arrays") ;for guards of GET-VALS-OF-ARGS-ARRAY
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/bv/bvif" :dir :system) ;built in to the evaluator
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "make-evaluator-common")

;dup in all-consp.lisp
(defun all-consp (x)
  (if (atom x)
      t
      (and (consp (first x))
           (all-consp (rest x)))))
(verify-guards all-consp)

;fixme if an acl2 function is given a fast body with mbe, perhaps this book should use it? or maybe not, because that would assume the guards...

;note that (quote . 3) satisfies quotep but cannot be unquoted! can we redo quoted things to use a single cons?

;; The eval-array maps nodenums to either nil (indicating that the node has not
;; been evaluated) or (cons <val> nil) indicating that the node evaluated to
;; <val>.  Because DAGs may be nested, we may need several such arrays, with
;; names distinguished by the depth.
(def-typed-acl2-array eval-arrayp (or (not val) (consp val)))

(defthm consp-of-aref1-when-eval-arrayp
  (implies (and (eval-arrayp eval-array-name eval-array array-len)
                (< index array-len)
                (natp index)
                )
           (iff (consp (aref1 eval-array-name eval-array index))
                (aref1 eval-array-name eval-array index)))
  :hints (("Goal" :use (:instance type-of-aref1-when-eval-arrayp
                                  (array-name eval-array-name)
                                  (array eval-array)
                                  (num-valid-nodes array-len))
           :in-theory (disable type-of-aref1-when-eval-arrayp))))

;extends the worklist with any args not done
;returns (mv nodenum-worklist worklist-extendedp)
(defun get-args-not-done-array (args eval-array-name eval-array worklist worklist-extendedp)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              (implies (not (all-consp args))
                                       (eval-arrayp eval-array-name eval-array (+ 1 (largest-non-quotep args))))
                              (all-natp worklist)
                              (booleanp worklist-extendedp))))
  (if (endp args)
      (mv worklist worklist-extendedp)
    (let ((arg (first args)))
      (if (or (consp arg) ;check for quotep
              (aref1 eval-array-name eval-array arg)) ;non-nil means the value is computed and wrapped in a cons
          ;;the arg is done:
          (get-args-not-done-array (cdr args)
                                   eval-array-name eval-array
                                   worklist worklist-extendedp)
        ;;the arg is not done:
        (get-args-not-done-array (cdr args)
                                 eval-array-name eval-array
                                 (cons arg worklist)
                                 t)))))

(defthm all-natp-of-mv-nth-0-of-get-args-not-done-array
  (implies (and (all-dargp args)
                (all-natp worklist))
           (all-natp (mv-nth 0 (get-args-not-done-array args eval-array-name eval-array worklist worklist-extendedp)))))

;assumes all args are done (and thus wrapped in a cons)
(defun get-vals-of-args-array (args eval-array-name eval-array)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              (implies (not (all-consp args))
                                       (eval-arrayp eval-array-name eval-array (+ 1 (largest-non-quotep args)))))))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (cons (if (consp arg)
                (unquote arg)
              (car (aref1 eval-array-name eval-array arg)) ;strip off the cons
              )
            (get-vals-of-args-array (rest args) eval-array-name eval-array)))))

;; ;record ops here might be a bit slow?
;; (defun pair-arities-with-calls (defuns-and-calls acc state)
;;   (declare (xargs :mode :logic))
;;   (if (endp defuns-and-calls)
;;       acc
;;     (let* ((defun-or-call (car defuns-and-calls))
;;            (fn (if (symbolp defun-or-call) defun-or-call (car defun-or-call)))
;;            (props (getprops fn 'current-acl2-world (w state)))
;;            (formals (if (not props)
;;                         (hard-error 'pair-arities-with-calls "Can't find a defun named ~x0." (list (cons #\0 fn)))
;;                       (lookup-eq 'formals props)))
;;            (formal-count (len formals))
;;            (call (if (symbolp defun-or-call)
;;                      (cons defun-or-call (make-var-names-aux 'arg 1 formal-count))
;;                    defun-or-call))
;;            (old-arity-calls (g formal-count acc))
;;            (new-arity-calls (cons call old-arity-calls))
;;            )
;;       (pair-arities-with-calls (cdr defuns-and-calls)
;;                                (s formal-count new-arity-calls acc)
;;                                state))))

;; (defun pair-arities-with-calls-new (calls acc)
;;   (declare (xargs :mode :logic))
;;   (if (endp calls)
;;       acc
;;     (let* ((call (car calls))
;;            ;(fn (ffn-symb defun-or-call))
;;            (formals (fargs call)) ;must be numbered args in order
;;            (formal-count (len formals))
;;            (old-arity-calls (g formal-count acc))
;;            (new-arity-calls (cons call old-arity-calls))
;;            (acc (s formal-count new-arity-calls acc))
;;            )
;;       (pair-arities-with-calls-new (cdr calls) acc))))

(defun empty-trace ()
  (declare (xargs :guard t))
  nil)

(defun enquote-list (items)
  (declare (xargs :guard t))
  (if (atom items)
      nil
    (cons (enquote (car items))
          (enquote-list (cdr items)))))

;adds an entry to arity-fn-call-alist-alist
(defun add-call-to-calls (fn arity expr arity-fn-call-alist-alist)
  (let* ((calls-for-arity (lookup arity arity-fn-call-alist-alist))
         (calls-for-arity (acons fn expr calls-for-arity))
         (arity-fn-call-alist-alist (acons-unique arity calls-for-arity arity-fn-call-alist-alist)))
    arity-fn-call-alist-alist))

;;this generates a mutually recursive set of defuns that evaluates functions and dags
;fixme make a simple version that doesn't use arrays or have any built-in functions other than the primitives?
;;we use that expression when we call the corresponding function
;i guess if we pass an interpreted fn we must also pass in any supporting fns - perhaps always include all the primitives - since we can't interpret them!
;ffixme since this no longer takes state we could use a macro instead of make-event
(defun make-evaluator-fn (base-name ;a symbol
                          arity-fn-call-alist-alist ;maps arities to fn-call-alists.  a fn-call-alist maps fns to the expressions by which to evaluate them
                          )
  (declare (xargs :guard (and (symbolp base-name)
                              (alistp arity-fn-call-alist-alist))
                  :verify-guards nil ; todo
                  ))
  (let* ((apply-function-name (pack$ 'apply- base-name))
         (apply-function-to-quoted-args-name (pack$ 'apply- base-name '-to-quoted-args))
         (eval-function-name (pack$ 'eval- base-name))
         (eval-list-function-name (pack$ 'eval-list- base-name))
         (dag-val-name (pack$ 'dag-val-with- base-name))
         (eval-dag-name (pack$ 'eval-dag-with- base-name))

         ;;we include the apply function itself as an evaluatable function! what about the eval functions?
         (arity-fn-call-alist-alist (add-call-to-calls apply-function-name 4 `(,apply-function-name arg1 arg2 arg3 array-depth) arity-fn-call-alist-alist))
         (arity-fn-call-alist-alist (add-call-to-calls dag-val-name 4 `(,dag-val-name arg1 arg2 arg3 (+ 1 array-depth)) arity-fn-call-alist-alist))
         (arity-fn-call-alist-alist (add-call-to-calls eval-dag-name 8 `(,eval-dag-name arg1 arg2 arg3 arg4 arg5 arg6 arg7 array-depth) arity-fn-call-alist-alist))

         ;;(arity-call-record (pair-arities-with-calls-new calls nil)) ;this digs definitions out of the state

         (max-arity (maxelem (strip-cars arity-fn-call-alist-alist)))
         )
    `(skip-proofs
      (progn
        ;;ffixme what would the termination argument be?  add a clock parameter?
        (mutual-recursion

         ;; The ARGS passed in to this version are not expected to be quoted (unless they happen to be, by chance).
         ;; fn must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
         ;; returns the (unquoted) value
         (defund ,apply-function-name (fn args interpreted-function-alist array-depth)
           (declare (xargs :measure 1 ;;ffixme bogus
                           :guard (and (or (symbolp fn)
                                           (pseudo-lambdap fn))
                                       (true-listp args)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (natp array-depth))))
           (if (consp fn) ;test for lambda
               (let* ((formals (second fn))
                      (body (third fn))
                      (alist (pairlis$-fast formals args)))
                 (,eval-function-name alist body interpreted-function-alist array-depth))
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
                     val
                   ;;fn isn't one of the built-in functions, so try to interpret it
                   (let ((match (assoc-eq fn interpreted-function-alist)))
                     (if (not match)
                         (er hard? ',apply-function-name "Unknown function: ~x0 applied to args ~x1.  Consider passing it as an interpreted function, or adding it to the list of built-ins for the evaluator ~x2.  (This error also occurs when a function appears with an incorrect number of arguments.)"
                             fn args ',base-name)
                       (let* ((fn-info (cdr match))
                              (formals (first fn-info))
                              (body (second fn-info))
                              (alist (pairlis$-fast formals args)) ;could pass two lists to walk down in parallel?
                              )
                         (,eval-function-name alist body interpreted-function-alist array-depth)))))))))

         ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
         ;; the cdrs of the alist are never quoted?
         ;; all the variables in form must have bindings in alist
         ;; returns the (unquoted) value
         (defund ,eval-function-name (alist form interpreted-function-alist array-depth)
           (declare (xargs :verify-guards nil
                           :guard (and (symbol-alistp alist)
                                       (pseudo-termp form)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (natp array-depth))))
           (cond ((variablep form) (lookup-eq form alist))
                 ((fquotep form) (unquote form)) ;the value returned is unquoted
                 (t (let ((fn (ffn-symb form)))
                      ;;special handling for if: fixme other kinds of if?!
                      (if (and (or (eq fn 'if)
                                   (eq fn 'myif)) ;bozo, consider handling bvif (different arity) as well? also boolif?
                               (= 3 (len (fargs form))))
                          (let* ((test-form (farg1 form))
                                 (test-result (,eval-function-name alist test-form interpreted-function-alist array-depth))
                                 )
                            (,eval-function-name alist
                                                 (if test-result ;if the test is not nil
                                                     (farg2 form) ;then part
                                                   (farg3 form)  ;else part
                                                   )
                                                 interpreted-function-alist array-depth))
                        ;;not an if, so evalate all arguments:
                        (let ((args (,eval-list-function-name alist (fargs form) interpreted-function-alist array-depth)))
                          ;;regular function call:
                          (,apply-function-name fn
                                                args
                                                interpreted-function-alist array-depth)))))))

         ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
         ;; the cdrs of the alist are never quoted?
         ;; all the variables in form-lst must have bindings in alist
         ;; returns the (unquoted) list of values
         (defund ,eval-list-function-name (alist form-lst interpreted-function-alist array-depth)
           (declare (xargs
                     :verify-guards nil
                     :measure (len form-lst) ;new
                     :guard (and (symbol-alistp alist)
                                 (pseudo-term-listp form-lst)
                                 (interpreted-function-alistp interpreted-function-alist)
                                 (natp array-depth))))
           (if (endp form-lst) ;fixme could use null but would complicate rules?
               nil
             (cons (,eval-function-name alist (car form-lst) interpreted-function-alist array-depth)
                   (,eval-list-function-name alist (cdr form-lst) interpreted-function-alist array-depth))))

         ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
         ;; the cdrs of the alist are never quoted?
         ;; all the variables in dag must have bindings in alist - do we check this?
         ;; returns the (unquoted) value of the top-node of the dag
         (defund ,dag-val-name (dag alist interpreted-function-alist array-depth)
           (declare (xargs :measure 0 ;ffixme
                           :guard (and (or (quotep dag)
                                           (and (pseudo-dagp dag)
                                                (< (len dag) 2147483646)) ;can't guarantee this, so perhaps we should check it (same for all args?)
                                           )
                                       (symbol-alistp alist)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (natp array-depth))))
           (if (quotep dag)
               (unquote dag)
             (let* ((top-nodenum (top-nodenum dag))
                    (dag-array-name (pack$ 'dag-array- array-depth '-for-dag-val))
                    (dag-array (make-into-array dag-array-name dag)) ; todo: call make-dag-into-array?
                    (eval-array-name (pack$ 'eval-array- array-depth '-for-dag-val))
                    (eval-array (make-empty-array eval-array-name (+ 1 top-nodenum))))
               (car ;strip off the cons
                (aref1 eval-array-name
                       (,eval-dag-name (list top-nodenum)
                                       dag-array-name
                                       dag-array
                                       alist
                                       eval-array-name
                                       eval-array
                                       interpreted-function-alist
                                       array-depth)
                       top-nodenum)))))

         ;;returns eval-array
         ;;very similar to evaluate-test-case-new-aux
         ;;tail recursive - redoes some analysis of nodes with unprocessed children, but maybe worth it since it's tail-recursive?
         ;; all functions to evaluate must be either built-in or passed in in interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
         ;; the cdrs of var-value-alist are never quoted?
         ;; all the variables in dag-lst must have bindings in alist - do we check this?
         ;; if an entry in eval-array is nil, that spot is not yet computed.  if it's (cons val nil), the value is val
         (defund ,eval-dag-name (nodenum-worklist dag-array-name dag-array var-value-alist eval-array-name
                                                 eval-array ;computed values are wrapped in cons
                                                 interpreted-function-alist array-depth)
           (declare (xargs :guard (and (nat-listp nodenum-worklist)
                                       (if (consp nodenum-worklist)
                                           (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenum-worklist)))
                                         t)
                                       (symbol-alistp var-value-alist)
                                       (symbolp eval-array-name)
                                       (if (consp nodenum-worklist)
                                           (eval-arrayp eval-array-name eval-array (+ 1 (maxelem nodenum-worklist)))
                                         t)
                                       (interpreted-function-alistp interpreted-function-alist)
                                       (natp array-depth))
                           :verify-guards nil))
           (if (endp nodenum-worklist)
               eval-array
             (let* ((nodenum (first nodenum-worklist))
                    (expr (aref1 dag-array-name dag-array nodenum)))
               (if (variablep expr)
                   (let ((value (lookup-eq-safe expr var-value-alist))) ;the -safe is new..
                     (,eval-dag-name (rest nodenum-worklist) dag-array-name dag-array var-value-alist
                                     eval-array-name
                                     (aset1 eval-array-name eval-array nodenum (cons value nil)) ;wraps the value in a cons to show that it's done
                                     interpreted-function-alist array-depth))
                 (let ((fn (car expr)))
                   (if (equal fn 'quote)
                       (let ((value (unquote expr)))
                         (,eval-dag-name (rest nodenum-worklist) dag-array-name dag-array var-value-alist
                                         eval-array-name
                                         (aset1 eval-array-name eval-array nodenum (cons value nil))
                                         interpreted-function-alist array-depth))
                     ;;function call or if
                     (let ((args (dargs expr)))
                       (if (or (eq 'if fn) ;maybe also bif? ;ffixme boolif!  but add a boolfix..
                               (eq 'myif fn)
                               (eq 'bvif fn))
                           ;;if it's an ITE, only evaluate the branch we need
                           (let* ((test (if (eq 'bvif fn)
                                            (second args)
                                          (first args)))
                                  (test-quotep (quotep test)) ;could we just check for a consp instead, since any cons must be a quote?

                                  (test-result (if test-quotep nil (aref1 eval-array-name eval-array test)))
                                  (test-done (or test-quotep
                                                 test-result)))
                             (if (not test-done)
                                 (,eval-dag-name (cons test nodenum-worklist) dag-array-name dag-array var-value-alist
                                                 eval-array-name eval-array
                                                 interpreted-function-alist array-depth)
                               ;;we know the result of the test, so handle the relevant branch
                               (let* ((test-val (if test-quotep
                                                    (unquote test)
                                                  (car test-result)))
                                      (relevant-branch (if (eq 'bvif fn)
                                                           (if test-val (third args) (fourth args))
                                                         (if test-val (second args) (third args))))
                                      (quotep-relevant-branch (quotep relevant-branch))
                                      (relevant-branch-result (if quotep-relevant-branch nil
                                                                (aref1 eval-array-name eval-array relevant-branch)))
                                      (relevant-branch-done (or quotep-relevant-branch
                                                                relevant-branch-result)))
                                 (if (not relevant-branch-done)
                                     (,eval-dag-name (cons relevant-branch nodenum-worklist)
                                                     dag-array-name dag-array var-value-alist
                                                     eval-array-name eval-array
                                                     interpreted-function-alist array-depth)
                                   ;; if the relevant branch has been computed, the value of the if/myif/bvif is just that branch,
                                   ;; except that for bvif we have to bvchop it - should we move this stuff up?
                                   (let* ((bvifp (eq fn 'bvif))
                                          (size (and bvifp (first args)))
                                          (size-quotep (and bvifp (quotep size))) ;use consp?
                                          (size-result (and bvifp (not size-quotep) (aref1 eval-array-name eval-array size)))
                                          (bvif-and-size-not-done (and bvifp
                                                                       (not (or size-quotep
                                                                                size-result)))))
                                     (if bvif-and-size-not-done
                                         (,eval-dag-name (cons size nodenum-worklist)
                                                         dag-array-name dag-array var-value-alist
                                                         eval-array-name eval-array
                                                         interpreted-function-alist array-depth)
                                       (let* ((relevant-branch-value (if quotep-relevant-branch
                                                                         (unquote relevant-branch)
                                                                       (car relevant-branch-result)))
                                              (value (if (eq fn 'bvif)
                                                         (bvchop (if size-quotep
                                                                     (unquote size)
                                                                   (car size-result))
                                                                 relevant-branch-value)
                                                       relevant-branch-value)))
                                         (,eval-dag-name (cdr nodenum-worklist) dag-array-name dag-array var-value-alist
                                                         eval-array-name
                                                         (aset1 eval-array-name eval-array nodenum (cons value nil))
                                                         interpreted-function-alist array-depth))))))))
                         ;;regular function call
                         (mv-let (nodenum-worklist worklist-extendedp)
                           (get-args-not-done-array args eval-array-name eval-array nodenum-worklist nil)
                           (if worklist-extendedp
                               (,eval-dag-name nodenum-worklist ;has been extended
                                               dag-array-name dag-array var-value-alist
                                               eval-array-name eval-array
                                               interpreted-function-alist array-depth)
                             ;;no args to compute, so call the function:
                             (let* ((arg-values (get-vals-of-args-array args eval-array-name eval-array))
                                    (value (,apply-function-name fn arg-values interpreted-function-alist array-depth)))
                               (,eval-dag-name (cdr nodenum-worklist) dag-array-name dag-array var-value-alist
                                               eval-array-name
                                               (aset1 eval-array-name eval-array nodenum (cons value nil))
                                               interpreted-function-alist array-depth)))))))))))))


        ;; The ARGS passed in to this version must all be quoted.
        ;; fn must be either built-in or passed in via interpreted-function-alist - otherwise, the return value is meaningless and an error is thrown
        ;; returns the (unquoted) value.
        (defund ,apply-function-to-quoted-args-name (fn args interpreted-function-alist array-depth)
          (declare (xargs :guard (and (or (symbolp fn)
                                          (pseudo-lambdap fn))
                                      (true-listp args)
                                      (all-myquotep args)
                                      (interpreted-function-alistp interpreted-function-alist)
                                      (natp array-depth))
                          :verify-guards nil))
          (if (consp fn) ;test for lambda
              (let* ((formals (second fn))
                     (body (third fn))
                     (alist (pairlis$-fast formals (unquote-list args)) ;optimize this?
                            ))
                (,eval-function-name alist body interpreted-function-alist array-depth))
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
                    val
                  ;;fn isn't one of the built-in functions, so try to interpret it
                  (let ((match (assoc-eq fn interpreted-function-alist)))
                    (if (not match)
                        (er hard? ',apply-function-to-quoted-args-name "Unknown function: ~x0 applied to args ~x1 (pass it as an interpreted function, or add to the list of built-ins, or check the arity of the call)."
                            fn args)
                      (let* ((fn-info (cdr match))
                             (formals (first fn-info))
                             (body (second fn-info))
                             (alist (pairlis$-fast formals (unquote-list args))) ;could pass two lists to walk down in parallel?
                             )
                        (,eval-function-name alist body interpreted-function-alist array-depth)))))))))))))

(defmacro make-evaluator (base-name ;a symbol
                          arity-fn-call-alist-alist)
  `(make-event
    (make-evaluator-fn ',base-name
                       ,arity-fn-call-alist-alist)))


;;this generates a mutually recursive set of defuns that evaluates functions and dags
;i guess if we pass an interpreted fn we must also pass in any supporting fns - perhaps always include all the primitives - since we can't interpret them!
;ffixme since this no longer takes state we could use a macro instead of make-event
;this one does tracing - so the functions return (mv value trace)
;i guess this doesn't work on functions whose recursive calls are within embedded dags?
;doesn't work with mutual recursion
;apply and eval are mutually recursive, but if eval is about to call apply on a function other than traced-fn, it just calls the non-traced version
;this requires that the non-tracing version of the same evalutor be submitted first?

(defun add-tracing-to-evaluator (base-name)
  (declare (xargs :guard (symbolp base-name)))
  (let* ((apply-function-name (pack$ 'apply- base-name))
         (apply-with-tracing-function-name (pack$ 'apply- base-name '-with-tracing))
         (eval-with-tracing-function-name (pack$ 'eval- base-name '-with-tracing))
         (eval-list-with-tracing-function-name (pack$ 'eval-list- base-name '-with-tracing)))
    ;;we're not interpeting any functions, so the evaluator is all we need:
    `(skip-proofs ;what would the termination argument be?
      (mutual-recursion

       ;;returns (mv val trace)
       ;;fn is the function we are tracing
       ;;some stuff above no longer has to handle tracing ffixme
       ;;interpreted-function-alist must at least contain an entry for fn - check that in a wrapper function?
       ;;fn should not be one of those built into the evaluator - check in a wrapper function? <- no longer an issue??
       (defund ,apply-with-tracing-function-name (fn args interpreted-function-alist)
         (declare (xargs :measure 1)) ;;bogus measure
         (let ((match (assoc-eq fn interpreted-function-alist)))
           (if (not match)
               (mv (hard-error ',apply-with-tracing-function-name "Attempt to trace function ~x0 without passing in its definition. (Pass it as an interpreted function, or add to the list of built-ins -- or add it to the list of functions not to trace)." (acons #\0 fn nil))
                   nil)
             (let* ((fn-info (cdr match))
                    (formals (first fn-info))
                    (body (second fn-info))
                    (alist (pairlis$ formals args)) ;could save consing and instead use two lists to walk down in parallel?
                    )
               (mv-let (result trace-lst)
                       (,eval-with-tracing-function-name alist body interpreted-function-alist fn)
                       (mv result
                           ;;ffixme record ops may be slow?!
                           (s :args args (s :result result (s :sub-traces trace-lst nil)))))))))

       ;;returns (mv val trace-lst)
       ;;this assumes that all the variables in form have bindings in alist
       ;;does not quote its result
       (defun ,eval-with-tracing-function-name (alist form interpreted-function-alist traced-fn)
         (declare (xargs :verify-guards nil
                         :guard (and (symbol-alistp alist)
                                     (pseudo-termp form))))
         (cond ((variablep form) (mv (lookup-eq-safe form alist) (empty-trace))) ;the safe is new
               ((fquotep form) (mv (unquote form) (empty-trace))) ;the value returned is unquoted
               (t (let ((fn (ffn-symb form)))
                    ;;special handling for if:
                    (if (or (eq fn 'if)
                            (eq fn 'myif)) ;fixme consider boolif and bvif
                        (let* ((test-form (second form)))
                          (mv-let (test-result test-trace-lst)
                                  (,eval-with-tracing-function-name alist test-form interpreted-function-alist traced-fn)
                                  (mv-let (then-or-else-result then-or-else-trace-lst)
                                          (,eval-with-tracing-function-name alist
                                                                            (if test-result ;if the test is not nil
                                                                                (third form) ;then part
                                                                              (fourth form) ;else part
                                                                              )
                                                                            interpreted-function-alist
                                                                            traced-fn)
                                          (mv then-or-else-result
                                              (append test-trace-lst then-or-else-trace-lst)))))
                      ;;non-if function or lambda:
                      ;;first evaluate the args:
                      (mv-let (args args-trace-lst)
                              (,eval-list-with-tracing-function-name alist (fargs form) interpreted-function-alist traced-fn)
                              (if (consp fn) ;it's a lambda application:
                                  (let* ((formals (second fn))
                                         (body (third fn))
                                         (alist (pairlis$ formals args)) ;would like to avoid this consing
                                         )
                                    (mv-let (value body-trace-lst)
                                            (,eval-with-tracing-function-name alist body interpreted-function-alist traced-fn)
                                            (mv value (append args-trace-lst body-trace-lst))))
                                ;;regular function call:
                                (if (not (eq fn traced-fn))
                                    (let ((value (,apply-function-name fn args
                                                                       interpreted-function-alist
                                                                       0)))
                                      (mv value args-trace-lst))
                                  ;;it's the function we are tracing:
                                  (mv-let (value body-trace)
                                          (,apply-with-tracing-function-name fn args interpreted-function-alist)
                                          (mv value (append args-trace-lst
                                                            (if body-trace
                                                                (list body-trace)
                                                              nil))))))))))))

       ;;returns (mv val-lst trace-lst)
       (defun ,eval-list-with-tracing-function-name (alist form-lst interpreted-function-alist traced-fn)
         (declare (xargs
                   :verify-guards nil
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp form-lst))))
         (if (endp form-lst)
             (mv nil nil)
           (mv-let (car-value car-trace-lst)
                   (,eval-with-tracing-function-name alist (car form-lst) interpreted-function-alist traced-fn)
                   (mv-let (cdr-value cdr-trace-lst)
                           (,eval-list-with-tracing-function-name alist (cdr form-lst) interpreted-function-alist traced-fn)
                           (mv (cons car-value cdr-value)
                               (append car-trace-lst cdr-trace-lst) ;can we save any consing here somehow?
                               )))))))))

;(make-event (add-tracing-to-evaluator 'len-evaluator nil))
;(apply-len-evaluator-with-tracing 'len '((a b c)) (make-interpreted-function-alist '(len) (w state)))

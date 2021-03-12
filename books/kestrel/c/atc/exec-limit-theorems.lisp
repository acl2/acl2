; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dynamic-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-exec-limit-theorems
  :parents (dynamic-semantics)
  :short "Theorems about the limit on the depth of the recursive calls of
          the big-step operational interpretive semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "If an execution terminates without exceeding the limit,
     any execution with a higher limit terminates
     terminates with the same results.
     This property is obvious, informally.")
   (xdoc::p
    "This can be formally proved by induction, of course.
     However, the statement involves two limit values
     (one greater than or equal than the other),
     and a plain induction on the execution function
     does not appear to work (which is not unexpected).
     A much trimmed down version of this works
     (somehow ACL2 modifies the induction scheme
     to also take the second limit into account),
     but the full example does not.
     The failed subgoals show that second limit appears unmodified
     in the premises that embody the induction hypotheses,
     while it should be instead decremented by one like the first limit.")
   (xdoc::p
    "In a case like this, the approach is to define a recursive function,
     or in this case a nest of mutually recursive functions,
     that take two limit values instead of one
     and that provide the kind of induction we want to perform on both.
     The exact result of these new functions normally would not matter,
     as just the recursive structure is important to the induction,
     but in this case the recursive structure depends on
     results of recursive calls in some cases
     (e.g. to execute a non-empty list of block items,
     we execute the first, and then execute the rest based on
     the results from the first.
     Thus, the simplest approach seems to copy the execution functions
     and add a second limit argument to them
     that is tested and decremented along with the first.
     This is not ideal, because every time the execution functions change
     these new induction functions must change accordingly;
     perhaps in the future we could generate the latter from the former.")
   (xdoc::p
    "The new functions give us the right induction:
     we use the flag macro generated from them by @(tsee defines).
     However, because of the aforementioned dependency of
     some recursive calls on the actual results,
     we will find subgoals with a mix of
     the execution functions and the new induction functions.
     However, by construction the two (sets of) functions are equal
     under the condition that the second limit is not smaller than the first.
     So we prove this equivalence, also by induction on the new functions.
     Those equivalences are used as rewrite rules in the main theorems
     (there is one main theorem for each execution function),
     and the main theorems are proved automatically
     by induction on the new functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are the new mutually recursive functions for the induction scheme.
; They do not need to be guard-verified, as their use is just logical.
; The only differences with the execution functions, aside from the names,
; is that we test for LIMIT1 besides LIMIT at the beginning of each,
; and that we decrement by one LIMIT1 alongside LIMIT in each recursive call.

(local
 (defines exec-induct
   :flag-local nil
   :verify-guards nil

   (define exec-expr-call-or-pure-induct (e compst fenv limit limit1)
     (b* (((when (or (zp limit) (zp limit1)))
           (mv (error :limit) (compustate-fix compst)))
          (e (expr-fix e)))
       (if (expr-case e :call)
           (b* ((e.args (expr-call->args e))
                (e.fun (expr-call->fun e))
                (args (exec-expr-pure-list e.args compst)))
             (value-list-result-case
              args
              :err (mv args.get (compustate-fix compst))
              :ok (exec-fun-induct e.fun args.get compst fenv
                                   (1- limit) (1- limit1))))
         (mv (exec-expr-pure e compst)
             (compustate-fix compst))))
     :measure (nfix limit))

   (define exec-expr-asg-induct (e compst fenv limit limit1)
     (b* (((when (or (zp limit) (zp limit1))) (error :limit))
          ((unless (expr-case e :binary))
           (error (list :expr-asg-not-binary (expr-fix e))))
          (op (expr-binary->op e))
          (left (expr-binary->arg1 e))
          (right (expr-binary->arg2 e))
          ((unless (binop-case op :asg))
           (error (list :expr-asg-not-asg op)))
          ((unless (expr-case left :ident))
           (error (list :expr-asg-left-not-var left)))
          (var (expr-ident->get left))
          ((mv val compst)
           (exec-expr-call-or-pure-induct right compst fenv
                                          (1- limit) (1- limit1))))
       (value-result-case
        val
        :err val.get
        :ok (write-var var val.get compst)))
     :measure (nfix limit))

   (define exec-fun-induct (fun args compst fenv limit limit1)
     (b* (((when (or (zp limit) (zp limit1)))
           (mv (error :limit) (compustate-fix compst)))
          (info (fun-env-lookup fun fenv))
          ((when (not info))
           (mv (error (list :function-undefined (ident-fix fun)))
               (compustate-fix compst)))
          ((fun-info info) info)
          (scope (init-scope info.params args)))
       (scope-result-case
        scope
        :err (mv scope.get (compustate-fix compst))
        :ok (b* ((frame (make-frame :function fun :scopes (list scope.get)))
                 (compst (push-frame frame compst))
                 ((mv val-opt compst)
                  (exec-stmt-induct info.body compst fenv
                                    (1- limit) (1- limit1)))
                 (compst (pop-frame compst)))
              (value-option-result-case
               val-opt
               :err (mv val-opt.get compst)
               :ok (if val-opt.get
                       (mv val-opt.get compst)
                     ;; (if (equal (type-of-value val-opt.get)
                     ;;            (type-name-to-type
                     ;;             (make-tyname :specs info.result
                     ;;                          :pointerp nil)))
                     ;;     (mv val-opt.get compst)
                     ;;   (mv (error (list :return-value-mistype
                     ;;                    :required info.result
                     ;;                    :supplied (type-of-value
                     ;;                               val-opt.get)))
                     ;;       compst))
                     (mv (error (list :no-return-value (ident-fix fun)))
                         compst))))))
     :measure (nfix limit))

   (define exec-stmt-induct (s compst fenv limit limit1)
     (b* (((when (or (zp limit) (zp limit1)))
           (mv (error :limit) (compustate-fix compst)))
          (s (stmt-fix s)))
       (stmt-case
        s
        :labeled (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :compound (b* ((compst (enter-scope compst))
                       ((mv value? compst)
                        (exec-block-item-list-induct s.items compst fenv
                                                     (1- limit) (1- limit1))))
                    (mv value? (exit-scope compst)))
        :expr (b* ((compst/error (exec-expr-asg-induct s.get compst fenv
                                                       (1- limit) (1- limit1)))
                   ((when (errorp compst/error))
                    (mv compst/error (compustate-fix compst))))
                (mv nil compst/error))
        :null (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :if (b* ((test (exec-expr-pure s.test compst)))
              (value-result-case
               test
               :ok (if (ucharp test.get)
                       (mv (error (list :exec-if-uchar-todo s))
                           (compustate-fix compst))
                     (if (sint-nonzerop test.get)
                         (exec-stmt-induct s.then compst fenv
                                           (1- limit) (1- limit1))
                       (mv nil (compustate-fix compst))))
               :err (mv test.get (compustate-fix compst))))
        :ifelse (b* ((test (exec-expr-pure s.test compst)))
                  (value-result-case
                   test
                   :ok (if (ucharp test.get)
                           (mv (error (list :exec-if-uchar-todo s))
                               (compustate-fix compst))
                         (if (sint-nonzerop test.get)
                             (exec-stmt-induct s.then compst fenv
                                               (1- limit) (1- limit1))
                           (exec-stmt-induct s.else compst fenv
                                             (1- limit) (1- limit1))))
                   :err (mv test.get (compustate-fix compst))))
        :switch (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :while (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :dowhile (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :for (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :goto (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :continue (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :break (mv (error (list :exec-stmt s)) (compustate-fix compst))
        :return (if (exprp s.value)
                    (b* (((mv retval compst)
                          (exec-expr-call-or-pure-induct s.value
                                                         compst
                                                         fenv
                                                         (1- limit)
                                                         (1- limit1))))
                      (value-result-case
                       retval
                       :err (mv retval.get compst)
                       :ok (mv retval.get compst)))
                  (mv nil (compustate-fix compst)))))
     :measure (nfix limit))

   (define exec-block-item-induct (item compst fenv limit limit1)
     :guard (and (> (compustate-frames-number compst) 0)
                 (> (compustate-top-frame-scopes-number compst) 1))
     (b* (((when (or (zp limit) (zp limit1)))
           (mv (error :limit) (compustate-fix compst))))
       (block-item-case
        item
        :declon (b* (((declon declon) item.get)
                     ((mv init compst)
                      (exec-expr-call-or-pure-induct declon.init compst fenv
                                                     (1- limit) (1- limit1)))
                     ((when (errorp init)) (mv init compst))
                     (var (declor->ident declon.declor))
                     (pointerp (declor->pointerp declon.declor))
                     (type (type-name-to-type
                            (make-tyname :specs declon.type
                                         :pointerp pointerp)))
                     ((unless (equal type (type-of-value init)))
                      (mv (error (list :decl-var-mistype var
                                       :required type
                                       :supplied (type-of-value init)))
                          compst))
                     (new-compst (create-var var init compst)))
                  (compustate-result-case
                   new-compst
                   :ok (mv (value-option-result-ok nil) new-compst.get)
                   :err (mv new-compst.get compst)))
        :stmt (exec-stmt-induct item.get compst fenv
                                (1- limit) (1- limit1))))
     :measure (nfix limit))

   (define exec-block-item-list-induct (items compst fenv limit limit1)
     (b* (((when (or (zp limit) (zp limit1)))
           (mv (error :limit) (compustate-fix compst)))
          ((when (endp items)) (mv nil (compustate-fix compst)))
          ((mv val? compst) (exec-block-item-induct (car items) compst fenv
                                                    (1- limit) (1- limit1)))
          ((when (value-option-result-case val? :err)) (mv val? compst))
          ((when (valuep val?)) (mv val? compst)))
       (exec-block-item-list-induct (cdr items) compst fenv
                                    (1- limit) (1- limit1)))
     :measure (nfix limit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the equivalence between the execution functions and the new ones.
; If LIMIT1 >= LIMIT, then clear LIMIT1 has no effect on the functions;
; it is just carried along with LIMIT, which affects the functions.

(local
 (defthm-exec-induct-flag

   (defthm exec-expr-call-or-pure-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-expr-call-or-pure-induct e compst fenv limit limit1)
                     (exec-expr-call-or-pure e compst fenv limit)))
     :flag exec-expr-call-or-pure-induct)

   (defthm exec-expr-asg-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-expr-asg-induct e compst fenv limit limit1)
                     (exec-expr-asg e compst fenv limit)))
     :flag exec-expr-asg-induct)

   (defthm exec-fun-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-fun-induct fun args compst fenv limit limit1)
                     (exec-fun fun args compst fenv limit)))
     :flag exec-fun-induct)

   (defthm exec-stmt-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-stmt-induct s compst fenv limit limit1)
                     (exec-stmt s compst fenv limit)))
     :flag exec-stmt-induct)

   (defthm exec-block-item-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-block-item-induct item compst fenv limit limit1)
                     (exec-block-item item compst fenv limit)))
     :flag exec-block-item-induct)

   (defthm exec-block-item-list-induct-rewrite
     (implies (and (natp limit1)
                   (natp limit)
                   (>= limit1 limit))
              (equal (exec-block-item-list-induct items compst fenv limit limit1)
                     (exec-block-item-list items compst fenv limit)))
     :flag exec-block-item-list-induct)

   :hints (("Goal" :in-theory (enable exec-expr-call-or-pure
                                      exec-expr-asg
                                      exec-fun
                                      exec-stmt
                                      exec-block-item
                                      exec-block-item-list
                                      exec-expr-call-or-pure-induct
                                      exec-expr-asg-induct
                                      exec-fun-induct
                                      exec-stmt-induct
                                      exec-block-item-induct
                                      exec-block-item-list-induct)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we prove the theorems of interest.
; If LIMIT1 >= LIMIT and execution with LIMIT does not return the limit error,
; then execution with LIMIT1 returns the same result as execution with LIMIT.
; We make them local because we re-introduce them just after,
; non-locally and redundantly,
; thus avoiding to also export the flag macro.

(local
 (defthm-exec-induct-flag

   (defthm exec-expr-call-or-pure-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (mv-nth 0 (exec-expr-call-or-pure e compst fenv limit))
                       (error :limit))))
      (equal (exec-expr-call-or-pure e compst fenv limit)
             (exec-expr-call-or-pure e compst fenv limit1)))
     :flag exec-expr-call-or-pure-induct)

   (defthm exec-expr-asg-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (exec-expr-asg e compst fenv limit)
                       (error :limit))))
      (equal (exec-expr-asg e compst fenv limit)
             (exec-expr-asg e compst fenv limit1)))
     :flag exec-expr-asg-induct)

   (defthm exec-fun-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (mv-nth 0 (exec-fun fun args compst fenv limit))
                       (error :limit))))
      (equal (exec-fun fun args compst fenv limit)
             (exec-fun fun args compst fenv limit1)))
     :flag exec-fun-induct)

   (defthm exec-stmt-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (mv-nth 0 (exec-stmt s compst fenv limit))
                       (error :limit))))
      (equal (exec-stmt s compst fenv limit)
             (exec-stmt s compst fenv limit1)))
     :flag exec-stmt-induct)

   (defthm exec-block-item-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (mv-nth 0 (exec-block-item item compst fenv limit))
                       (error :limit))))
      (equal (exec-block-item item compst fenv limit)
             (exec-block-item item compst fenv limit1)))
     :flag exec-block-item-induct)

   (defthm exec-block-item-list-limit
     (implies
      (and (natp limit)
           (natp limit1)
           (>= limit1 limit)
           (not (equal (mv-nth 0 (exec-block-item-list items compst fenv limit))
                       (error :limit))))
      (equal (exec-block-item-list items compst fenv limit)
             (exec-block-item-list items compst fenv limit1)))
     :flag exec-block-item-list-induct)

   :hints (("Goal" :in-theory (enable exec-expr-call-or-pure
                                      exec-expr-asg
                                      exec-fun
                                      exec-stmt
                                      exec-block-item
                                      exec-block-item-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm exec-expr-call-or-pure-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (mv-nth 0 (exec-expr-call-or-pure e compst fenv limit))
                    (error :limit))))
   (equal (exec-expr-call-or-pure e compst fenv limit)
          (exec-expr-call-or-pure e compst fenv limit1))))

(defthm exec-expr-asg-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (exec-expr-asg e compst fenv limit)
                    (error :limit))))
   (equal (exec-expr-asg e compst fenv limit)
          (exec-expr-asg e compst fenv limit1))))

(defthm exec-fun-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (mv-nth 0 (exec-fun fun args compst fenv limit))
                    (error :limit))))
   (equal (exec-fun fun args compst fenv limit)
          (exec-fun fun args compst fenv limit1))))

(defthm exec-stmt-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (mv-nth 0 (exec-stmt s compst fenv limit))
                    (error :limit))))
   (equal (exec-stmt s compst fenv limit)
          (exec-stmt s compst fenv limit1))))

(defthm exec-block-item-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (mv-nth 0 (exec-block-item item compst fenv limit))
                    (error :limit))))
   (equal (exec-block-item item compst fenv limit)
          (exec-block-item item compst fenv limit1))))

(defthm exec-block-item-list-limit
  (implies
   (and (natp limit)
        (natp limit1)
        (>= limit1 limit)
        (not (equal (mv-nth 0 (exec-block-item-list items compst fenv limit))
                    (error :limit))))
   (equal (exec-block-item-list items compst fenv limit)
          (exec-block-item-list items compst fenv limit1))))

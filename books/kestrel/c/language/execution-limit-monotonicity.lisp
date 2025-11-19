; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dynamic-semantics")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution-limit-monotonicity
  :parents (dynamic-semantics)
  :short "A monotonicity property of execution limits."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the execution of a construct with a certain limit
     does not return an error (for exhausting the limit or other reason),
     neither does the execution of the same construct with a larger limit
     (and with the same computation state and function environment of course),
     and in addition it returns the same non-error outcome.
     This is a form of monotonicity, which maps the numeric order of limit
     to a (non-explicated) ordering of error vs. non-error outcomes.")
   (xdoc::p
    "This is proved by induction, but since there are two limits involved,
     the induction schema of the execution functions does not work here.
     We need one that involves two limits,
     tested and decremented ``in parallel'',
     in the same way as the execution functions do for one limit.
     Since some of the recursive calls of the execution functions
     take as arguments results of previous recursive calls,
     the induction schema with two limits needs to return
     the same results as the execution functions.
     So we define the mutually recursive clique @(tsee exec-2limits)
     to be exactly like the mutually recursive clique @(tsee exec)
     but with two limits, handled in parallel, instead of one.")
   (xdoc::p
    "Using the induction scheme defined by @(tsee exec-2limits),
     we prove our desired theorems.
     But first, we need to prove that the execution functions with two limits
     return the same results as the normal execution functions,
     when one limits is the same as or larger than the other.
     This is because, in the proofs of our desired theorems,
     calls of the @(tsee exec-2limits) functions show up in subgoals,
     and thus we need to rewrite them away,
     to calls of the regular execution functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exec-2limits
  :short "Execution functions with two limits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines the induction schema described in
     @(see execution-limit-monotonicity).
     We do not bother verifying the guards or proving return theorems,
     because we only use this function logically."))

  (define exec-fun-2limits (fun args compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst)))
         (info (fun-env-lookup fun fenv))
         ((when (not info))
          (mv (error (list :function-undefined (ident-fix fun)))
              (compustate-fix compst)))
         ((fun-info info) info)
         (scope (init-scope info.params args))
         ((when (errorp scope)) (mv scope (compustate-fix compst)))
         (frame (make-frame :function fun :scopes (list scope)))
         (compst (push-frame frame compst))
         ((mv sval compst) (exec-block-item-list-2limits info.body
                                                         compst
                                                         fenv
                                                         (1- limit)
                                                         (1- limit1)))
         (compst (pop-frame compst))
         ((when (errorp sval)) (mv sval compst))
         (val? (stmt-value-case
                sval
                :none nil
                :return sval.value?))
         ((unless (equal (type-of-value-option val?)
                         (tyname-to-type info.result)))
          (mv (error (list :return-value-mistype
                           :required info.result
                           :supplied (type-of-value-option val?)))
              compst)))
      (mv val? compst))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-expr-2limits (e compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst))))
      (expr-case
       e
       :ident (mv (exec-ident e.get compst) (compustate-fix compst))
       :const (mv (exec-const e.get) (compustate-fix compst))
       :arrsub (b* (((unless (and (expr-purep e.arr)
                                  (expr-purep e.sub)))
                     (mv (error (list :arrsub-nonpure-arg (expr-fix e)))
                         (compustate-fix compst)))
                    ((mv arr compst)
                     (exec-expr-2limits
                      e.arr compst fenv (1- limit) (1- limit1)))
                    ((when (errorp arr)) (mv arr compst))
                    ((unless arr)
                     (mv (error (list :arrsub-void-expr e.arr)) compst))
                    ((mv sub compst)
                     (exec-expr-2limits
                      e.sub compst fenv (1- limit) (1- limit1)))
                    ((when (errorp sub)) (mv sub compst))
                    ((unless sub)
                     (mv (error (list :arrsub-void-expr e.sub)) compst)))
                 (mv (exec-arrsub arr sub compst) compst))
       :call (b* ((vals (exec-expr-pure-list e.args compst))
                  ((when (errorp vals)) (mv vals (compustate-fix compst)))
                  ((mv val? compst)
                   (exec-fun-2limits
                    e.fun vals compst fenv (1- limit) (1- limit1)))
                  ((when (errorp val?)) (mv val? compst)))
               (if val?
                   (mv (make-expr-value :value val? :object nil) compst)
                 (mv nil compst)))
       :member (b* (((mv str compst)
                     (exec-expr-2limits
                      e.target compst fenv (1- limit) (1- limit1)))
                    ((when (errorp str)) (mv str compst))
                    ((unless str)
                     (mv (error (list :member-void-expr (expr-fix e)))
                         compst)))
                 (mv (exec-member str e.name) compst))
       :memberp (b* (((mv str compst)
                      (exec-expr-2limits
                       e.target compst fenv (1- limit) (1- limit1)))
                     ((when (errorp str)) (mv str compst))
                     ((unless str)
                      (mv (error (list :memberp-void-expr (expr-fix e)))
                          compst)))
                  (mv (exec-memberp str e.name compst) compst))
       :postinc (mv (error (list :expression-not-supported (expr-fix e)))
                    (compustate-fix compst))
       :postdec (mv (error (list :expression-not-supported (expr-fix e)))
                    (compustate-fix compst))
       :preinc (mv (error (list :expression-not-supported (expr-fix e)))
                   (compustate-fix compst))
       :predec (mv (error (list :expression-not-supported (expr-fix e)))
                   (compustate-fix compst))
       :unary (b* (((mv arg compst)
                    (exec-expr-2limits
                     e.arg compst fenv (1- limit) (1- limit1)))
                   ((when (errorp arg)) (mv arg compst))
                   ((unless arg)
                    (mv (error (list :unary-void-expr e.arg)) compst)))
                (mv (exec-unary e.op arg compst) compst))
       :cast (b* (((mv arg compst)
                   (exec-expr-2limits
                    e.arg compst fenv (1- limit) (1- limit1)))
                  ((when (errorp arg)) (mv arg compst))
                  ((unless arg)
                   (mv (error (list :cast-void-expr e.arg)) compst)))
               (mv (exec-cast e.type arg) compst))
       :binary (cond
                ((and (binop-strictp e.op)
                      (binop-purep e.op))
                 (b* (((unless (and (expr-purep e.arg1)
                                    (expr-purep e.arg2)))
                       (mv (error (list :pure-strict-binary-nonpure-args
                                        (expr-fix e)))
                           (compustate-fix compst)))
                      ((mv arg1-eval compst)
                       (exec-expr-2limits
                        e.arg1 compst fenv (1- limit) (1- limit1)))
                      ((when (errorp arg1-eval)) (mv arg1-eval compst))
                      ((unless arg1-eval)
                       (mv (error (list :binary-void-expr e.arg1)) compst))
                      ((mv arg2-eval compst)
                       (exec-expr-2limits
                        e.arg2 compst fenv (1- limit) (1- limit1)))
                      ((when (errorp arg2-eval)) (mv arg2-eval compst))
                      ((unless arg2-eval)
                       (mv (error (list :binary-void-expr e.arg2)) compst)))
                   (mv (exec-binary-strict-pure e.op arg1-eval arg2-eval)
                       compst)))
                ((or (binop-case e.op :logand)
                     (binop-case e.op :logor))
                 (if (expr-purep e)
                     (mv (exec-expr-pure e compst) (compustate-fix compst))
                   (mv (error (list :nonstrict-binary-nonpure-args
                                    (expr-fix e)))
                       (compustate-fix compst))))
                ((binop-case e.op :asg)
                 (b* ((left (expr-binary->arg1 e))
                      (right (expr-binary->arg2 e))
                      (left-eval (exec-expr-pure left compst))
                      ((when (errorp left-eval))
                       (mv left-eval (compustate-fix compst)))
                      (left-eval (apconvert-expr-value left-eval))
                      ((when (errorp left-eval))
                       (mv left-eval (compustate-fix compst)))
                      (objdes (expr-value->object left-eval))
                      ((unless objdes)
                       (mv (error (list :not-lvalue left))
                           (compustate-fix compst)))
                      ((mv right-eval? compst)
                       (if (expr-case left :ident)
                           (exec-expr-2limits
                            right compst fenv (1- limit) (1- limit1))
                         (mv (exec-expr-pure right compst)
                             (compustate-fix compst))))
                      ((when (errorp right-eval?)) (mv right-eval? compst))
                      ((when (not right-eval?))
                       (mv (error (list :asg-void-expr right)) compst))
                      (right-eval right-eval?)
                      (right-eval (apconvert-expr-value right-eval))
                      ((when (errorp right-eval)) (mv right-eval compst))
                      (val (expr-value->value right-eval))
                      (compst/error (write-object objdes val compst))
                      ((when (errorp compst/error))
                       (mv compst/error compst))
                      (compst compst/error))
                   (mv (make-expr-value :value val :object nil) compst)))
                (t (mv (error (list :expression-not-supported (expr-fix e)))
                       (compustate-fix compst))))
       :otherwise
       (b* (((when (expr-purep e))
             (mv (exec-expr-pure e compst) (compustate-fix compst))))
         (mv (error (list :expression-not-supported (expr-fix e)))
             (compustate-fix compst)))))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-stmt-2limits (s compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst)))
         (s (stmt-fix s)))
      (stmt-case
       s
       :labeled (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :compound (b* ((compst (enter-scope compst))
                      ((mv sval compst)
                       (exec-block-item-list-2limits
                        s.items compst fenv (1- limit) (1- limit1))))
                   (mv sval (exit-scope compst)))
       :expr (b* (((mv eval compst)
                   (exec-expr-2limits s.get compst fenv (1- limit) (1- limit1)))
                  ((when (errorp eval)) (mv eval compst)))
               (mv (stmt-value-none) compst))
       :null (mv (stmt-value-none) (compustate-fix compst))
       :if (b* ((test (exec-expr-pure s.test compst))
                ((when (errorp test)) (mv test (compustate-fix compst)))
                (test (apconvert-expr-value test))
                ((when (errorp test)) (mv test (compustate-fix compst)))
                (test (expr-value->value test))
                (test (test-value test))
                ((when (errorp test)) (mv test (compustate-fix compst))))
             (if test
                 (exec-stmt-2limits s.then compst fenv (1- limit) (1- limit1))
               (mv (stmt-value-none) (compustate-fix compst))))
       :ifelse (b* ((test (exec-expr-pure s.test compst))
                    ((when (errorp test)) (mv test (compustate-fix compst)))
                    (test (apconvert-expr-value test))
                    ((when (errorp test)) (mv test (compustate-fix compst)))
                    (test (expr-value->value test))
                    (test (test-value test))
                    ((when (errorp test)) (mv test (compustate-fix compst))))
                 (if test
                     (exec-stmt-2limits
                      s.then compst fenv (1- limit) (1- limit1))
                   (exec-stmt-2limits
                    s.else compst fenv (1- limit) (1- limit1))))
       :switch (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :while (exec-stmt-while-2limits
               s.test s.body compst fenv (1- limit) (1- limit1))
       :dowhile (b* ((compst (enter-scope compst))
                     ((mv sval compst)
                      (exec-stmt-dowhile-2limits
                       s.body s.test compst fenv (1- limit) (1- limit1)))
                     ((when (errorp sval)) (mv sval (exit-scope compst)))
                     (compst (exit-scope compst)))
                  (mv sval compst))
       :for (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :goto (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :continue (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :break (mv (error (list :exec-stmt s)) (compustate-fix compst))
       :return (if (exprp s.value)
                   (b* (((mv eval? compst)
                         (exec-expr-2limits
                          s.value compst fenv (1- limit) (1- limit1)))
                        ((when (errorp eval?)) (mv eval? compst))
                        ((when (not eval?)) (mv (error (list :return-void-expr
                                                             s.value))
                                                compst))
                        (eval eval?)
                        (eval (apconvert-expr-value eval))
                        ((when (errorp eval)) (mv eval compst))
                        (val (expr-value->value eval)))
                     (mv (stmt-value-return val) compst))
                 (mv (stmt-value-return nil) (compustate-fix compst)))))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-stmt-while-2limits (test body compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst)))
         (test-eval (exec-expr-pure test compst))
         ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
         (test-eval (apconvert-expr-value test-eval))
         ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
         (test-val (expr-value->value test-eval))
         (continuep (test-value test-val))
         ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
         ((when (not continuep)) (mv (stmt-value-none) (compustate-fix compst)))
         ((mv sval compst)
          (exec-stmt-2limits body compst fenv (1- limit) (1- limit1)))
         ((when (errorp sval)) (mv sval compst))
         ((when (stmt-value-case sval :return)) (mv sval compst)))
      (exec-stmt-while-2limits test body compst fenv (1- limit) (1- limit1)))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-stmt-dowhile-2limits (body test compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst)))
         (compst (enter-scope compst))
         ((mv sval compst)
          (exec-stmt-2limits body compst fenv (1- limit) (1- limit1)))
         ((when (errorp sval)) (mv sval (exit-scope compst)))
         (compst (exit-scope compst))
         ((when (stmt-value-case sval :return)) (mv sval compst))
         (test-eval (exec-expr-pure test compst))
         ((when (errorp test-eval)) (mv test-eval compst))
         (test-eval (apconvert-expr-value test-eval))
         ((when (errorp test-eval)) (mv test-eval compst))
         (test-val (expr-value->value test-eval))
         (continuep (test-value test-val))
         ((when (errorp continuep)) (mv continuep compst))
         ((when (not continuep)) (mv (stmt-value-none) compst)))
      (exec-stmt-dowhile-2limits body test compst fenv (1- limit) (1- limit1)))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-initer-2limits (initer compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst))))
      (initer-case
       initer
       :single
       (b* (((mv eval compst)
             (exec-expr-2limits initer.get compst fenv (1- limit) (1- limit1)))
            ((when (errorp eval)) (mv eval compst))
            ((when (not eval))
             (mv (error (list :void-initializer (initer-fix initer)))
                 compst))
            (eval (apconvert-expr-value eval))
            ((when (errorp eval)) (mv eval compst))
            (val (expr-value->value eval))
            (ival (init-value-single val)))
         (mv ival compst))
       :list
       (b* ((vals (exec-expr-pure-list initer.get compst))
            ((when (errorp vals)) (mv vals (compustate-fix compst)))
            (ival (init-value-list vals)))
         (mv ival (compustate-fix compst)))))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-obj-declon-2limits (declon compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit))) (error :limit))
         ((mv var scspec tyname init?)
          (obj-declon-to-ident+scspec+tyname+init declon))
         ((unless (scspecseq-case scspec :none))
          (error :unsupported-storage-class-specifier))
         (type (tyname-to-type tyname))
         ((when (type-case type :array)) (error :unsupported-local-array))
         ((when (not init?)) (error :unsupported-no-initializer))
         (init init?)
         ((mv ival compst)
          (exec-initer-2limits init compst fenv (1- limit) (1- limit1)))
         ((when (errorp ival)) ival)
         (val (init-value-to-value type ival))
         ((when (errorp val)) val))
      (create-var var val compst))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-block-item-2limits (item compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst))))
      (block-item-case
       item
       :declon (b* ((new-compst
                     (exec-obj-declon-2limits
                      item.get compst fenv (1- limit) (1- limit1)))
                    ((when (errorp new-compst))
                     (mv new-compst (compustate-fix compst))))
                 (mv (stmt-value-none) new-compst))
       :stmt (exec-stmt-2limits item.get compst fenv (1- limit) (1- limit1))))
    :measure (+ (nfix limit1) (nfix limit)))

  (define exec-block-item-list-2limits (items compst fenv limit limit1)
    (b* (((when (or (zp limit1) (zp limit)))
          (mv (error :limit) (compustate-fix compst)))
         ((when (endp items)) (mv (stmt-value-none) (compustate-fix compst)))
         ((mv sval compst)
          (exec-block-item-2limits
           (car items) compst fenv (1- limit) (1- limit1)))
         ((when (errorp sval)) (mv sval compst))
         ((when (stmt-value-case sval :return)) (mv sval compst)))
      (exec-block-item-list-2limits
       (cdr items) compst fenv (1- limit) (1- limit1)))
    :measure (+ (nfix limit1) (nfix limit)))

  :hints (("Goal" :in-theory (enable o-p o-finp nfix fix o< zp)))

  :verify-guards nil

  :flag-local nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-2limits-to-exec
  :short "Equivalence of the execution functions with two limits
          to the normal execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see execution-limit-monotonicity) for motivation.")
   (xdoc::p
    "We leave these enabled so they can be used automatically
     in @(tsee exec-monotone)."))

  (defthm-exec-2limits-flag
    (defthm exec-fun-2limits-to-exec-fun
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-fun-2limits fun args compst fenv limit limit1)
                      (exec-fun fun args compst fenv limit)))
      :flag exec-fun-2limits)
    (defthm exec-expr-2limits-to-exec-expr
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-expr-2limits e compst fenv limit limit1)
                      (exec-expr e compst fenv limit)))
      :flag exec-expr-2limits)
    (defthm exec-stmt-2limits-to-exec-stmt
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-stmt-2limits s compst fenv limit limit1)
                      (exec-stmt s compst fenv limit)))
      :flag exec-stmt-2limits)
    (defthm exec-stmt-while-2limits-to-exec-stmt-while
      (implies (>= (nfix limit1) (nfix limit))
               (equal
                (exec-stmt-while-2limits test body compst fenv limit limit1)
                (exec-stmt-while test body compst fenv limit)))
      :flag exec-stmt-while-2limits)
    (defthm exec-stmt-dowhile-2limits-to-exec-stmt-dowhile
      (implies (>= (nfix limit1) (nfix limit))
               (equal
                (exec-stmt-dowhile-2limits body test compst fenv limit limit1)
                (exec-stmt-dowhile body test compst fenv limit)))
      :flag exec-stmt-dowhile-2limits)
    (defthm exec-initer-2limits-to-exec-initer
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-initer-2limits initer compst fenv limit limit1)
                      (exec-initer initer compst fenv limit)))
      :flag exec-initer-2limits)
    (defthm exec-obj-declon-2limits-to-exec-obj-declon
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-obj-declon-2limits declon compst fenv limit limit1)
                      (exec-obj-declon declon compst fenv limit)))
      :flag exec-obj-declon-2limits)
    (defthm exec-block-item-2limits-to-exec-block-item
      (implies (>= (nfix limit1) (nfix limit))
               (equal (exec-block-item-2limits item compst fenv limit limit1)
                      (exec-block-item item compst fenv limit)))
      :flag exec-block-item-2limits)
    (defthm exec-block-item-list-2limits-to-exec-block-item-list
      (implies (>= (nfix limit1) (nfix limit))
               (equal
                (exec-block-item-list-2limits items compst fenv limit limit1)
                (exec-block-item-list items compst fenv limit)))
      :flag exec-block-item-list-2limits)
    :hints (("Goal" :in-theory (enable exec-fun-2limits
                                       exec-expr-2limits
                                       exec-stmt-2limits
                                       exec-stmt-while-2limits
                                       exec-stmt-dowhile-2limits
                                       exec-initer-2limits
                                       exec-obj-declon-2limits
                                       exec-block-item-2limits
                                       exec-block-item-list-2limits
                                       exec-fun
                                       exec-expr
                                       exec-stmt
                                       exec-stmt-while
                                       exec-stmt-dowhile
                                       exec-initer
                                       exec-obj-declon
                                       exec-block-item
                                       exec-block-item-list
                                       nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-monotone
  :short "Monotonicity of the execution functions with respect to limits."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see execution-limit-monotonicity) for motivation.")
   (xdoc::p
    "we also disable the theorems in @(tsee exec-2limits-to-exec),
     now that they have served their purpose in the proof here."))

  (defthm-exec-2limits-flag
    (defthm exec-fun-limit-monotone
      (b* (((mv val? &) (exec-fun fun args compst fenv limit)))
        (implies (and (not (errorp val?))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-fun fun args compst fenv limit1)
                        (exec-fun fun args compst fenv limit))))
      :flag exec-fun-2limits
      :hints ('(:expand (exec-fun fun args compst fenv limit)
                :in-theory (enable exec-fun nfix))))
    (defthm exec-expr-limit-monotone
      (b* (((mv eval? &) (exec-expr e compst fenv limit)))
        (implies (and (not (errorp eval?))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-expr e compst fenv limit1)
                        (exec-expr e compst fenv limit))))
      :flag exec-expr-2limits
      :hints ('(:expand (exec-expr e compst fenv limit)
                :in-theory (enable exec-expr nfix))))
    (defthm exec-stmt-limit-monotone
      (b* (((mv sval &) (exec-stmt s compst fenv limit)))
        (implies (and (not (errorp sval))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-stmt s compst fenv limit1)
                        (exec-stmt s compst fenv limit))))
      :flag exec-stmt-2limits
      :hints ('(:expand (exec-stmt s compst fenv limit)
                :in-theory (enable exec-stmt nfix))))
    (defthm exec-stmt-while-limit-monotone
      (b* (((mv sval &) (exec-stmt-while test body compst fenv limit)))
        (implies (and (not (errorp sval))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-stmt-while test body compst fenv limit1)
                        (exec-stmt-while test body compst fenv limit))))
      :flag exec-stmt-while-2limits
      :hints ('(:expand (exec-stmt-while test body compst fenv limit)
                :in-theory (enable exec-stmt-while nfix))))
    (defthm exec-stmt-dowhile-limit-monotone
      (b* (((mv sval &) (exec-stmt-dowhile body test compst fenv limit)))
        (implies (and (not (errorp sval))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-stmt-dowhile body test compst fenv limit1)
                        (exec-stmt-dowhile body test compst fenv limit))))
      :flag exec-stmt-dowhile-2limits
      :hints ('(:expand (exec-stmt-dowhile body test compst fenv limit)
                :in-theory (enable exec-stmt-dowhile nfix))))
    (defthm exec-initer-limit-monotone
      (b* (((mv ival &) (exec-initer initer compst fenv limit)))
        (implies (and (not (errorp ival))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-initer initer compst fenv limit1)
                        (exec-initer initer compst fenv limit))))
      :flag exec-initer-2limits
      :hints ('(:expand (exec-initer initer compst fenv limit)
                :in-theory (enable exec-initer nfix))))
    (defthm exec-obj-declon-limit-monotone
      (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
        (implies (and (not (errorp compst1))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-obj-declon declon compst fenv limit1)
                        (exec-obj-declon declon compst fenv limit))))
      :flag exec-obj-declon-2limits
      :hints ('(:expand (exec-obj-declon declon compst fenv limit)
                :in-theory (enable exec-obj-declon nfix))))
    (defthm exec-block-item-limit-monotone
      (b* (((mv sval &) (exec-block-item item compst fenv limit)))
        (implies (and (not (errorp sval))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-block-item item compst fenv limit1)
                        (exec-block-item item compst fenv limit))))
      :flag exec-block-item-2limits
      :hints ('(:expand (exec-block-item item compst fenv limit)
                :in-theory (enable exec-block-item nfix))))
    (defthm exec-block-item-list-limit-monotone
      (b* (((mv sval &) (exec-block-item-list items compst fenv limit)))
        (implies (and (not (errorp sval))
                      (>= (nfix limit1) (nfix limit)))
                 (equal (exec-block-item-list items compst fenv limit1)
                        (exec-block-item-list items compst fenv limit))))
      :flag exec-block-item-list-2limits
      :hints ('(:expand (exec-block-item-list items compst fenv limit)
                :in-theory (enable exec-block-item-list nfix)))))

  (in-theory (disable exec-fun-limit-monotone
                      exec-expr-limit-monotone
                      exec-stmt-limit-monotone
                      exec-stmt-while-limit-monotone
                      exec-stmt-dowhile-limit-monotone
                      exec-initer-limit-monotone
                      exec-obj-declon-limit-monotone
                      exec-block-item-limit-monotone
                      exec-block-item-list-limit-monotone
                      exec-fun-2limits-to-exec-fun
                      exec-expr-2limits-to-exec-expr
                      exec-stmt-2limits-to-exec-stmt
                      exec-stmt-while-2limits-to-exec-stmt-while
                      exec-stmt-dowhile-2limits-to-exec-stmt-dowhile
                      exec-initer-2limits-to-exec-initer
                      exec-obj-declon-2limits-to-exec-obj-declon
                      exec-block-item-2limits-to-exec-block-item
                      exec-block-item-list-2limits-to-exec-block-item-list)))

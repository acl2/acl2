; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax-operations")
(include-book "../shallow/top")
(include-book "kestrel/alists-light/lookup-equal" :dir :system)

;; Supported transforms
(include-book "kestrel/apt/tailrec" :dir :system)
(include-book "kestrel/apt/simplify" :dir :system)
(include-book "kestrel/apt/isodata" :dir :system)
(include-book "kestrel/apt/restrict" :dir :system)
;; These is temporary until they are put in community books
(include-book "kestrel/apt/wrap-output" :dir :system)
(include-book "kestrel/apt/finite-difference" :dir :system)
(include-book "kestrel/apt/drop-irrelevant-params" :dir :system)
(include-book "kestrel/apt/rename-params" :dir :system)
;(include-book "flatten-params")

(define d-->s-type ((ty typep))
  :measure (type-count ty)
  :returns (r true-listp)
  (case (type-kind ty)
     (:boolean '(s-type-boolean))
     (:character '(s-type-character))
     (:string '(s-type-string))
     (:integer '(s-type-integer))
     (:set `(s-type-set ,(d-->s-type (type-set->element ty))))
     (:sequence `(s-type-sequence ,(d-->s-type (type-sequence->element ty))))
     (:map `(s-type-map ,(d-->s-type (type-map->domain ty))
                        ,(d-->s-type (type-map->range ty))))
     (:option `(s-type-option ,(d-->s-type (type-option->base ty))))
     (:defined `(s-type-ref ,(identifier->name (type-defined->name ty))))))

(define d-->s-literal ((lit literalp))
  ;:returns (r true-listp)
  (case (literal-kind lit)
    (:boolean (if (literal-boolean->value lit)
                  '(s-literal-true)
                '(s-literal-false)))
    (:character (literal-character->value lit))
    (:string (literal-string->value lit))
    (:integer (literal-integer->value lit))))

(define d-->s-unary-op ((op unary-opp))
  :returns (r symbolp)
  (case (unary-op-kind op)
    (:not 's-not)
    (:minus 's-negate)))

(define d-->s-binary-op ((op binary-opp))
  :returns (r symbolp)
  (case (binary-op-kind op)
    (:eq 's-equal)
    (:ne 's-notequal)
    (:gt 's-gt)
    (:ge 's-gte)
    (:lt 's-lt)
    (:le 's-lte)
    (:and 's-and)
    (:or 's-or)
    (:implies 's-implies)               ; NYI
    (:implied 's-implied)               ; NYI
    (:iff 's-iff)                       ; NYI
    (:add 's-plus)
    (:sub 's-minus)
    (:mul 's-times)
    (:div 's-div)
    (:rem 's-rem)))

(defconst *d-->s-fn-map*
  '(("some" . s-some)
    ("none" . s-none)
    ("empty" . s-literal-empty-seq)
    ("is_empty" . s-empty-p)
    ("first" . s-head)
    ("last" . s-last)
    ("head" . s-head)
    ("rest" . s-tail)
    ("tail" . s-tail)
    ("member" . s-member)
    ("remove_first" . s-remove-first)
    ("length" . s-length)                 ; ?
    ("string_length" . s-string-length)   ; ?
    ("append" . append)
    ))

(define d-->s-typed-vars ((tv-l typed-variable-listp))
  :returns (r alistp)
  (if (endp tv-l)
      ()
    (b* (((typed-variable tv) (car tv-l))
         ((identifier id) tv.name))
      (cons (list id.name (d-->s-type tv.type))
            (d-->s-typed-vars (cdr tv-l))))))

(defines d-->s-translate-expressions
  (define d-->s-expr ((e expressionp))
    :measure (expression-count e)
   ; :returns (r true-listp) ; actually returns a shallow form
    (case (expression-kind e)
      (:literal (d-->s-literal (expression-literal->get e)))
      (:variable `(s-var-ref ,(identifier->name (expression-variable->name e))))
      (:unary `(,(d-->s-unary-op (expression-unary->operator e))
                ,(d-->s-expr (expression-unary->operand e))))
      (:binary `(,(d-->s-binary-op (expression-binary->operator e))
                 ,(d-->s-expr (expression-binary->left-operand e))
                 ,(d-->s-expr (expression-binary->right-operand e))))
      (:if `(s-conditional ,(d-->s-expr (expression-if->test e))
                           ,(d-->s-expr (expression-if->then e))
                           ,(d-->s-expr (expression-if->else e))))
      (:when `(s-conditional ,(d-->s-expr (expression-when->test e)) ; s-conditional ? s-when
                             ,(d-->s-expr (expression-when->then e))
                             ,(d-->s-expr (expression-when->else e))))
      (:unless `(s-conditional ,(d-->s-expr (expression-unless->test e)) ; s-conditional ? s-unless
                               ,(d-->s-expr (expression-unless->then e))
                               ,(d-->s-expr (expression-unless->else e))))
      (:cond `(s-cond ,@(d-->s-branches (expression-cond->branches e))))  ; NYI
      (:call (let* ((fn-nm (identifier->name (expression-call->function e)))
                    (s-fn? (acl2::lookup-equal fn-nm *d-->s-fn-map*))
                    (types (expression-call->types e))
                    (s-args (d-->s-expr-list (expression-call->arguments e))))
               (if s-fn?
                   `(,s-fn? ,@s-args)
                 (if (and (equal fn-nm "add")
                          (= (len types) 1)) ; Already checked in static-semantics
                     (if (type-case (car types) :sequence)
                         `(s-cons ,@s-args)
                       `(s-insert ,@s-args)) ; (type-case (car types) :set)
                   `(s-call ,fn-nm ,@s-args)))))
      (:multi `(s-multi ,(d-->s-expr-list (expression-multi->arguments e)))) ; NYI?
      (:component `(s-multi-component ,(d-->s-expr (expression-component->multi e))
                                      ,(expression-component->index e)))       ; NYI
      (:bind (b* (((expression-bind binder) e)
                  (vt-pairs (d-->s-typed-vars binder.variables)))
               (if (and (consp vt-pairs)
                        (consp (car vt-pairs))
                        (null (consp (cdr vt-pairs))))
                   `(s-let ((,(caar vt-pairs) ,(d-->s-expr binder.value))) ; ignore the type?
                        ,(d-->s-expr binder.body))
                 `(s-mv-let ,(strip-cars vt-pairs) ,(d-->s-expr binder.value) ; NYI
                            ,(d-->s-expr binder.body)))))
      (:product-construct `(s-prod-make ,(identifier->name (expression-product-construct->type e))
                                        ,@(d-->s-expr-field-val-pairs (expression-product-construct->fields e))))
      (:product-field `(s-prod-field-get ,(identifier->name (expression-product-field->type e))
                                         ,(identifier->name (expression-product-field->field e))
                                         ,(d-->s-expr (expression-product-field->target e))))
      (:product-update `(s-prod-update ,(identifier->name (expression-product-update->type e))   ; NYI
                                       ,(d-->s-expr (expression-product-update->target e))
                                       ,@(d-->s-expr-field-val-pairs (expression-product-update->fields e))))
      (:sum-construct `(s-sum-construct ; NYI
                        ,(identifier->name (expression-sum-construct->type e))
                        ,(identifier->name (expression-sum-construct->alternative e))
                        ,@(d-->s-expr-field-val-pairs (expression-sum-construct->fields e))))
      (:sum-field `(s-sum-field ; NYI
                        ,(identifier->name (expression-sum-field->type e))
                        ,(identifier->name (expression-sum-field->alternative e))
                        ,(identifier->name (expression-sum-field->field e))
                        ,(d-->s-expr (expression-sum-field->target e))))
      (:sum-update `(s-sum-update ; NYI
                        ,(identifier->name (expression-sum-update->type e))
                        ,(identifier->name (expression-sum-update->alternative e))
                        ,(d-->s-expr (expression-sum-update->target e))
                        ,@(d-->s-expr-field-val-pairs (expression-sum-update->fields e))))
      (:sum-test `(s-sum-test ; NYI
                   ,(identifier->name (expression-sum-test->type e))
                   ,(identifier->name (expression-sum-test->alternative e))
                   ,(d-->s-expr (expression-sum-test->target e))))))
  (define d-->s-expr-list ((e-l expression-listp))
    :measure (expression-list-count e-l)
    :returns (r true-listp)
    (if (endp e-l)
        ()
      (cons (d-->s-expr (car e-l))
            (d-->s-expr-list (cdr e-l)))))
  (define d-->s-expr-field-val-pairs ((e-l initializer-listp))
    :measure (initializer-list-count e-l)
    ;; EM: these are generally supposed to be flattened---see shallow/function-tests.lisp
    ;; Changed return type alistp  to true-listp
    ;; and relocated a cons.
    :returns (r true-listp)
    (if (endp e-l)
        ()
      (cons (identifier->name (initializer->field (car e-l)))
            (cons (d-->s-expr (initializer->value (car e-l)))
                  (d-->s-expr-field-val-pairs (cdr e-l))))))
  (define d-->s-branches ((e-l branch-listp))
    :measure (branch-list-count e-l)
    :returns (r alistp)
    (if (endp e-l)
        ()
      (cons (cons (d-->s-expr (branch->condition (car e-l)))
                  (d-->s-expr (branch->action (car e-l))))
            (d-->s-branches (cdr e-l)))))
) ; translate-expressions

(define variable-names ((vars typed-variable-listp))
  :returns (names symbol-listp)
  (if (endp vars)
      ()
    (cons (intern-syndef (identifier->name (typed-variable->name (car vars))))
          (variable-names (cdr vars)))))

(define d-->a-expr ((d-tm expressionp))
  (translate-term (d-->s-expr d-tm)))

(define d-->a-type-name ((d-ty typep))
  :returns (nm symbolp)
  (let ((shallow-ty-tm (d-->s-type d-ty)))
    (if (valid-type-constructor-p shallow-ty-tm)
        (s-type-to-fty-name-symbol shallow-ty-tm)
      (er hard? 'obligations "illegal type term"))))

(define d-->s-field+type-pairs ((prs field-listp))
  :returns (r true-listp)
  (if (endp prs)
      ()
    (b* (((field fld) (car prs)))
        (cons (list (identifier->name fld.name)
                    (d-->s-type fld.type))
              (d-->s-field+type-pairs (cdr prs))))))

(define d-->s-sum-type-alternatives ((alts alternative-listp))
  :returns (r true-listp)
  (if (endp alts)
      ()
    (b* (((alternative alt) (car alts)))
      (cons `(,(identifier->name alt.name)
              ,(d-->s-field+type-pairs (type-product->fields alt.product)))
            (d-->s-sum-type-alternatives (cdr alts))))))

(define check-integer-satisyfing-pred (i restriction (j integerp))
  (if (and (integerp i)
           (integerp j))
      (+ i j)
    (if (case-match restriction
          (('s-call "circular_vertex_seq" &) t))
        ;; Until this can be expressed in grammar!
        '(s-cons (s-prod-make "point" "x" 0 "y" 0)
                 (s-literal-empty-seq))
      (if (case-match restriction
            (('s-call "closed_path_p" &) t))
          ;; Until this can be expressed in grammar!
          '(s-cons (s-prod-make "edge"
                                "p1" (s-prod-make "point" "x" 0 "y" 0)
                                "p2" (s-prod-make "point" "x" 0 "y" 0))
                   (s-literal-empty-seq))
        (if (case-match restriction
              (('s-call "polygon_vertices_p" &) t))
            ;; Until this can be expressed in grammar!
            '(s-cons (s-prod-make "point" "x" 0 "y" 0)
                     (s-cons (s-prod-make "point" "x" 1 "y" 0)
                             (s-cons (s-prod-make "point" "x" 0 "y" 1)
                                     (s-literal-empty-seq))))
          (if (case-match restriction
                (('s-call "polygon_edges_p" &) t))
              ;; Until this can be expressed in grammar!
              '(s-cons (s-prod-make "edge"
                                    "p1" (s-prod-make "point" "x" 0 "y" 0)
                                    "p2" (s-prod-make "point" "x" 1 "y" 0))
                       (s-cons (s-prod-make "edge"
                                            "p1" (s-prod-make "point" "x" 1 "y" 0)
                                            "p2" (s-prod-make "point" "x" 0 "y" 1))
                               (s-cons (s-prod-make "edge"
                                                    "p1" (s-prod-make "point" "x" 0 "y" 1)
                                                    "p2" (s-prod-make "point" "x" 0 "y" 0))
                                       (s-literal-empty-seq))))
            (if (case-match restriction
                  (('s-call "points2_p" &) t))
                ;; Until this can be expressed in grammar!
                '(s-cons (s-prod-make "point" "x" 1 "y" 0)
                         (s-cons (s-prod-make "point" "x" 0 "y" 1)
                                 (s-literal-empty-seq)))
              (if (case-match restriction
                    (('s-call "path_p" &) t))
                  ;; Until this can be expressed in grammar!
                  '(s-literal-empty-seq)
                '(s-literal-empty-seq)))))))
    ;; (progn$ (er std::hard? 'find-witness "Can't get witness from ~x0." restriction)
    ;;         0)
    ))

;; This is a stop-gap procedure before doing something more comprehensive
(define find-val-satisfying-pred (var restriction)
  (case-match restriction
    ;; (('natp !var)
    ;;  0)
    (('s-gt !var i)
     (check-integer-satisyfing-pred i restriction 1))
    (('s-gt i !var)
     (check-integer-satisyfing-pred i restriction -1))
    (('s-gte !var i)
     (check-integer-satisyfing-pred i restriction 0))
    (('s-gte i !var)
     (check-integer-satisyfing-pred i restriction 0))
    (('s-lt i !var)
     (check-integer-satisyfing-pred i restriction 1))
    (('s-lt !var i)
     (check-integer-satisyfing-pred i restriction -1))
    (('s-lte i !var)
     (check-integer-satisyfing-pred i restriction 0))
    (('s-lte !var i)
     (check-integer-satisyfing-pred i restriction 0))
    (('s-and c1 c2)
     (b* ((r1 (find-val-satisfying-pred var c1))
          (r2 (find-val-satisfying-pred var c2)))
       (if (and (integerp r1)
                (integerp r2))
           (min r1 r2)
         0)))
    (& (check-integer-satisyfing-pred nil restriction 0))))

(define find-witness (supertype var restriction)
  :ignore-ok t
  :irrelevant-formals-ok t
  (find-val-satisfying-pred var restriction))

(define d-->s-type-definition ((ty-def type-definitionp))
  :returns (r true-listp)
  (b* (((type-definition td) ty-def))
    (type-definer-case td.body
      (:product (b* (((type-product prod) td.body.get)
                     (prod-nm (identifier->name td.name))
                     (field+type-pairs (d-->s-field+type-pairs prod.fields))
                     (invariant? (and prod.invariant (d-->s-expr prod.invariant))))
                  `(make-product-type ,prod-nm
                                      ,@field+type-pairs
                                      ,@(if invariant? `(:invariant ,invariant?)
                                          ())
                                      ,@(if invariant?
                                            (case-match field+type-pairs
                                               (((field1 field1-type)) ; !! only special case for now !!
                                                `(:fixvals (,(find-witness field1-type
                                                                           `(s-var-ref ,field1)
                                                                           invariant?))))
                                               (& nil))
                                          ()))))
      (:sum (b* (((type-sum sum) td.body.get))
              `(make-sum-type ,(identifier->name td.name)
                              ,@(d-->s-sum-type-alternatives sum.alternatives))))
      (:subset (b* (((type-subset st) td.body.get)
                    (supertype (d-->s-type st.supertype))
                    (var (identifier->name st.variable))
                    (restriction (d-->s-expr st.restriction))
                    (witness (or st.witness
                                 (find-witness supertype `(s-var-ref ,var) restriction))))
                 `(make-subtype ,(identifier->name td.name)
                                ,supertype ,var ,restriction ,witness)))
      ;; :set :seq :map NYI?
      )))

(define d-->s-type-definitions ((fn-defs type-definition-listp))
  :returns (r true-listp)
  (if (endp fn-defs)
      ()
    (cons (d-->s-type-definition (car fn-defs))
          (d-->s-type-definitions (cdr fn-defs)))))

(define d-->s-type-recursions ((fn-defs type-definition-listp))
  :returns (r true-listp)
  `(s-types ,@(d-->s-type-definitions fn-defs)))

(define d-->s-quantifier ((q quantifierp))
  :returns (r symbolp)
  (case (quantifier-kind q)
    (:forall 's-forall)
    (:exists 's-exists)))

(define d-->s-function-definition ((fn-def function-definitionp))
  :returns (r true-listp)
  (b* (((function-definition fd) fn-def)
       ((function-header fh) fd.header))
    `(s-fun ,(identifier->name fh.name)
            :inputs  ,(d-->s-typed-vars fh.inputs)
            :outputs ,(d-->s-typed-vars fh.outputs)
            ,@(if fd.precondition `(:assumes ,(d-->s-expr fd.precondition))
                ())
            ,@(if fd.postcondition `(:ensures ,(d-->s-expr fd.postcondition))
                ())
            ,@(function-definer-case fd.definer
                (:regular `(:body ,(d-->s-expr fd.definer.body)
                            ,@(if fd.definer.measure
                                  `(:measure ,(d-->s-expr fd.definer.measure))
                                ())))
                (:quantified `(:defined-by (,(d-->s-quantifier fd.definer.quantifier)
                                            ,(d-->s-typed-vars fd.definer.variables)
                                            ,(d-->s-expr fd.definer.matrix))))))))

(define d-->s-function-definitions ((fn-defs function-definition-listp))
  :returns (r true-listp)
  (if (endp fn-defs)
      ()
    (cons (d-->s-function-definition (car fn-defs))
          (d-->s-function-definitions (cdr fn-defs)))))

(define d-->s-function-recursions ((fn-defs function-definition-listp))
  :returns (r true-listp)
  `(s-funs ,@(d-->s-function-definitions fn-defs)))

(define d-->s-function-headers ((fn-hdrs function-header-listp))
  :returns (r true-listp)
  (if (endp fn-hdrs)
      ()
    (b* (((function-header fh) (car fn-hdrs)))
      (cons `(s-function-header ,(identifier->name fh.name)
                                :inputs  ,(d-->s-typed-vars fh.inputs)
                                :outputs ,(d-->s-typed-vars fh.outputs))
            (d-->s-function-headers (cdr fn-hdrs))))))

(define d-->s-function-specifier ((fs function-specifierp))
  :returns (r true-listp)
  (function-specifier-case fs
    (:regular `(s-body ,(d-->s-expr fs.body)))
    (:quantified `(s-quant ,(d-->s-quantifier fs.quantifier)
                           ,(d-->s-typed-vars fs.variables)
                           ,(d-->s-expr fs.matrix)))
    (:input-output `(s-relation ,(d-->s-expr fs.relation)))))

; partial support for specifications initially:

;; (define d-->s-specification ((sp function-specificationp))
;;   :returns (r true-listp)
;;   (b* (((function-specification spc) sp))
;;     `(s-specification ,(identifier->name spc.name)
;;                       ,(d-->s-function-headers spc.functions)
;;                       ,(d-->s-function-specifier spc.specifier))))

(define d-->s-specification ((sp function-specificationp))
  :returns (r true-listp)
  (b* (((function-specification spc) sp)
       ((unless (function-specifier-case spc.specifier :input-output))
        (raise "Only input/output specifications are supported."))
       ((unless (= (len spc.functions) 1))
        (raise "An input/output specification may only constrain one function."))
       ((function-header fh) (car spc.functions))
       (spec-namestring (identifier->name spc.name))
       (fun-namestring (identifier->name fh.name))
       (inputs (d-->s-typed-vars fh.inputs))
       (outputs (d-->s-typed-vars fh.outputs))
       (relation
        (d-->s-expr (function-specifier-input-output->relation spc.specifier))))
    `(s-spec-in-out ,spec-namestring
                    :fun-namestring ,fun-namestring
                    :inputs ,inputs
                    :outputs ,outputs
                    :relation ,relation)))

(define d-->s-theorem ((thm theoremp))
  :returns (r true-listp)
  (b* (((theorem th) thm))
    `(s-theorem ,(identifier->name th.name)
                ,(d-->s-typed-vars th.variables)
                ,(d-->s-expr th.formula))))

(defthmd factoring-lemma
  (implies (acl2-numberp c)
           (equal (if a (+ b c) c)
                  (+ (if a b 0) c))))

(defthmd numberp-when-natp
  (implies (natp x)
           (acl2-numberp x)))

(defthmd numberp-when-integerp
  (implies (integerp x)
           (acl2-numberp x)))

;; Transformations go directly to acl2 rather than an intermediate

;; *d-s-transform-templates* is an alist that maps syntheto transform names to one or more
;; apt transformation templates.  The templates are instantiated by substituting strings
;; which represent syntheto transformation arguments (see abstract-syntax.lisp for specification of these).
;; The general case is a list of pairs of conditions and templates. The condition is a
;; boolean expression where a string is T if the corresponding transformation argument is
;; present and NIL otherwise. The generated event is a progn of all the instantiated
;; templates whose condition is T.
(defconst *d-s-transform-templates*
  '(("tail_recursion" (t acl2::simplify :enable (factoring-lemma numberp-when-natp numberp-when-integerp)
                                        :disable (endp)
                                        :must-simplify nil)
                      ("wrapper_name"
                       apt::tailrec :accumulator "new_parameter_name"
                                    :old-to-new-enable t
                                    :wrapper "make_wrapper?" :wrapper-name "wrapper_name")
                      ((not "wrapper_name")
                       apt::tailrec :accumulator "new_parameter_name"
                                    :old-to-new-enable t
                                    :wrapper "make_wrapper?"))
    ("simplify" acl2::simplify :thm-name "old_to_new_name"
                               :disable (syndef::|even| syndef::|odd| odd-is-oddp even-is-evenp)
                               :new-enable nil)
    ("rename_param" acl2::rename-params ("old" "new"))
    ("restrict" apt::restrict "predicate" :old-to-new-enable t)
    ;("remove_cdring")
    ;("flatten_param" acl2::flatten-params "new" :param "old")
    ("isomorphism" (t apt::isodata (("parameter" ("old_type" "new_type" "old_to_new" "new_to_old")))
                                   :old-to-new-enable t)
                   ("simplify" acl2::simplify :disable (syndef::|even| syndef::|odd| odd-is-oddp even-is-evenp))
                   ("new_parameter_name" acl2::rename-params ("parameter" "new_parameter_name")))
    ("wrap_output" (t acl2::wrap-output "wrap_function")
                   ("simplify" acl2::simplify
                              :disable (syndef::|even| syndef::|odd| odd-is-oddp even-is-evenp)
                              :new-enable nil))
    ("finite_difference" (t acl2::finite-difference "expression" "rules" :new-param-name "new_parameter_name"
                                                    :build-wrapper nil)
                         ("simplify" acl2::simplify :assumptions ((equal "new_parameter_name" "expression")
                                                                  "new_parameter_guard")
                                                    :simplify-guard t
                                                    :disable (syndef::|even| syndef::|odd| odd-is-oddp even-is-evenp)
                                                    ))
    ("drop_irrelevant_parameter" acl2::drop-irrelevant-params "parameter" :build-wrapper "make_wrapper?")))

(define lookup-transform-table ((transfm-name stringp))
  :returns (sb (alistp sb))
  (cdr (assoc-equal transfm-name *transform-argument-defaults-table*)))

(define get-transform-argument-value ((arg-val transform-argument-valuep) type)
  (transform-argument-value-case arg-val
     :identifier (let ((sym (intern-syndef (identifier->name arg-val.name))))
                   (if (and (consp type)
                            (equal (car type) 'old-type-identifier))
                       (type-name-to-pred sym)
                     sym))
     :identifier-list (translate-names (identifier-list-names arg-val.names))
     :term (d-->a-expr arg-val.get)
     :bool arg-val.val))

(define transform-arg-subst ((args transform-argument-listp) type-info)
  :returns (a alistp)
  (if (endp args)
      nil
    (b* ((r-val (transform-arg-subst (cdr args) type-info))
         ((transform-argument arg) (car args))
         (arg-name (identifier->name arg.name))
         (arg-value (get-transform-argument-value arg.value (and (alistp type-info)
                                                                  (cdr (assoc-equal arg-name type-info))))))
       (cons (cons arg-name arg-value)
             (if (and (equal arg-name "expression")
                      (acl2::pseudo-termp arg-value)
                      (member 'syndef::|count| (acl2::free-vars-in-term arg-value)))
                 ;; !! Todo: Compute this properly!
                 (cons (cons "new_parameter_guard" '(and (integerp syndef::|count|)
                                                         (not (< syndef::|count| 0))))
                       r-val)
               r-val)))))

(define eval-ground-boolean-term (b-tm)
  (if (atom b-tm)
      b-tm
    (case-match b-tm
      (('not r-b-tm)
       (not (eval-ground-boolean-term r-b-tm)))
      (('and r-b-tm1 r-b-tm2)
       (and (eval-ground-boolean-term r-b-tm1)
            (eval-ground-boolean-term r-b-tm2)))
      (('or r-b-tm1 r-b-tm2)
       (or (eval-ground-boolean-term r-b-tm1)
           (eval-ground-boolean-term r-b-tm2)))
      (& t))))

(define find-needed-transforms (guarded-transforms)
  (if (atom guarded-transforms)
      ()
    (b* (((cons this-guarded-transform r-guarded-transforms) guarded-transforms)
         (r-result (find-needed-transforms r-guarded-transforms)))
      (if (and (consp this-guarded-transform)
               (eval-ground-boolean-term (car this-guarded-transform)))
          (cons (cdr this-guarded-transform)
                r-result)
        r-result))))

(define add-names-to-transforms (base-transfms
                                 (old-fn-name symbolp)
                                 (new-fn-name symbolp)
                                 (i natp))
  (if (atom base-transfms)
      ()
    (b* (((cons this-base-transfm r-base-transfms) base-transfms)
         (target-fn-name (if (= i 0)
                             old-fn-name
                           (pack-1 new-fn-name "-" i)))
         (result-fn-name (if (null r-base-transfms)
                             new-fn-name
                           (pack-1 new-fn-name "-" (+ i 1))))
         (r-transfms (add-names-to-transforms r-base-transfms old-fn-name new-fn-name (+ i 1)))
         ((unless (and (true-listp this-base-transfm) ; Shouldn't happen
                       (> (len this-base-transfm) 0)))
          nil)
         ((cons apt-transform-name transfm-args)
          this-base-transfm)
         (this-transfm `(,apt-transform-name ,target-fn-name ,@transfm-args
                                             :new-name ,result-fn-name)))
      (cons this-transfm r-transfms))))

(verify-termination acl2::sublis-equal)

(define d-->s-transform ((transform transformp))
  (b* (((transform transfm) transform)
       (old-fn-name (intern-syndef (identifier->name transfm.old-function-name)))
       (new-fn-name (intern-syndef (identifier->name transfm.new-function-name)))
       (transfm-name transfm.transform-name)
       (template (assoc-equal transfm-name *d-s-transform-templates*))
       (type-info (assoc-equal transfm-name *transform-argument-table*))
       ((unless (and (consp template)
                     (> (len template) 1)))
        (er std::hard? 'd-->s-transform "Can't find transform info for transform ~x0." transfm-name))
       (default-subst `(,@(lookup-transform-table transfm-name)
                        ("old_to_new_name" . ,(pack-1 old-fn-name "_to_" new-fn-name))))
       (subst (append (transform-arg-subst transfm.arguments (cdr type-info))
                      default-subst))   ; Supplied args shadow defaults
       (substituted-template (acl2::sublis-equal subst (cdr template)))
       (transforms-needed (if (and (consp substituted-template)
                                   (consp (car substituted-template)))
                              (find-needed-transforms substituted-template)
                            (list substituted-template)))
       (transforms-with-fn-names (add-names-to-transforms transforms-needed old-fn-name new-fn-name 0)))
    (and (true-listp transforms-with-fn-names)                     ; should always be true
         `(progn ,@transforms-with-fn-names))))

(define d-->s-toplevel ((dfn toplevelp))
  :returns (r true-listp)
  (toplevel-case dfn
    (:type (d-->s-type-definition dfn.get))
    (:types (d-->s-type-definitions (type-recursion->definitions dfn.get)))
    (:function (d-->s-function-definition dfn.get))
    (:functions (d-->s-function-recursions (function-recursion->definitions dfn.get)))
    (:specification (d-->s-specification dfn.get))
    (:theorem (d-->s-theorem dfn.get))
    (:transform (d-->s-transform dfn.get))))

(define d-->s-toplevel-list ((dfns toplevel-listp))
  :returns (r true-list-listp)
  (cond ((endp dfns) nil)
        (t (cons (d-->s-toplevel (car dfns))
                 (d-->s-toplevel-list (cdr dfns))))))

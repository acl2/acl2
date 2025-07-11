; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "expressions")
(include-book "literal-evaluation")
(include-book "arithmetic-operations")
(include-book "tuple-operations")

(include-book "kestrel/number-theory/prime" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ value-expressions
  :parents (dynamic-semantics)
  :short "Value expressions and their evaluation."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some contexts, we need to denote values via expressions
     that can be readily evaluated without the need for a dynamic environment.
     Thus, we introduce a notion of value expressions,
     as the expressions that can be evaluated in that way.
     These include literals (to denote primitive values),
     arithmetic negation applied to signed literals
     (to denote negative signed values),
     tuple expressions whose components are value expressions,
     and struct expressions whose components are value expressions.")
   (xdoc::p
    "The representation of values by value expressions is not unique.
     For example, the same field value may be denoted by infinite literals
     whose numerals differ by the prime.")
   (xdoc::p
    "Along with expression values,
     we also define their evaluation to values.
     We also define an inverse, namely a mapping from values
     to expression values that evaluate to the values.
     We pick a ``minimal'' such mapping:
     with reference to the non-uniqueness example above,
     we pick the smallest numeral for a field literal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expression-valuep
  :short "Check if an expression is an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This means that the expression is one of the following:")
   (xdoc::ul
    (xdoc::li
     "A literal.")
    (xdoc::li
     "A unary expression with @('-') as operator
      and a signed literal as operand.")
    (xdoc::li
     "A unit expression.")
    (xdoc::li
     "A tuple expressions whose components are value expressions.")
    (xdoc::li
     "A struct expression whose components contain value expressions.")))

  (define expression-valuep ((expr expressionp))
    :returns (yes/no booleanp)
    (or (expression-case expr :literal)
        (and (expression-case expr :unary)
             (unop-case (expression-unary->op expr) :neg)
             (expression-case (expression-unary->arg expr) :literal)
             (literal-case (expression-literal->get (expression-unary->arg expr))
                           :signed))
        (expression-case expr :unit)
        (and (expression-case expr :tuple)
             (expression-list-valuep (expression-tuple->components expr)))
        (and (expression-case expr :struct)
             (struct-init-list-valuep (expression-struct->components expr))))
    :measure (expression-count expr))

  (define expression-list-valuep ((exprs expression-listp))
    :returns (yes/no booleanp)
    (or (endp exprs)
        (and (expression-valuep (car exprs))
             (expression-list-valuep (cdr exprs))))
    :measure (expression-list-count exprs))

  (define struct-init-valuep ((cinit struct-initp))
    :returns (yes/no booleanp)
    (expression-valuep (struct-init->expr cinit))
    :measure (struct-init-count cinit))

  (define struct-init-list-valuep ((cinits struct-init-listp))
    :returns (yes/no booleanp)
    (or (endp cinits)
        (and (struct-init-valuep (car cinits))
             (struct-init-list-valuep (cdr cinits))))
    :measure (struct-init-list-count cinits))

  ///

  (fty::deffixequiv-mutual expression-valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines value-expr-to-value
  :short "Value denoted by an expression value."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the expression value is a literal, we evaluate it.")
   (xdoc::p
    "If it is a unary expression,
     whose operator must be @('-') and whose operand must be a signed integer,
     there are two cases:
     (i) if the operand's numeral is the absolute value
     of the most negative value of the literal's type,
     the value is the most negative of that type;
     (ii) otherwise, we evaluate the literal and then we negate it.")
   (xdoc::p
    "If any of these evaluations fails, we return @('nil')."))

  (define value-expr-to-value ((expr expressionp) (curve curvep))
    :guard (expression-valuep expr)
    :returns (val value-resultp)
    (b* ((curve (curve-fix curve)))
      (expression-case
       expr
       :literal (b* ((val (eval-literal expr.get curve)))
                  (or val
                      (reserrf (list :eval-lit-fail expr.get))))
       :var/const (reserrf (impossible))
       :assoc-const (reserrf (impossible))
       :unary (b* (((unless (unop-case expr.op :neg))
                    (reserrf (impossible)))
                   ((unless (expression-case expr.arg :literal))
                    (reserrf (impossible)))
                   (lit (expression-literal->get expr.arg))
                   ((unless (literal-case lit :signed))
                    (reserrf (impossible)))
                   (size (literal-signed->size lit))
                   (val (literal-signed->val lit)))
                (cond ((and (bitsize-case size :8)
                            (= val (expt 2 7)))
                       (value-i8 ( - (expt 2 7))))
                      ((and (bitsize-case size :16)
                            (= val (expt 2 15)))
                       (value-i16 ( - (expt 2 15))))
                      ((and (bitsize-case size :32)
                            (= val (expt 2 31)))
                       (value-i32 ( - (expt 2 31))))
                      ((and (bitsize-case size :64)
                            (= val (expt 2 63)))
                       (value-i64 ( - (expt 2 63))))
                      ((and (bitsize-case size :128)
                            (= val (expt 2 127)))
                       (value-i128 ( - (expt 2 127))))
                      (t (b* ((lit-val (eval-literal lit curve))
                              ((unless lit-val)
                               (reserrf (list :eval-lit-fail lit))))
                           (op-neg lit-val curve)))))
       :binary (reserrf (impossible))
       :cond (reserrf (impossible))
       :unit (op-tuple-make nil)
       :tuple (b* (((okf vals)
                    (value-expr-list-to-value-list expr.components curve)))
                (op-tuple-make vals))
       :tuple-component (reserrf (impossible))
       :struct (reserrf :todo-struct)
       :struct-component (reserrf (impossible))
       :internal-call (reserrf (impossible))
       :external-call (reserrf (impossible))
       :static-call (reserrf (impossible))))
    :guard-hints (("Goal" :in-theory (enable expression-valuep)))
    :measure (expression-count expr))

  (define value-expr-list-to-value-list ((exprs expression-listp)
                                         (curve curvep))
    :guard (expression-list-valuep exprs)
    :returns (vals value-list-resultp)
    (b* (((when (endp exprs)) nil)
         ((okf val) (value-expr-to-value (car exprs) curve))
         ((okf vals) (value-expr-list-to-value-list (cdr exprs) curve)))
      (cons val vals))
    :measure (expression-list-count exprs))

  :prepwork
  ((local
    (in-theory
     (enable valuep-when-value-resultp-and-not-reserrp
             value-listp-when-value-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards value-expr-to-value
    :hints (("Goal" :in-theory (enable expression-valuep
                                       expression-list-valuep))))

  (fty::deffixequiv-mutual value-expr-to-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines value-to-value-expr
  :short "Value expression that denotes a given value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is inverse of @(tsee value-expr-to-value), as we plan to prove.
     More precisely, going from value to value expression
     and from there back to value yields the same value.
     Due to the non-uniqueness of expression values denoting values,
     the other inversion property does not hold in general.")
   (xdoc::p
    "We return @('nil') if the group value is a non-finite point.
     This should never happen, so we plan to revise this code eventually,
     after perhaps the definition of group value is updated
     to require finite points."))

  (define value-to-value-expr ((val valuep))
    :returns (expr expression-resultp)
    (value-case
     val
     :bool (expression-literal (literal-bool val.get))
     :u8 (expression-literal (make-literal-unsigned :val val.get
                                                    :size (bitsize-8)))
     :u16 (expression-literal (make-literal-unsigned :val val.get
                                                     :size (bitsize-16)))
     :u32 (expression-literal (make-literal-unsigned :val val.get
                                                     :size (bitsize-32)))
     :u64 (expression-literal (make-literal-unsigned :val val.get
                                                     :size (bitsize-64)))
     :u128 (expression-literal (make-literal-unsigned :val val.get
                                                      :size (bitsize-128)))
     :i8 (if (>= val.get 0)
             (expression-literal (make-literal-signed :val val.get
                                                      :size (bitsize-8)))
           (make-expression-unary
            :op (unop-neg)
            :arg (expression-literal (make-literal-signed :val (- val.get)
                                                          :size (bitsize-8)))))
     :i16 (if (>= val.get 0)
              (expression-literal (make-literal-signed :val val.get
                                                       :size (bitsize-16)))
            (make-expression-unary
             :op (unop-neg)
             :arg (expression-literal (make-literal-signed
                                       :val (- val.get)
                                       :size (bitsize-16)))))
     :i32 (if (>= val.get 0)
              (expression-literal (make-literal-signed
                                   :val val.get
                                   :size (bitsize-32)))
            (make-expression-unary
             :op (unop-neg)
             :arg (expression-literal (make-literal-signed
                                       :val (- val.get)
                                       :size (bitsize-32)))))
     :i64 (if (>= val.get 0)
              (expression-literal (make-literal-signed
                                   :val val.get
                                   :size (bitsize-64)))
            (make-expression-unary
             :op (unop-neg)
             :arg (expression-literal (make-literal-signed
                                       :val (- val.get)
                                       :size (bitsize-64)))))
     :i128 (if (>= val.get 0)
               (expression-literal (make-literal-signed
                                    :val val.get
                                    :size (bitsize-128)))
             (make-expression-unary
              :op (unop-neg)
              :arg (expression-literal (make-literal-signed
                                        :val (- val.get)
                                        :size (bitsize-128)))))
     :field (expression-literal (literal-field val.get))
     :group (if (eq (ecurve::point-kind val.get) :finite)
                (expression-literal
                 (literal-group (make-group-literal-affine
                                 :x (coordinate-explicit
                                     (ecurve::point-finite->x val.get))
                                 :y (coordinate-explicit
                                     (ecurve::point-finite->y val.get)))))
              (reserrf :infinite-point))
     :scalar (expression-literal (literal-scalar val.get))
     :address (expression-literal (literal-address val.get))
     :string (expression-literal (literal-string val.get))
     :tuple (b* (((okf exprs) (value-list-to-value-expr-list val.components)))
              (if (null exprs)
                  (expression-unit)
                (expression-tuple exprs)))
     :struct (b* (((okf inits)
                    (value-map-to-value-struct-init-list val.components)))
                (make-expression-struct :type val.type :components inits)))
    :measure (two-nats-measure (value-count val) 0))

  (define value-list-to-value-expr-list ((vals value-listp))
    :returns (exprs expression-list-resultp)
    (b* (((when (endp vals)) nil)
         ((okf expr) (value-to-value-expr (car vals)))
         ((okf exprs) (value-list-to-value-expr-list (cdr vals))))
      (cons expr exprs))
    :measure (two-nats-measure (value-list-count vals) 0))

  (define name+value-to-value-struct-init ((name identifierp) (val valuep))
    :returns (init struct-init-resultp)
    (b* (((okf expr) (value-to-value-expr val)))
      (make-struct-init :name name :expr expr))
    :measure (two-nats-measure (value-count val) 1))

  (define value-map-to-value-struct-init-list ((valmap value-mapp))
    :returns (inits struct-init-list-resultp)
    (b* ((valmap (value-map-fix valmap))
         ((when (omap::emptyp valmap)) nil)
         ((mv name val) (omap::head valmap))
         ((okf init) (name+value-to-value-struct-init name val))
         ((okf inits)
          (value-map-to-value-struct-init-list (omap::tail valmap))))
      (cons init inits))
    :measure (two-nats-measure (value-map-count valmap) 0))

  :prepwork
  ((local
    (in-theory
     (enable
      expressionp-when-expression-resultp-and-not-reserrp
      expression-listp-when-expression-list-resultp-and-not-reserrp
      struct-initp-when-struct-init-resultp-and-not-reserrp
      struct-init-listp-when-struct-init-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards value-to-value-expr)

  (fty::deffixequiv-mutual value-to-value-expr)

  (defret-mutual expressions-valuep-of-values-to-value-exprs
    (defret expression-valuep-of-value-to-value-expr
      (implies (not (reserrp expr))
               (expression-valuep expr))
      :fn value-to-value-expr)
    (defret expression-list-valuep-of-value-list-to-value-expr-list
      (implies (not (reserrp exprs))
               (expression-list-valuep exprs))
      :fn value-list-to-value-expr-list)
    (defret struct-init-valuep-of-name+value-to-value-struct-init
      (implies (not (reserrp init))
               (struct-init-valuep init))
      :fn name+value-to-value-struct-init)
    (defret struct-init-list-valuep-of-value-map-to-value-struct-init-list
      (implies (not (reserrp inits))
               (struct-init-list-valuep inits))
      :fn value-map-to-value-struct-init-list)
    :hints (("Goal" :in-theory (enable expression-valuep
                                       expression-list-valuep
                                       struct-init-valuep
                                       struct-init-list-valuep))
            '(:expand (value-map-to-value-struct-init-list valmap)))))

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

(include-book "files")
(include-book "static-environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-checking
  :parents (static-semantics)
  :short "Type checking of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type checking consists of the bulk of the static semantic requirements
     that must be satisfied by the Leo code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funparam-to-var/const-sinfo ((param funparamp))
  :returns (info var/const-sinfop)
  :short "Turn a function parameter into
          static information about the parameter as a variable or constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we treat public and private parameters as just variables,
     and we treat constant and const parameters as just constants.
     We may extend this in the future."))
  (b* (((funparam param) param)
       (constp (or (var/const-sort-case param.sort :constant)
                   (var/const-sort-case param.sort :const))))
    (make-var/const-sinfo :type param.type :constp constp))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection funparam-list-to-var/const-sinfo-list (x)
  :guard (funparam-listp x)
  :returns (infos var/const-sinfo-listp)
  :short "Lift @(tsee funparam-to-var/const-sinfo) to lists."
  (funparam-to-var/const-sinfo x)
  ///
  (fty::deffixequiv funparam-list-to-var/const-sinfo-list
    :args ((x funparam-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-fundecl ((decl fundeclp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add an entry for the function, if possible.
     We ignore the body of the function")
   (xdoc::p
    "This does not type-check the function declaration.
     It just incorporates it into the environment."))
  (b* (((fundecl decl) decl)
       (inputs (funparam-list-to-var/const-sinfo-list decl.inputs))
       (output decl.output)
       (info (make-function-sinfo :inputs inputs :output output))
       (new-env (add-function-sinfo decl.name info env))
       ((unless new-env)
        (reserrf (list :cannot-add-function decl.name (senv-fix env)))))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-structdecl ((decl structdeclp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a struct declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we build a finite map from identifiers to types
     from the struct component declarations,
     which we use to build the information about the struct type.
     Then we add an entry to the static environment
     for the struct type, unless its name is already in use."))
  (b* (((structdecl decl) decl)
       ((okf comps)
        (extend-type-map-with-compdecl-list decl.components nil))
       (info (make-struct-sinfo :components comps))
       (new-env (add-struct-sinfo decl.name info env))
       ((unless new-env)
        (reserrf (list :cannot-add-struct decl.name (senv-fix env)))))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-vardecl ((decl vardeclp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a variable declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add an entry for the variable, if possible.
     We ignore the initializing expression.")
   (xdoc::p
    "This does not type-check the variable declaration.
     It just incorporates it into the environment."))
  (b* (((vardecl decl) decl)
       (info (make-var/const-sinfo :type decl.type :constp nil))
       (new-env (add-var/const-sinfo decl.name info env))
       ((unless new-env)
        (reserrf (list :cannot-add-variable decl.name (senv-fix env)))))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-constdecl ((decl constdeclp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a constant declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add an entry for the constant, if possible.
     We ignore the initializing expression.")
   (xdoc::p
    "This does not type-check the constant declaration.
     It just incorporates it into the environment."))
  (b* (((constdecl decl) decl)
       (info (make-var/const-sinfo :type decl.type :constp t))
       (new-env (add-var/const-sinfo decl.name info env))
       ((unless new-env)
        (reserrf (list :cannot-add-constant decl.name (senv-fix env)))))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-topdecl ((decl topdeclp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a top-level declaration."
  (topdecl-case decl
                :function (extend-senv-with-fundecl decl.get env)
                :struct (extend-senv-with-structdecl decl.get env)
                ;; TODO: fix :mapping
                :mapping (reserrf :extend-senv-for-mapping-not-yet-implemented)
                )
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define extend-senv-with-topdecl-list ((decls topdecl-listp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Extend a static environment with a list of top-level declarations."
  (b* (((when (endp decls)) (senv-fix env))
       ((okf env) (extend-senv-with-topdecl (car decls) env)))
    (extend-senv-with-topdecl-list (cdr decls) env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-to-senv ((file filep))
  :returns (env senv-resultp)
  :short "Build a static environment from a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with the initial (empty) static environment,
     we extend it with all the top-level declarations in the file."))
  ;; TODO: consider imports
  (extend-senv-with-topdecl-list (programdecl->items (file->program file)) (init-senv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines typecheck-type
  :short "Type-check a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Types themselves are type-checked to be well-formed:
     a tuple type cannot have one component;
     and an identifier must refer to a struct type in scope.")
   (xdoc::p
    "If a type type-checks, no information needs to be returned."))

  (define typecheck-type ((type typep) (env senvp))
    :returns (ok reserr-optionp)
    (type-case
     type
     :bool nil
     :unsigned nil
     :signed nil
     :field nil
     :group nil
     :scalar nil
     :address nil
     :string nil
     :internal-named (b* ((info (get-struct-sinfo type.get env)))
                       (if info
                           nil
                         (reserrf (list :type-not-found type.get))))
     ;; TODO: fill out :external-named, and consider what to do with recordp
     ;; on :internal-named and :external-named
     :external-named nil
     :unit nil
     :tuple (b* (((okf &) (typecheck-type-list type.components env)))
              (if (equal (len type.components) 1)
                  (reserrf (list :one-tuple-type type.components))
                nil)))
    :measure (type-count type))

  (define typecheck-type-list ((types type-listp) (env senvp))
    :returns (ok reserr-optionp)
    (b* (((when (endp types)) nil)
         ((okf &) (typecheck-type (car types) env)))
      (typecheck-type-list (cdr types) env))
    :measure (type-list-count types))

  ///

  (fty::deffixequiv-mutual typecheck-type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-literal ((lit literalp))
  :returns (type type-resultp)
  :short "Type-check a literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the type of the literal if successful.")
   (xdoc::p
    "There are no requirements on
     boolean, address, field, scalar, and string literals.")
   (xdoc::p
    "An unsigned or signed literal must have a value in the range of the type.
     The special cases of the literals @('128u8'), @('32768u16'), etc.
     are not handled here, but rather when type-checking expressions;
     if we get here (i.e. to type-check a literal,
     it means that the case has not been already handled,
     and therefore we must reject those special literals:
     they are not operands of unary @('-')
     (because if they did, they would have been already handled
     and we would not end up here).")
   (xdoc::p
    "For now we do not check any requirements on group literals, but we plan to.
     Those are fairly elaborate requirements, which need some work.")
   (xdoc::p
    "Type-checking literals does not require the static environment."))
  (literal-case
   lit
   :bool (type-bool)
   :unsigned (b* ((bound (bitsize-case lit.size
                                       :8 (expt 2 8)
                                       :16 (expt 2 16)
                                       :32 (expt 2 32)
                                       :64 (expt 2 64)
                                       :128 (expt 2 128))))
               (if (< lit.val bound)
                   (type-unsigned lit.size)
                 (reserrf (list :bad-literal (literal-fix lit)))))
   :signed (b* ((bound (bitsize-case lit.size
                                     :8 (expt 2 7)
                                     :16 (expt 2 15)
                                     :32 (expt 2 31)
                                     :64 (expt 2 63)
                                     :128 (expt 2 127))))
             (if (< lit.val bound)
                 (type-signed lit.size)
               (reserrf (list :bad-literal (literal-fix lit)))))
   :string (type-string)
   :address (type-address)
   :field (type-field)
   :group (type-group)
   :scalar (type-scalar))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-unop ((op unopp) (arg typep))
  :returns (type type-resultp)
  :short "Type-check a use of a unary operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "When type-checking a unary expression,
     we first type-check the argument expression,
     obtaining a type for it (if its type checking is successful).
     This type is passed to this ACL2 function,
     which checks whether the unary operator is allowed on the type,
     in which case the resulting type is returned."))
  (b* ((err (list :bad-unary (unop-fix op) (type-fix arg))))
    (case (unop-kind op)
      ((:abs :abs-wrapped) (if (member-eq (type-kind arg) '(:signed))
                               (type-fix arg)
                             (reserrf err)))
      (:double (if (member-eq (type-kind arg) '(:field :group))
                   (type-fix arg)
                 (reserrf err)))
      ((:inv :square :square-root) (if (member-eq (type-kind arg) '(:field))
                                       (type-fix arg)
                                     (reserrf err)))
      (:neg (if (member-eq (type-kind arg) '(:signed :field :group))
                (type-fix arg)
              (reserrf err)))
      (:not (if (member-eq (type-kind arg) '(:bool :unsigned :signed))
                (type-fix arg)
              (reserrf err)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-binop ((op binopp) (arg1 typep) (arg2 typep))
  :returns (type type-resultp)
  :short "Type-check a use of a binary operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "When type-checking a binary expression,
     we first type-check the argument expressions,
     obtaining types for them (if their type checking is successful).
     These types are passed to this ACL2 function,
     which checks whether the binary operator is allowed on the types,
     in which case the resulting type is returned."))
  (b* ((err (list (binop-fix op) (type-fix arg1) (type-fix arg2))))
    (case (binop-kind op)
      ((:and :or :nand :nor) (if (and (type-case arg1 :bool)
                                      (type-case arg2 :bool))
                                 (type-bool)
                               (reserrf err)))
      ((:eq :ne) (if (type-equiv arg1 arg2)
                     (type-bool)
                   (reserrf err)))
      ((:ge :gt :le :lt) (if (and (member-eq (type-kind arg1)
                                             '(:unsigned
                                               :signed
                                               :field
                                               :scalar))
                                  (type-equiv arg1 arg2))
                             (type-bool)
                           (reserrf err)))
      ((:bitxor :bitior :bitand) (if (and (type-equiv arg1 arg2)
                                          (member-eq (type-kind arg1)
                                                     '(:bool :unsigned :signed)))
                                     (type-fix arg1)
                                   (reserrf err)))
      ((:shl
        :shr
        :shl-wrapped
        :shr-wrapped) (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                               (type-case arg2 :unsigned)
                               (member-equal (type-unsigned->size arg2)
                                             (list (make-bitsize-8)
                                                   (make-bitsize-16)
                                                   (make-bitsize-32))))
        (type-fix arg1)
        (reserrf err)))
      (:add (if (and (member-eq (type-kind arg1)
                                '(:unsigned :signed :field :group :scalar))
                     (type-equiv arg1 arg2))
                (type-fix arg1)
              (reserrf err)))
      (:add-wrapped (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                             (type-equiv arg1 arg2))
                        (type-fix arg1)
                      (reserrf err)))
      (:sub (if (and (member-eq (type-kind arg1)
                                '(:unsigned :signed :field :group))
                     (type-equiv arg1 arg2))
                (type-fix arg1)
              (reserrf err)))
      (:sub-wrapped (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                             (type-equiv arg1 arg2))
                        (type-fix arg1)
                      (reserrf err)))
      (:mul (case (type-kind arg1)
              ((:unsigned :signed) (if (type-equiv arg1 arg2)
                                       (type-fix arg1)
                                     (reserrf err)))
              (:field (if (type-case arg2 :field)
                          (type-field)
                        (reserrf err)))
              (:group (if (type-case arg2 :scalar)
                          (type-group)
                        (reserrf err)))
              (:scalar (if (type-case arg2 :group)
                           (type-group)
                         (reserrf err)))
              (t (reserrf err))))
      (:mul-wrapped (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                             (type-equiv arg1 arg2))
                        (type-fix arg1)
                      (reserrf err)))
      (:div (if (and (member-eq (type-kind arg1) '(:unsigned :signed :field))
                     (type-equiv arg1 arg2))
                (type-fix arg1)
              (reserrf err)))
      (:div-wrapped (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                             (type-equiv arg1 arg2))
                        (type-fix arg1)
                      (reserrf err)))
      (:rem (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                     (type-equiv arg1 arg2))
                (type-fix arg1)
              (reserrf err)))
      (:rem-wrapped (if (and (member-eq (type-kind arg1) '(:unsigned :signed))
                             (type-equiv arg1 arg2))
                        (type-fix arg1)
                      (reserrf err)))
      (:pow (case (type-kind arg1)
              ((:unsigned :signed)
               (if (and (type-case arg2 :unsigned)
                        (member-equal (type-unsigned->size arg2)
                                      (list (bitsize-8)
                                            (bitsize-16)
                                            (bitsize-32))))
                   (type-fix arg1)
                 (reserrf err)))
              (:field (if (type-case arg2 :field)
                          (type-field)
                        (reserrf err)))
              (t (reserrf err))))
      (:pow-wrapped (case (type-kind arg1)
                      ((:unsigned :signed)
                       (if (and (type-case arg2 :unsigned)
                                (member-equal (type-unsigned->size arg2)
                                              (list (bitsize-8)
                                                    (bitsize-16)
                                                    (bitsize-32))))
                           (type-fix arg1)
                         (reserrf err)))
                      (t (reserrf err))))
      (t (reserrf (impossible)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expr-sort
  :short "Fixtype of expression sorts."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are three sorts of expressions:
     those that evaluate to a constant value;
     those that evaluate to a non-constant value;
     and those that evaluation to a location.
     These three possibilities are captured here."))
  (:constant ())
  (:nonconst ())
  (:location ())
  :pred expr-sortp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist expr-sort-list
  :short "Fixtype of lists of expression sorts"
  :elt-type expr-sort
  :true-listp t
  :elementp-of-nil nil
  :pred expr-sort-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-type
  :short "Fixtype of expression types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a broader notion of type compared to @(tsee type).
     It is the information about each expression
     that is calculated by type checking.
     It consists of a plain type plus a sort."))
  ((type type)
   (sort expr-sort))
  :pred expr-typep)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist expr-type-list
  :short "Fixtype of lists of expression types."
  :elt-type expr-type
  :true-listp t
  :elementp-of-nil nil
  :pred expr-type-listp)

;;;;;;;;;;

(std::defprojection expr-type-list->type-list (x)
  :guard (expr-type-listp x)
  :returns (types type-listp)
  :short "Lift @(tsee expr-type->type) to lists."
  (expr-type->type x)
  ///
  (fty::deffixequiv expr-type-list->type-list
    :args ((x expr-type-listp))))

;;;;;;;;;;

(std::defprojection expr-type-list->sort-list (x)
  :guard (expr-type-listp x)
  :returns (sorts expr-sort-listp)
  :short "Lift @(tsee expr-type->sort) to lists."
  (expr-type->sort x)
  ///
  (fty::deffixequiv expr-type-list->sort-list
    :args ((x expr-type-listp))))

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-type-result
  :short "Fixtype of errors and expression types."
  :ok expr-type
  :pred expr-type-resultp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-type-list-result
  :short "Fixtype of errors and lists of expression types."
  :ok expr-type-list
  :pred expr-type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod identifier+exprtype
  :short "Fixtype of pairs consisting of an identifier and an expression type."
  ((identifier identifier)
   (expr-type expr-type))
  :tag :identifier+exprtype
  :pred identifier+exprtype-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier+exprtype-result
  :short "Fixtype of errors and
          pairs consisting of an identifier and an expression type."
  :ok identifier+exprtype
  :pred identifier+exprtype-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap identifier-exprtype-map
  :short "Fixtype of finite maps from identifiers to expression types."
  :key-type identifier
  :val-type expr-type
  :pred identifier-exprtype-mapp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult identifier-exprtype-map-result
  :short "Fixtype of errors and
          finite maps from identifiers to expression types."
  :ok identifier-exprtype-map
  :pred identifier-exprtype-map-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-call ((fun identifierp) (args expr-type-listp) (env senvp))
  :returns (type type-resultp)
  :short "Type-check a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "When type-checking a function call,
     we first type-check the arguments,
     obtaining a list of expression types if successful.
     That list of expression types is passed to this ACL2 function,
     which checks them against the function's parameters,
     and returns the output type of the function,
     which is also the type of the function call.")
   (xdoc::p
    "The argumens types must match the functino parameter types,
     in number and element-wise.
     Furthermore, if a parameter is constant,
     the corresponding argument must be constant too."))
  (b* ((info (get-function-sinfo fun env))
       ((unless info)
        (reserrf (list :function-not-found (identifier-fix fun))))
       (inputs (function-sinfo->inputs info))
       (output (function-sinfo->output info)))
    (typecheck-call-aux inputs args output))
  :hooks (:fix)

  :prepwork
  ((define typecheck-call-aux ((inputs var/const-sinfo-listp)
                               (args expr-type-listp)
                               (output typep))
     :returns (type type-resultp)
     :parents nil
     (b* (((when (endp inputs))
           (if (endp args)
               (type-fix output)
             (reserrf (list :extra-arguments
                        (expr-type-list-fix args)))))
          ((when (endp args))
           (reserrf (list :extra-formals
                      (var/const-sinfo-list-fix inputs))))
          (input (car inputs))
          (arg (car args))
          ((unless (equal (var/const-sinfo->type input)
                          (expr-type->type arg)))
           (reserrf (list :type-mismatch
                      (var/const-sinfo-fix input)
                      (expr-type-fix arg))))
          ((unless (or (not (var/const-sinfo->constp input))
                       (expr-sort-case (expr-type->sort arg) :constant)))
           (reserrf (list :const-mismatch
                                  (var/const-sinfo-fix input)
                                  (expr-type-fix arg)))))
       (typecheck-call-aux (cdr inputs) (cdr args) output))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identexprtype-map-to-identype-map ((emap identifier-exprtype-mapp))
  :returns (map type-mapp)
  :short "Turn a finite map from identifiers to expression types
          into a finite map from identifiers to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Project each expression type to the underlying type.
     The new map has the same keys."))
  (b* ((emap (identifier-exprtype-map-fix emap))
       ((when (omap::emptyp emap)) nil)
       ((mv id etype) (omap::head emap))
       (map (identexprtype-map-to-identype-map (omap::tail emap))))
    (omap::update id (expr-type->type etype) map))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-exprtype-map-constp ((map identifier-exprtype-mapp))
  :returns (yes/no booleanp)
  :short "Check if a finite map from identifiers to expression types
          has all constant expression types in its range."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to determine, when type-checking a struct expression,
     whether the expression is constant or not.
     It is when all of its component expressions are."))
  (b* ((map (identifier-exprtype-map-fix map))
       ((when (omap::emptyp map)) t)
       ((mv & etype) (omap::head map))
       ((unless (expr-sort-case (expr-type->sort etype) :constant)) nil))
    (identifier-exprtype-map-constp (omap::tail map)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines typecheck-expressions
  :short "Type-check expressions and lists of expressions."

  (define typecheck-expression ((expr expressionp) (env senvp))
    :returns (etype expr-type-resultp)
    :parents (type-checking typecheck-expressions)
    :short "Type-check an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If type checking succeeds, we return an expression type:
       see @(tsee expr-type).")
     (xdoc::p
      "For a variable or a constant,
       we look it up in the static environment,
       and return an expression type according to the type found
       and whether it is a variable or constant.
       If it is a variable, the expression denotes a location;
       if it is a constant, the expression denotes a constant value.")
     (xdoc::p
      "A literal denotes a constant value of the type of the literal.")
     (xdoc::p
      "Unary and binary expressions are type-checked by
       first recursively type-checking their arguments,
       and then using @(tsee typecheck-unop) and @(tsee typecheck-binop)
       to check whether the argument types are allowed for the operator
       and to determine what the resulting type is.
       A unary or binary expression
       is constant when its operand(s) is/are.
       Otherwise, it denotes a non-constant value;
       it never denotes a location.")
     (xdoc::p
      "However, a unary expression consisting of
       the arithmetic negation operator applied to a literal
       whose numeric value is @('2^(N-1)') and whose type suffix is @('iN'),
       for @('N') in {8, 16, 32, 64, 128},
       is treated specially:
       it is allowed and it has type @('iN').
       This is the only (simple) way to denote
       the most negative element of each signed type,
       due to the inherent asymmetry of two's complement numbers.")
     (xdoc::p
      "In a ternary (i.e. conditional) expression,
       the test must be boolean,
       and the two branches must have the same type.
       The expression is constant when all three operands are.
       Otherwise, it denotes a value;
       it never denotes a location.")
     (xdoc::p
      "For a tuple expression,
       we recursively type-check the component expressions.
       We form the tuple type from the types of the components.
       The expression is constant if the components are;
       otherwise it is non-constant;
       it never denotes a location.")
     (xdoc::p
      "For a tuple component expression,
       we recursively type-check the sub-expression,
       ensuring that it has a tuple type.
       We ensure that the index is below the tuple type's length,
       and we return the type of the corresponding component.
       If the tuple sub-expression returns a location,
       so does the tuple component expression.
       If the tuple sub-expression is constant,
       so is the tuple component expression.
       Otherwise, i.e. if the tuple sub-expression is non-constant,
       so is the tuple component expression.")
     (xdoc::p
      "For a struct expression,
       we recursively type-check the struct component initializers,
       obtaining a finite map from identifiers to expression types.
       We ensure that this finite map matches
       the one in the environment for the struct type.
       The struct expression is constant if all its components are;
       otherwise, it is non-constant.
       We also ensure that the struct expression has at least one component.")
     (xdoc::p
      "For a struct component expression,
       we recursively type-check the struct sub-expression,
       ensuring it has a struct type in scope.
       We ensure that the struct type has a component with the given name,
       whose type is also the type of the struct component expression.
       Similarly to tuple component expressins,
       the sort of a struct component expression
       is the same as the struct sub-expression.")
     (xdoc::p
      "For a function call,
       we recursively type-check the arguments,
       obtaining their expression types.
       Then we use a separate ACL2 function
       to find the function and to check the argument expression types
       against the formal parameters of the function,
       returning the output type if successful.
       A function call always denotes a non-constant value;
       never a constant value or a location."))
    (expression-case
     expr
     :literal
     (b* (((okf type) (typecheck-literal expr.get))
          (sort (expr-sort-constant)))
       (make-expr-type :type type :sort sort))
     :var/const
     (b* ((info (get-var/const-sinfo expr.name env))
          ((unless info) (reserrf (list :no-var/const expr.name)))
          (type (var/const-sinfo->type info))
          (sort (if (var/const-sinfo->constp info)
                    (expr-sort-constant)
                  (expr-sort-location))))
       (make-expr-type :type type :sort sort))
     :assoc-const (reserrf :todo)
     :unary
     (b* (((when (and (unop-case expr.op :neg)
                      (equal expr.arg
                             (expression-literal
                              (make-literal-signed :val (expt 2 7)
                                                   :size (bitsize-8))))))
           (make-expr-type :type (type-signed (bitsize-8))
                           :sort (expr-sort-constant)))
          ((when (and (unop-case expr.op :neg)
                      (equal expr.arg
                             (expression-literal
                              (make-literal-signed :val (expt 2 15)
                                                   :size (bitsize-16))))))
           (make-expr-type :type (type-signed (bitsize-16))
                           :sort (expr-sort-constant)))
          ((when (and (unop-case expr.op :neg)
                      (equal expr.arg
                             (expression-literal
                              (make-literal-signed :val (expt 2 31)
                                                   :size (bitsize-32))))))
           (make-expr-type :type (type-signed (bitsize-32))
                           :sort (expr-sort-constant)))
          ((when (and (unop-case expr.op :neg)
                      (equal expr.arg
                             (expression-literal
                              (make-literal-signed :val (expt 2 63)
                                                   :size (bitsize-64))))))
           (make-expr-type :type (type-signed (bitsize-64))
                           :sort (expr-sort-constant)))
          ((when (and (unop-case expr.op :neg)
                      (equal expr.arg
                             (expression-literal
                              (make-literal-signed :val (expt 2 127)
                                                   :size (bitsize-128))))))
           (make-expr-type :type (type-signed (bitsize-128))
                           :sort (expr-sort-constant)))
          ((okf etype) (typecheck-expression expr.arg env))
          ((okf type) (typecheck-unop expr.op (expr-type->type etype)))
          (sort (if (expr-sort-case (expr-type->sort etype) :constant)
                    (expr-sort-constant)
                  (expr-sort-nonconst))))
       (make-expr-type :type type :sort sort))
     :binary
     (b* (((okf etype1) (typecheck-expression expr.arg1 env))
          ((okf etype2) (typecheck-expression expr.arg2 env))
          ((okf type) (typecheck-binop expr.op
                                       (expr-type->type etype1)
                                       (expr-type->type etype2)))
          (sort (if (and (expr-sort-case (expr-type->sort etype1) :constant)
                         (expr-sort-case (expr-type->sort etype2) :constant))
                    (expr-sort-constant)
                  (expr-sort-nonconst))))
       (make-expr-type :type type :sort sort))
     :cond
     (b* (((okf etype1) (typecheck-expression expr.test env))
          ((okf etype2) (typecheck-expression expr.then env))
          ((okf etype3) (typecheck-expression expr.else env))
          ((unless (type-case (expr-type->type etype1) :bool))
           (reserrf (list :cond-test (expr-type->type etype1))))
          ((unless (equal (expr-type->type etype2)
                          (expr-type->type etype3)))
           (reserrf (list :cond-mismatch
                          (expr-type->type etype2)
                          (expr-type->type etype3))))
          (type (expr-type->type etype2))
          (sort (if (and (expr-sort-case (expr-type->sort etype1) :constant)
                         (expr-sort-case (expr-type->sort etype2) :constant)
                         (expr-sort-case (expr-type->sort etype3) :constant))
                    (expr-sort-constant)
                  (expr-sort-nonconst))))
       (make-expr-type :type type :sort sort))
     :unit
     (make-expr-type :type (type-unit)
                     :sort (expr-sort-constant))
     :tuple
     (b* (((okf etypes) (typecheck-expression-list expr.components env))
          (types (expr-type-list->type-list etypes))
          (type (type-tuple types))
          (sort (if (equal (expr-type-list->sort-list etypes)
                           (repeat (len expr.components) (expr-sort-constant)))
                    (expr-sort-constant)
                  (expr-sort-nonconst))))
       (make-expr-type :type type :sort sort))
     :tuple-component
     (b* (((okf etype) (typecheck-expression expr.tuple env))
          (type (expr-type->type etype))
          ((unless (type-case type :tuple))
           (reserrf (list :tuple-component-mismatch
                          (expr-type->type etype))))
          (types (type-tuple->components type))
          ((unless (< expr.index (len types)))
           (reserrf (list :tuple-component-index
                          expr.index
                          types)))
          (comptype (nth expr.index types))
          (sort (expr-type->sort etype)))
       (make-expr-type :type comptype :sort sort))
     :struct
     (b* ((info (get-struct-sinfo expr.type env))
          ((unless info) (reserrf (list :struct-not-found expr.type)))
          ((okf map-etypes) (typecheck-struct-init-list expr.components env))
          ((when (omap::emptyp map-etypes)) (reserrf :no-components))
          (map-types (identexprtype-map-to-identype-map map-etypes))
          ((unless (equal map-types
                          (struct-sinfo->components info)))
           (reserrf (list :struct-mismatch
                          :required (struct-sinfo->components info)
                          :found map-types)))
          (constp (identifier-exprtype-map-constp map-etypes)))
       ;; TODO: consider if this next form needs to take into consideration
       ;; recordp=T and/or type-external-named
       (make-expr-type :type (type-internal-named expr.type nil)
                       :sort (if constp
                                 (expr-sort-constant)
                               (expr-sort-nonconst))))
     :struct-component
     (b* (((okf etype) (typecheck-expression expr.struct env))
          (type (expr-type->type etype))
          (sort (expr-type->sort etype))
          ((unless (type-case type :internal-named))
           (reserrf (list :struct-component-mismatch
                          :required :internal-named
                          :supplied type)))
          (info (get-struct-sinfo (type-internal-named->get type) env))
          ((unless info)
           (reserrf (list :struct-not-found (type-internal-named->get type))))
          (comps (struct-sinfo->components info))
          (name+type (omap::assoc expr.component comps))
          ((unless (consp name+type))
           (reserrf (list :component-not-found
                          :available comps
                          :not-found expr.component)))
          (type (cdr name+type)))
       (make-expr-type :type type :sort sort))
     :internal-call
     (b* (((okf etypes) (typecheck-expression-list expr.args env))
          ((okf type) (typecheck-call expr.fun etypes env))
          (sort (expr-sort-nonconst)))
       (make-expr-type :type type :sort sort))
     :external-call
     (reserrf :todo)
     :static-call
     (reserrf :todo))
    :measure (expression-count expr))

  (define typecheck-expression-list ((exprs expression-listp) (env senvp))
    :returns (etypes expr-type-list-resultp)
    :parents (type-checking typecheck-expressions)
    :short "Type-check a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check the expressions, one after the other."))
    (b* (((when (endp exprs)) (expr-type-list-result-ok nil))
         ((okf etype) (typecheck-expression (car exprs) env))
         ((okf etypes) (typecheck-expression-list (cdr exprs) env)))
      (cons etype etypes))
    :measure (expression-list-count exprs))

  (define typecheck-struct-init ((init struct-initp) (env senvp))
    :returns (name+etype identifier+exprtype-resultp)
    :parents (type-checking typecheck-expressions)
    :short "Type-check a struct component initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "We type-check the type.
       We return a pair consisting of
       the component name and its expression type."))
    (b* (((okf etype) (typecheck-expression (struct-init->expr init) env)))
      (make-identifier+exprtype :identifier (struct-init->name init)
                                :expr-type etype))
    :measure (struct-init-count init))

  (define typecheck-struct-init-list ((inits struct-init-listp) (env senvp))
    :returns (map identifier-exprtype-map-resultp)
    :short "Type-check a list of struct component initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "We type-check each initializer,
       building a finite map for all the components.
       We return an error if there is a duplicate component."))
    (b* (((when (endp inits)) nil)
         ((okf (identifier+exprtype first))
          (typecheck-struct-init (car inits) env))
         ((okf map) (typecheck-struct-init-list (cdr inits) env))
         ((when (consp (omap::assoc first.identifier map)))
          (reserrf (list :duplicate-component first.identifier))))
      (omap::update first.identifier first.expr-type map))
    :measure (struct-init-list-count inits))

  :prepwork
  ((local
    (in-theory
     (enable expr-typep-when-expr-type-resultp-and-not-reserrp
             expr-type-listp-when-expr-type-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards typecheck-expression)

  (fty::deffixequiv-mutual typecheck-expressions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-print-args ((string char-listp)
                              (exprs expression-listp)
                              (env senvp))
  (declare (ignore string))
  :returns (ok reserr-optionp)
  :short "Type-check the arguments of a console print call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the expressions all type-check.
     We should also check that the format string is well-formed,
     according to the format string grammar,
     and that the number of containers matches the number of expressions."))
  (b* (((okf &) (typecheck-expression-list exprs env)))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-console ((cnsl consolep) (env senvp))
  :returns (ok reserr-optionp)
  :short "Type-check a console call."
  :long
  (xdoc::topstring
   (xdoc::p
    "The expression of an assertion call must be boolean.")
   (xdoc::p
    "The arguments of a print call must type-check."))
  (console-case
   cnsl
   :assert (b* (((okf etype) (typecheck-expression cnsl.arg env)))
             (if (type-case (expr-type->type etype) :bool)
                 nil
               (reserrf (list :non-bool-assertion cnsl.arg))))
   :error (typecheck-print-args cnsl.string cnsl.exprs env)
   :log (typecheck-print-args cnsl.string cnsl.exprs env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod types+senv
  :short "Fixtype of pairs consisting of
          a set of optional types
          and a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the results of successfully type-checking statements.")
   (xdoc::p
    "In general, a statement may return a value (of some type) or not:
     one such outcome can be captured, statically, as an optional type.
     In the presence of conditionals,
     different branches may return different optional types:
     this leads to using finite sets of optional types
     to capture the possible types of values returned by a statement,
     including (for @('nil')) the case of returning no value.")
   (xdoc::p
    "Furthermore, a statement may introduce new variables and constants,
     which must be added to the static environment.
     This means that the type-checking of a statement also results in
     a possibly updated static environments."))
  ((types type-option-set)
   (senv senv))
  :tag :optypes+senv
  :pred types+senv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult types+senv-result
  :short "Fixtype of errors and pairs consisting of
          a set of optional types
          and a static environment."
  :ok types+senv
  :pred types+senv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-vardecl ((decl vardeclp) (env senvp))
  :returns (types+senv types+senv-resultp)
  :short "Type-check a variable declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We type-check the type and the initializing expression,
     whose type must match the variable's type.
     We extend the static environment with the variable,
     provided that the name is not already there.
     A variable declaration returns no type."))
  (b* (((vardecl decl) decl)
       ((okf &) (typecheck-type decl.type env))
       ((okf etype) (typecheck-expression decl.init env))
       ((unless (equal decl.type (expr-type->type etype)))
        (reserrf (list :mismatch-var-decl
                   :name decl.name
                   :required decl.type
                   :supplied (expr-type->type etype))))
       ((okf env) (extend-senv-with-vardecl decl env)))
    (make-types+senv :types (set::insert nil nil)
                     :senv env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-constdecl ((decl constdeclp) (env senvp))
  :returns (types+senv types+senv-resultp)
  :short "Type-check a constant declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We type-check the type and the initializing expression,
     whose type must match the constants's type
     and whose sort must be constant.
     We extend the static environment with the constant,
     provided that the name is not already there.
     A constant declaration returns no type."))
  (b* (((constdecl decl) decl)
       ((okf &) (typecheck-type decl.type env))
       ((okf etype) (typecheck-expression decl.init env))
       ((unless (equal decl.type (expr-type->type etype)))
        (reserrf (list :mismatch-const-decl
                   :name decl.name
                   :required decl.type
                   :supplied (expr-type->type etype))))
       ((unless (expr-sort-case (expr-type->sort etype) :constant))
        (reserrf (list :mismatch-const
                   :name decl.name
                   :init (expr-type->sort etype))))
       ((okf env) (extend-senv-with-constdecl decl env)))
    (make-types+senv :types (set::insert nil nil)
                     :senv env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines typecheck-statements
  :short "Type-check
          statements,
          lists of statments,
          branches,
          and lists of branches."

  (define typecheck-statement ((stmt statementp) (env senvp))
    :returns (types+senv types+senv-resultp)
    :parents (type-checking typecheck-statements)
    :short "Type-check a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If type checking succeeds,
       we return a set of optional types
       and a possibly updated static environment.")
     (xdoc::p
      "Variable and constant declarations are type-checked
       via separate ACL2 functions.")
     (xdoc::p
      "For an assignment statement, we first type-check both expressions.
       The left one must denote a location,
       and must have the same type as the right one.
       An assignment statement returns no type
       and leaves the environment unchanged.")
     (xdoc::p
      "For a return statement, we first type-check the expression.
       A return statement returns the type of the expression,
       and leaves the static environment unchanged.")
     (xdoc::p
      "For a loop,
       we first ensure that the type of the variable is an integer one
       (which is therefore always well-formed,
       and does not need to be type-checked explicitly).
       Then we type-check the two expressions,
       which must have the same integer type as the variable,
       and which must denote constant values.
       We extend the static environment with the loop variable,
       but we add it as a constant to the environment:
       this is because the new environment is for type-checking the loop body,
       where the loop variable is a constant
       because loops are unrolled eventually,
       and thus in each unrolled iteration
       the value of the loop variable is a known constant.
       We type-check the statements in the loop, with the new environment.
       The loop statement as a whole may return
       any of the types returned by the body, or no type:
       the latter case is motivated by the fact that, at type checking time,
       we do not know how many times the loop executes, possibly none,
       and in that case execution proceeds just after the loop,
       i.e. the loop statement returns nothing.
       The loop statement as a whole does not change the static environment:
       the new environment is just for the loop body,
       but the environment is restored to what it was before the loop
       when type-checking any statements following the loop.")
     (xdoc::p
      "For a conditional statement,
       we first type-check its branches via a separate ACL2 function.
       Then we type-check the default block recursively.
       The conditional statement may return all the types returned
       by any of the branches or the default block.
       Note that the absence of default block in concrete syntax
       is represented as an empty default block in abstract syntax:
       an empty block never returns any type.
       The static environment is unchanged by the conditional statement;
       even though the branch and default blocks may extend the environment,
       the extensions are local to those blocks.")
     (xdoc::p
      "A console statement always completes normally
       and does not change the static environment.")
     (xdoc::p
      "The type checking of a block statement reduces to
       the type checking of the enclosed statements.
       The static environment is unchanged after the block;
       any changes within the block are local to the block."))
    (statement-case
     stmt
     :let
     (typecheck-vardecl stmt.get env)
     :const
     (typecheck-constdecl stmt.get env)
     :assign
     (b* (((okf etype-left) (typecheck-expression stmt.left env))
          ((okf etype-right) (typecheck-expression stmt.left env))
          ((unless (equal (expr-type->type etype-left)
                          (expr-type->type etype-right)))
           (reserrf (list :assign-mismatch
                      :left (expr-type->type etype-left)
                      :right (expr-type->type etype-right))))
          ((unless (expr-sort-case (expr-type->sort etype-left) :location))
           (reserrf (list :non-assignable stmt.left))))
       (make-types+senv :types (set::insert nil nil)
                        :senv (senv-fix env)))
     :return
     (b* (((okf etype) (typecheck-expression stmt.value env)))
       (make-types+senv :types (set::insert (expr-type->type etype) nil)
                        :senv (senv-fix env)))
     :for
     (b* (((unless (member-eq (type-kind stmt.type) '(:unsigned :signed)))
           (reserrf (list :non-integer-loop-type stmt.type)))
          ((okf etype-from) (typecheck-expression stmt.from env))
          ((okf etype-to) (typecheck-expression stmt.to env))
          ((unless (equal etype-from
                          (make-expr-type :type stmt.type
                                          :sort (expr-sort-constant))))
           (reserrf (list :non-constant-loop-start stmt.from)))
          ((unless (equal etype-to
                          (make-expr-type :type stmt.type
                                          :sort (expr-sort-constant))))
           (reserrf (list :non-constant-loop-end stmt.to)))
          (info (make-var/const-sinfo :type stmt.type :constp t))
          (new-env (add-var/const-sinfo stmt.name info env))
          ((unless new-env) (reserrf (list :loop-variable-exist stmt.name)))
          ((okf types) (typecheck-statement-list stmt.body new-env)))
       (make-types+senv :types (set::insert nil types)
                        :senv (senv-fix env)))
     :if
     (b* (((okf types-branches) (typecheck-branch-list stmt.branches env))
          ((okf types-else) (typecheck-statement-list stmt.else env)))
       (make-types+senv :types (set::union types-branches types-else)
                        :senv (senv-fix env)))
     :console
     (if (typecheck-console stmt.get env)
         (make-types+senv :types (set::insert nil nil)
                          :senv (senv-fix env))
       (reserrf (list :bad-console stmt.get)))
     ;; TODO these next three
     :finalize
     (reserrf (list :typecheck-finalize-statement-not-yet-implemented))
     :increment
     (reserrf (list :typecheck-increment-statement-not-yet-implemented))
     :decrement
     (reserrf (list :typecheck-decrement-statement-not-yet-implemented))
     :block
     (b* (((okf types) (typecheck-statement-list stmt.get env)))
       (make-types+senv :types types
                        :senv (senv-fix env))))
    :measure (statement-count stmt))

  (define typecheck-statement-list ((stmts statement-listp) (env senvp))
    :returns (types type-option-set-resultp)
    :parents (type-checking typecheck-statements)
    :short "Type-check a list of statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "We return just a set of optional types if type checking is successful.
       We do not return the final static environment after the statements,
       because the caller would discard it anyways:
       the list of statements forms a block,
       and any extension to the static environment is local to the block.")
     (xdoc::p
      "An empty list of statements returns no types.
       For a non-empty list of statements,
       we first type-check the first statement;
       there are two cases.
       If the first statement may return no type,
       we proceed to type-check the remaining statements,
       in the static environment resulting
       from type-checking the first statement;
       we take the union of the types returned by the first statement
       and the types returned by the remaining statements.
       If instead the first statement cannot return no type
       (i.e. it always returns some type),
       then the remaining statements are dead code,
       and we do not type-check them."))
    (b* (((when (endp stmts)) (set::insert nil nil))
         ((okf types+env) (typecheck-statement (car stmts) env))
         (types-first (types+senv->types types+env))
         ((unless (set::in nil types-first)) types-first)
         (types-first (set::delete nil types-first))
         (env (types+senv->senv types+env))
         ((okf types-rest) (typecheck-statement-list (cdr stmts) env)))
      (set::union types-first types-rest))
    :measure (statement-list-count stmts))

  (define typecheck-branch ((branch branchp) (env senvp))
    :returns (types type-option-set-resultp)
    :parents (type-checking typecheck-statements)
    :short "Type-check a branch."
    :long
    (xdoc::topstring
     (xdoc::p
      "We type-check the test, ensuring that it is boolean-valued.
       Then we type-check the body.
       The branch's possible returned types are the ones of the body."))
    (b* (((branch branch) branch)
         ((okf etype) (typecheck-expression branch.test env))
         (type (expr-type->type etype))
         ((unless (type-case type :bool))
          (reserrf (list :non-boolean-branch-test
                     branch.test))))
      (typecheck-statement-list branch.body env))
    :measure (branch-count branch))

  (define typecheck-branch-list ((branches branch-listp) (env senvp))
    :returns (types type-option-set-resultp)
    :parents (type-checking typecheck-statements)
    :short "Type-check a list of branches."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the list is empty, we return the empty set.
       Note that conditional statements always have one or more branches
       (this is enforced by an invariant in @(tsee statement)),
       so the empty set is just an artificial base case,
       but the set of optional types is never empty
       for the actual branches of a conditional statement.")
     (xdoc::p
      "If the list is not empty,
       we type-check the first branch and the remaining branches,
       and we take the union of the sets of optional types.")
     (xdoc::p
      "All the branches are type-checked in the same static environment,
       which is the one just before the conditional statement."))
    (b* (((when (endp branches)) nil)
         ((okf types-first) (typecheck-branch (car branches) env))
         ((okf types-rest) (typecheck-branch-list (cdr branches) env)))
      (set::union types-first types-rest))
    :measure (branch-list-count branches))

  :prepwork
  ((local
    (in-theory
     (enable
      type-option-setp-when-type-option-set-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards typecheck-statement)

  (fty::deffixequiv-mutual typecheck-statements))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-funparam ((param funparamp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Type-check a function parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "We type-check the type,
     and we extend the static environment with the parameter.
     In fact, the body of the function is type-checked
     in the top-level environment extended with the parameters."))
  (b* (((funparam param) param)
       ((okf &) (typecheck-type param.type env))
       (info (funparam-to-var/const-sinfo param))
       (new-env (add-var/const-sinfo param.name info env))
       ((unless new-env) (reserrf (list :parameter-exists param.name))))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-funparam-list ((params funparam-listp) (env senvp))
  :returns (new-env senv-resultp)
  :short "Type-check a list of function parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This checks the parameters one after the other,
     threading the static environment through.
     Thus, if the type checking is successful,
     the final static environment includes all the parameters."))
  (b* (((when (endp params)) (senv-fix env))
       ((okf env) (typecheck-funparam (car params) env)))
    (typecheck-funparam-list (cdr params) env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-fundecl ((decl fundeclp) (env senvp))
  :returns (ok reserr-optionp)
  :short "Type-check a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We start by checking the function's parameter,
     which returns (if successful) a static environment that includes them.
     Then we type-check the output type.
     Finally we type-check the function's body, in the extended environment;
     the body must returns a singleton set
     that contains the output type of the function.")
   (xdoc::p
    "If the checking is successful, we return nothing,
     other than an indication of success,
     as opposed to an error."))
  (b* (((fundecl decl) decl)
       ((okf env) (typecheck-funparam-list decl.inputs env))
       ((okf &) (typecheck-type decl.output env))
       ((okf types) (typecheck-statement-list decl.body env))
       ((unless (equal types (set::insert decl.output nil)))
        (reserrf (list :output-mismatch
                   :required decl.output
                   :supplied types))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-compdecl ((decl compdeclp) (env senvp))
  :returns (name+type name+type-resultp)
  :short "Type-check a struct component declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We type-check the type,
     and we return it along with the name."))
  (b* ((type (compdecl->type decl))
       ((okf &) (typecheck-type type env)))
    (make-name+type :name (compdecl->name decl)
                    :type type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-compdecl-list ((decls compdecl-listp) (env senvp))
  :returns (map type-map-resultp)
  :short "Type-check a list of struct component declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We type-check all of them, returning their types in a map.
     We ensure that there are no duplicates."))
  (b* (((when (endp decls)) nil)
       ((okf (name+type first)) (typecheck-compdecl (car decls) env))
       ((okf map) (typecheck-compdecl-list (cdr decls) env))
       ((when (consp (omap::assoc first.name map)))
        (reserrf (list :duplicate-component first.name))))
    (omap::update first.name first.type map))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-structdecl ((decl structdeclp) (env senvp))
  :returns (ok reserr-optionp)
  :short "Type-check a struct declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the component declarations,
     ensuring that there is at least one.
     There is no need to check whether
     the struct type name is already in use or not,
     because this is already done when building the environment:
     in fact, the struct type's information is always in the environment
     when we get to the point of type-checking its declaration."))
  (b* (((okf map) (typecheck-compdecl-list (structdecl->components decl) env))
       ((when (omap::emptyp map))
        (reserrf (list :empty-struct (structdecl-fix decl)))))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-topdecl ((decl topdeclp) (env senvp))
  :returns (ok reserr-optionp)
  :short "Type-check a top-level declaration."
  (topdecl-case decl
                :function (typecheck-fundecl decl.get env)
                :struct (typecheck-structdecl decl.get env)
                ;; TODO: fix :mapping
                :mapping (reserrf :typecheck-for-mapping-not-yet-implemented))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-topdecl-list ((decls topdecl-listp) (env senvp))
  :returns (ok reserr-optionp)
  :short "Type-check a list of top-level declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check them one after the other."))
  (b* (((when (endp decls)) nil)
       ((okf &) (typecheck-topdecl (car decls) env)))
    (typecheck-topdecl-list (cdr decls) env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typecheck-file ((file filep))
  :returns (ok senv-resultp)
  :short "Type-check a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we go through the file
     and build the initial static environment,
     which we use to type-check all the declarations that form the file.
     In case of success, we return the static environment for the file:
     this is used as context to check input files."))
  (b* (((okf env) (file-to-senv file))

       ((okf &) (typecheck-topdecl-list (programdecl->items (file->program file))
       ;; TODO: consider imports
                                        env)))
    env)
  :hooks (:fix))

; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax-operations")
(include-book "portable-ascii-identifiers")
(include-book "integer-ranges")
(include-book "tag-environments")
(include-book "errors")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/fty/defunit" :dir :system)

(local (include-book "std/lists/last" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (language)
  :short "A static semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This static semantics consists of ACL2 functions
     that check whether the abstract syntactic entities
     satisfy the needed constraints.
     If the constraints are satisfied,
     additional information (e.g. types) may be returned,
     used to check constraints on enclosing abstract syntactic entities."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum var-defstatus
  :short "Fixtype of definition statuses of variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable (i.e. object) may be defined by a declaration or not
     [C:6.7/5] [C:6.9.2];
     it may be also tentatively defined,
     in the case of a file-scope variable under certain conditions.
     Thus, a variable may have three possible definition statuses:
     not defined, tentatively defined, and defined.
     This fixtype captures them.")
   (xdoc::p
    "See @(tsee var-table-add-var) for the details on
     how this status is handled."))
  (:undefined ())
  (:tentative ())
  (:defined ())
  :pred var-defstatusp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var-sinfo
  :short "Fixtype of static information about variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the information about variables needed for the static semantics.
     It consists of a type and a definition status."))
  ((type type)
   (defstatus var-defstatusp))
  :pred var-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption var-sinfo-option
  var-sinfo
  :short "Fixtype of optional static information about variables."
  :pred var-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap var-table-scope
  :short "Fixtype of scopes of variable tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable table is a symbol table for variables.
     The table (see @(tsee var-table)) is organized as
     a sequence with one element for each nested scope [C:6.2.1].
     This @('var-table-scope') fixtype
     contains information about such a scope.
     The information is organized as a finite map
     from identifiers (variable names) to static information for variables.
     Using a map is adequate because
     all the variables declared in a scope must have different names
     [C:6.2.1/2].
     The scope may be a file scope or a block scope [C:6.2.1/4]."))
  :key-type ident
  :val-type var-sinfo
  :pred var-table-scopep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var-table
  :short "Fixtype of variable tables, i.e. symbol tables for variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This keeps track of all the variables in scope [C:6.2.1],
     organized according to file and block scopes.
     The list has one element for the file scope
     and one element for each nested block scope,
     where the first element (the @(tsee car))
     corresponds to the innermost scope:
     this order is natural, as blocks are added via @(tsee cons).
     The list is never empty: we always have at least the file scope.")
   (xdoc::p
    "It is possible for two scopes in the list to have overlapping keys,
     when a variable in an inner block scope hides
     one in an outer block or scope in the file scope
     [C:6.2.1/4]."))
  :elt-type var-table-scope
  :true-listp t
  :non-emptyp t
  :elementp-of-nil t
  :pred var-tablep
  :prepwork ((local (in-theory (enable fix max))))
  ///

  (defrule var-tablep-of-cons-alt
    (iff (var-tablep (cons a x))
         (and (var-table-scopep a)
              (or (var-tablep x)
                  (eq x nil))))
    :enable var-tablep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult var-table-result
  :short "Fixtype of errors and variable table."
  :ok var-table
  :pred var-table-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-lookup ((var identp) (vartab var-tablep))
  :returns (info var-sinfo-optionp)
  :short "Look up a variable in a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is found, we return its information;
     otherwise, we return @('nil').
     We search for the variable in the sequence of scopes in order,
     i.e. from innermost to outermost block."))
  (b* (((unless (mbt (consp vartab))) nil)
       (varscope (var-table-scope-fix (car vartab)))
       (pair (omap::in (ident-fix var) varscope))
       ((when (consp pair)) (cdr pair))
       (vartab (cdr vartab))
       ((when (endp vartab)) nil))
    (var-table-lookup var vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-init ()
  :returns (vartab var-tablep)
  :short "Create an initial variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains a single (file) scope with no variables."))
  (list nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-add-block ((vartab var-tablep))
  :returns (new-table var-tablep)
  :short "Add a block scope to a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the empty set (of variables)
     to the front of the sequence.
     This is used when a block is entered.")
   (xdoc::p
    "Since a variable table is never empty,
     as enforced by its invariant,
     any scope added to it must be a block scope,
     because the file scope is always in the table."))
  (cons nil (var-table-fix vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-add-var ((var identp)
                           (type typep)
                           (defstatus var-defstatusp)
                           (vartab var-tablep))
  :returns (new-vartab
            var-table-resultp
            :hints (("Goal" :in-theory (enable var-table-resultp))))
  :short "Add a variable to (the innermost scope of) a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the type of the variable,
     we also pass a variable definition status to this ACL2 function,
     which says whether the variable declaration that we are processing
     constitutes a definition, a tentative definition, or neither.
     This variable definition status is determined
     by the specifics of the declaration,
     including where it occurs (block scope or file scope).")
   (xdoc::p
    "We look up the variable in the variable table.
     If it is not found, we add it, with the definition status given.
     If it is found, it must have the same type as the given type,
     otherwise it is an error.
     The given definition status is combined with the one in the table,
     as follows [C:6.9.2]:")
   (xdoc::ul
    (xdoc::li
     "If the one in the table is undefined,
      and the one in the declaration is also undefined,
      it remains undefined in the table.")
    (xdoc::li
     "If the one in the table is undefined,
      and the one in the declaration is defined or tentatively defined,
      the latter replaces the former in the table.")
    (xdoc::li
     "If the one in the table is tentatively defined,
      and the one in the declaration is undefined or tentatively defined,
      it remains tentatively defined in the table.")
    (xdoc::li
     "If the one in the table is tentatively defined,
      and the one in the declaration is defined,
      the latter replaces the former in the table.")
    (xdoc::li
     "If the one in the table is defined,
      and the one in the declaration is undefined or tentatively defined,
      it remains defined in the table.")
    (xdoc::li
     "If the one in the table is defined,
      and the one in the declaration is defined,
      it is an error, because there cannot be two definitions [C:6.9/5].")))
  (b* ((var (ident-fix var))
       (vartab (var-table-fix vartab))
       (varscope (car vartab))
       (var-info (omap::in var varscope))
       ((when (not (consp var-info)))
        (b* ((info (make-var-sinfo :type type
                                   :defstatus defstatus))
             (new-varscope (omap::update var info varscope)))
          (cons new-varscope (cdr vartab))))
       (info (cdr var-info))
       ((unless (type-equiv type
                            (var-sinfo->type info)))
        (reserrf (list :different-type-var var)))
       (tabdefstatus (var-sinfo->defstatus info))
       ((when (or (and (var-defstatus-case tabdefstatus :undefined)
                       (var-defstatus-case defstatus :undefined))
                  (and (var-defstatus-case tabdefstatus :tentative)
                       (var-defstatus-case defstatus :undefined))
                  (and (var-defstatus-case tabdefstatus :tentative)
                       (var-defstatus-case defstatus :tentative))
                  (and (var-defstatus-case tabdefstatus :defined)
                       (var-defstatus-case defstatus :undefined))
                  (and (var-defstatus-case tabdefstatus :defined)
                       (var-defstatus-case defstatus :tentative))))
        vartab)
       ((when (or (and (var-defstatus-case tabdefstatus :undefined)
                       (var-defstatus-case defstatus :tentative))
                  (and (var-defstatus-case tabdefstatus :undefined)
                       (var-defstatus-case defstatus :defined))
                  (and (var-defstatus-case tabdefstatus :tentative)
                       (var-defstatus-case defstatus :defined))))
        (b* ((new-info (change-var-sinfo info :defstatus defstatus))
             (new-varscope (omap::update var new-info varscope)))
          (cons new-varscope (cdr vartab)))))
    (assert* (and (var-defstatus-case tabdefstatus :defined)
                  (var-defstatus-case defstatus :defined))
             (reserrf (list :duplicate-var-def var))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-scope-all-definedp ((varscope var-table-scopep))
  :returns (yes/no booleanp)
  :short "CHeck if all the variables in a scope are defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "This applies to the file scope; see @(tsee var-table-all-definedp).")
   (xdoc::p
    "Even though C allows a variable to remain undefined in a translation unit
     (if it is not used in expressions),
     we are more strict and require every variable to be defined.
     This includes the case of a tentative definition,
     which is automatically turned into a full definition [C:6.9.2/2].
     So we go through the variables in the (file) scope,
     ensuring that they are defined or tentatively defined."))
  (b* ((varscope (var-table-scope-fix varscope))
       ((when (omap::empty varscope)) t)
       ((mv & info) (omap::head varscope))
       (defstatus (var-sinfo->defstatus info))
       ((unless (or (var-defstatus-case defstatus :defined)
                    (var-defstatus-case defstatus :tentative)))
        nil))
    (var-scope-all-definedp (omap::tail varscope)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-all-definedp ((vartab var-tablep))
  :returns (yes/no booleanp)
  :short "CHeck if all the variables in a file scope are defined."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only use this ACL2 function when the variable table has one scope,
     which must therefore be the file scope."))
  (var-scope-all-definedp (car vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-sinfo
  :short "Fixtype of static information about functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the information about functions needed for the static semantics.")
   (xdoc::p
    "This static information includes the type of the function.
     Function types are described in [C:6.2.5/20].
     Eventually these may be integrated into
     a broader formalized notion of C types,
     but for now we use
     a list of zero or more input types and a single output type.")
   (xdoc::p
    "This static information also includes a flag that says
     whether the function has been defined or not.
     A function may be declared without being defined,
     via a declaration [C:6.7].
     A file may have multiple declarations of the same function,
     via linkage [C:6.2.2/1],
     and up to one definition of the function [C:6.9/3] [C:6.9/5].
     The declarations and definition must have compatible types [C:6.7/4],
     which in our C subset, for functions,
     means identical input and output types.
     In order to check all of these requirements,
     as soon as we encounter the declaration or definition of a function,
     we add it to the function table with the appropriate flag and types.
     If we encounter more declarations of the same function after that,
     we ensure that the types are the same, and we leave the flag unchanged.
     If the function has one or more declarations before its definition,
     the flag is initially @('nil'),
     but we turn it to @('t') when we encounter the definition,
     which must have the same input and output types already in the table.
     If we encounter a second definition, i.e. if the flag is already set,
     it is an error, because it means that there are multiple definitions
     (which are disallowed in C, even if they are syntactically identical)."))
  ((inputs type-list)
   (output type)
   (definedp bool))
  :pred fun-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fun-sinfo-option
  fun-sinfo
  :short "Fixtype of optional static information about functions."
  :pred fun-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap fun-table
  :short "Fixtype of function tables, i.e. symbol tables for functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We associate a function type to the function name, in a finite map."))
  :key-type ident
  :val-type fun-sinfo
  :pred fun-tablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult fun-table-result
  :short "Fixtype of errors and function table."
  :ok fun-table
  :pred fun-table-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-table-lookup ((fun identp) (funtab fun-tablep))
  :returns (info fun-sinfo-optionp
                 :hints (("Goal" :in-theory (enable fun-sinfo-optionp))))
  :short "Look up a function in a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the type of the function, if the function is present.
     Otherwise, we return @('nil')."))
  (cdr (omap::in (ident-fix fun) (fun-table-fix funtab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-table-init ()
  :returns (funtab fun-tablep)
  :short "Create an initial function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just the empty map."))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-table-add-fun ((fun identp)
                           (inputs type-listp)
                           (output typep)
                           (definedp booleanp)
                           (funtab fun-tablep))
  :returns (new-funtab fun-table-resultp)
  :short "Add static information about a function to a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called when processing
     a function declaration or a function definition.
     Besides the name and the (input and output) types of the function,
     we pass a flag saying whether we are processing
     a function declaration or a function definition.
     If there is no entry in the table for the function,
     we add the information about the function.
     If there is already an entry,
     it must have the same input and output types [C:6.7/4]
     (in our C subset, compatible types means equal types);
     otherwise it is an error.
     If the information in the table has the @('definedp') flag @('nil'),
     it means that we have not encountered a definition yet;
     if it is @('t'), we have encountered it already.
     Thus, it is an error if the @('definedp') flag in the table
     and the @('definedp') parameter of this ACL2 function are both @('t'),
     because it means that there are two definitions.
     For the other three combinations of the flags there is no error,
     but if the flag in the table is @('nil')
     while the parameter of this ACL2 function is @('t'),
     then we update the flag in the table,
     because now the function is defined."))
  (b* ((fun (ident-fix fun))
       (funtab (fun-table-fix funtab))
       (info (fun-table-lookup fun funtab))
       ((when (not info))
        (omap::update fun
                      (make-fun-sinfo :inputs inputs
                                      :output output
                                      :definedp definedp)
                      funtab))
       ((unless (and (type-list-equiv (fun-sinfo->inputs info)
                                      inputs)
                     (type-equiv (fun-sinfo->output info)
                                 output)))
        (reserrf (list :fun-type-mismatch
                       :old-inputs (fun-sinfo->inputs info)
                       :new-inputs (type-list-fix inputs)
                       :old-output (fun-sinfo->output info)
                       :new-output (type-fix output))))
       (already-definedp (fun-sinfo->definedp info))
       ((when (and already-definedp definedp))
        (reserrf (list :fun-redefinition fun)))
       ((when (and (not already-definedp) definedp))
        (omap::update fun
                      (change-fun-sinfo info :definedp t)
                      funtab)))
    funtab)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-table-all-definedp ((funtab fun-tablep))
  :returns (yes/no booleanp)
  :short "Check if all the functions in a table are defined."
  (b* ((funtab (fun-table-fix funtab))
       ((when (omap::empty funtab)) t)
       ((mv & info) (omap::head funtab))
       ((unless (fun-sinfo->definedp info)) nil))
    (fun-table-all-definedp (omap::tail funtab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-member-lookup ((tag identp) (mem identp) (tagenv tag-envp))
  :returns (type type-resultp)
  :short "Look up a member in a structure type in the tag environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first look up the tag, ensuring we find a structure type.
     Then we look for the member in the structure type,
     returning its type if successful.
     We propagate errors.")
   (xdoc::p
    "This is used to check member expressions,
     both the @('.') kind and the @('->') kind."))
  (b* ((info (tag-env-lookup tag tagenv))
       ((when (tag-info-option-case info :none))
        (reserrf (list :struct-not-found
                       (ident-fix tag)
                       (tag-env-fix tagenv))))
       (info (tag-info-option-some->val info))
       ((unless (tag-info-case info :struct))
        (reserrf (list :tag-not-struct
                       (ident-fix tag)
                       info)))
       (members (tag-info-struct->members info))
       (type (member-type-lookup mem members))
       ((when (type-option-case type :none))
        (reserrf (list :member-not-found
                       (ident-fix tag)
                       (ident-fix mem)
                       members))))
    (type-option-some->val type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defunit wellformed
  :short "Fixtype of the well-formedness indicator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is returned by the ACL2 static semantic checking functions
     when an abstract syntactic entity passes the static semantic checks
     and there is no additional information to return.
     When the static semantic checks fail,
     those functions return errors instead;
     see @(tsee wellformed-result)."))
  :value :wellformed
  :pred wellformedp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult wellformed-result
  :short "Fixtype of errors and the @(tsee wellformed) indicator."
  :ok wellformed
  :pred wellformed-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-type
  :short "Fixtype of expression types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain C expressions are lvalues [C:6.3.2/1],
     i.e. they evaluate to object designations rather than values [C:6.5/1].
     In many cases, lvalue conversion [C:6.3.2/2]
     turns an object designation into the value of the designated object,
     but some operators (e.g. assignments) require lvalues.
     Thus, the static semantics must calculate, for each expression,
     not only its type, but also whether it is an lvalue or not.
     This information is captured via a type and an lvalue flag.")
   (xdoc::p
    "Expressions may also evaluate to function designations [C:6.5/1].
     We do not cover that case for now,
     because our subset of C makes a limited use of functions;
     in particular, it has no function pointers.
     However, in the future this fixtype could be extended accordingly."))
  ((type type)
   (lvalue bool))
  :tag :expr-type
  :pred expr-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-type-result
  :short "Fixtype of errors and expression types."
  :ok expr-type
  :pred expr-type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod types+vartab
  :short "Fixtype of pairs consisting of
          a non-empty set of types and a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the information inferred by the static semantics
     about a statement (or block item or block).
     The information consists of:")
   (xdoc::ul
    (xdoc::li
     "A non-empty set of types that describes
      the possible values returned by the statement.
      These are determined by the @('return') statements;
      in the presence of conditionals,
      the possible types in the two branches are merged (i.e. unioned).
      The type @('void') is used to describe statements
      that do not return a value,
      but instead transfer control to the next statement (if any).")
    (xdoc::li
     "A possibly updated variable table.
      This is updated by block items that are declarations.
      We actually only need to return possibly updated variable tables
      from the ACL2 function @(tsee check-block-item);
      the ACL2 functions @(tsee check-stmt) and @(tsee check-block-item-list)
      could just return a set of types (see above).
      However, for uniformity we have all three functions
      return also a possibly updated variable table.")))
  ((return-types type-set :reqfix (if (set::emptyp return-types)
                                      (set::insert (type-void) nil)
                                    return-types))
   (variables var-table))
  :require (not (set::emptyp return-types))
  :pred types+vartab-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult types+vartab-result
  :short "Fixtype of errors and pairs consisting of
          a non-empty set of types and a variable table."
  :ok types+vartab
  :pred types+vartab-resultp)

;;;;;;;;;;;;;;;;;;;;

(defrule not-types+vartab-p-of-error
  (not (types+vartab-p (reserrf x)))
  :enable (fty::reserr types+vartab-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funtab+vartab+tagenv
  :short "Fixtype of triples consisting of
          a function table, a variable table, and a tag environment."
  ((funs fun-tablep)
   (vars var-tablep)
   (tags tag-envp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funtab+vartab+tagenv-result
  :short "Fixtype of errors and triples consisting of
          a function table, a variable table, and a tag environment."
  :ok funtab+vartab+tagenv
  :pred funtab+vartab+tagenv-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-type ((type typep))
  :guard (type-arithmeticp type)
  :returns (promoted-type typep)
  :short "Apply the integer promotions to an arithmetic type [C:6.3.1.1/2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the static counterpart of
     the integer promotions that are applied to values:
     statically, they are applied to types.")
   (xdoc::p
    "These only modify the character and short types;
     all the other types are unchanged.")
   (xdoc::p
    "If @('int') can represent all the values of the original type,
     the promotion is to @('int'):
     this is always the case for @('signed char') and @('signed short'),
     but not necessarily for @('char') (which may be signed or not),
     @('unsigned char'), and @('unsigned short').
     In the unlikely but allowed case that
     a byte consists of 16 bits and that @('int') also consists of 16 bits,
     some @('unsigned char') values are not representable in @('int').
     Otherwise, the promotion is to @('unsigned int').")
   (xdoc::p
    "The plain @('char') type is not supported for now. It will be soon."))
  (case (type-kind type)
    (:char (prog2$ (raise "Internal error: plain char type not supported.")
                   (type-sint)))
    (:schar (type-sint))
    (:uchar (if (<= (uchar-max) (sint-max)) (type-sint) (type-uint)))
    (:sshort (type-sint))
    (:ushort (if (<= (ushort-max) (sint-max)) (type-sint) (type-uint)))
    (t (type-fix type)))
  :hooks (:fix)
  ///

  (defrule type-arithmeticp-of-promote-type
    (equal (type-arithmeticp (promote-type type))
           (type-arithmeticp type))
    :enable (promote-type
             type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defrule type-promoted-arithmeticp-of-promote-type
    (equal (type-promoted-arithmeticp (promote-type type))
           (type-arithmeticp type))
    :enable (type-promoted-arithmeticp
             type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defrule type-integerp-of-promote-type
    (equal (type-integerp (promote-type type))
           (type-integerp type))
    :enable (type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defrule type-nonchar-integerp-of-promote-type
    (implies (type-nonchar-integerp type)
             (type-nonchar-integerp (promote-type type)))
    :enable type-nonchar-integerp)

  (defruled promote-type-when-not-type-integerp
    (implies (not (type-integerp type))
             (equal (promote-type type)
                    (type-fix type)))
    :enable (type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defrule type-kind-of-promote-type-not-schar
    (not (equal (type-kind (promote-type type))
                :schar)))

  (defrule type-kind-of-promote-type-not-uchar
    (not (equal (type-kind (promote-type type))
                :uchar)))

  (defrule type-kind-of-promote-type-not-sshort
    (not (equal (type-kind (promote-type type))
                :sshort)))

  (defrule type-kind-of-promote-type-not-ushort
    (not (equal (type-kind (promote-type type))
                :ushort))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uaconvert-types ((type1 typep) (type2 typep))
  :guard (and (type-arithmeticp type1)
              (type-arithmeticp type2))
  :returns (type typep)
  :short "Apply the usual arithmetic conversions to two arithmetic types
          [C:6.3.1.8]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These determine a common type from the two types,
     which is also the type of the result of
     a binary operator applied to operands of the two types."))
  (b* ((type1 (promote-type type1))
       (type2 (promote-type type2))
       ((acl2::fun (irr-type)) (ec-call (type-fix :irrelevant))))
    (case (type-kind type1)
      (:sllong (case (type-kind type2)
                 (:sllong (type-sllong))
                 (:slong (type-sllong))
                 (:sint (type-sllong))
                 (:ullong (type-ullong))
                 (:ulong (if (>= (sllong-max) (ulong-max))
                             (type-sllong)
                           (type-ullong)))
                 (:uint (if (>= (sllong-max) (uint-max))
                            (type-sllong)
                          (type-ullong)))
                 (t (prog2$ (impossible) (irr-type)))))
      (:slong (case (type-kind type2)
                (:sllong (type-sllong))
                (:slong (type-slong))
                (:sint (type-slong))
                (:ullong (type-ullong))
                (:ulong (type-ulong))
                (:uint (if (>= (slong-max) (uint-max))
                           (type-slong)
                         (type-ulong)))
                (t (prog2$ (impossible) (irr-type)))))
      (:sint (case (type-kind type2)
               (:sllong (type-sllong))
               (:slong (type-slong))
               (:sint (type-sint))
               (:ullong (type-ullong))
               (:ulong (type-ulong))
               (:uint (type-uint))
               (t (prog2$ (impossible) (irr-type)))))
      (:ullong (case (type-kind type2)
                 (:sllong (type-ullong))
                 (:slong (type-ullong))
                 (:sint (type-ullong))
                 (:ullong (type-ullong))
                 (:ulong (type-ullong))
                 (:uint (type-ullong))
                 (t (prog2$ (impossible) (irr-type)))))
      (:ulong (case (type-kind type2)
                (:sllong (if (>= (sllong-max) (ulong-max))
                             (type-sllong)
                           (type-ullong)))
                (:slong (type-ulong))
                (:sint (type-ulong))
                (:ullong (type-ullong))
                (:ulong (type-ulong))
                (:uint (type-ulong))
                (t (prog2$ (impossible) (irr-type)))))
      (:uint (case (type-kind type2)
               (:sllong (if (>= (sllong-max) (uint-max))
                            (type-sllong)
                          (type-ullong)))
               (:slong (if (>= (slong-max) (uint-max))
                           (type-slong)
                         (type-ulong)))
               (:sint (type-uint))
               (:ullong (type-ullong))
               (:ulong (type-ulong))
               (:uint (type-uint))
               (t (prog2$ (impossible) (irr-type)))))
      (t (prog2$ (impossible) (irr-type)))))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-realp
                                           type-integerp
                                           type-signed-integerp
                                           type-unsigned-integerp
                                           promote-type)))
  :hooks (:fix)
  ///

  (defrule type-arithmeticp-of-uaconvert-types
    (equal (type-arithmeticp (uaconvert-types type1 type2))
           (and (type-arithmeticp type1)
                (type-arithmeticp type2)))
    :enable (promote-type
             type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defrule type-integerp-of-uaconvert-types
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2))
             (equal (type-integerp (uaconvert-types type1 type2))
                    (and (type-integerp type1)
                         (type-integerp type2))))
    :enable (promote-type
             type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp))

  (defret type-nonchar-integerp-of-uaconvert-types
    (type-nonchar-integerp type)
    :hyp (and (type-integerp type1)
              (type-integerp type2))
    :hints (("Goal" :in-theory (enable promote-type
                                       type-integerp
                                       type-unsigned-integerp
                                       type-signed-integerp))))


  (defrule type-kind-of-uaconvert-types-not-schar
    (not (equal (type-kind (uaconvert-types type1 type2))
                :schar)))

  (defrule type-kind-of-uaconvert-types-not-uchar
    (not (equal (type-kind (uaconvert-types type1 type2))
                :uchar)))

  (defrule type-kind-of-uaconvert-types-not-sshort
    (not (equal (type-kind (uaconvert-types type1 type2))
                :sshort)))

  (defrule type-kind-of-uaconvert-types-not-ushort
    (not (equal (type-kind (uaconvert-types type1 type2))
                :ushort)))

  (defruled uaconvert-types-when-same
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2)
                  (type-equiv type1 type2))
             (equal (uaconvert-types type1 type2)
                    (promote-type type1)))
    :enable (promote-type
             type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp))

  (defruled uaconvert-types-symmetry
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2))
             (equal (uaconvert-types type1 type2)
                    (uaconvert-types type2 type1)))
    :enable (promote-type
             type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apconvert-type ((type typep))
  :returns (type1 typep)
  :short "Convert array type to pointer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Under most circumstances,
     an array is converted to a pointer to the first element of the array
     [C:6.3.2.1/3];
     indeed, arrays are used like pointers most of the time.")
   (xdoc::p
    "This conversion is captured, at the level of types, here.
     Non-array types are left unchanged.")
   (xdoc::p
    "The dynamic counterpart of this is @(tsee apconvert-expr-value)."))
  (if (type-case type :array)
      (type-pointer (type-array->of type))
    (type-fix type))
  :hooks (:fix)
  ///

  (defrule type-arithmeticp-of-apconvert-type
    (equal (type-arithmeticp (apconvert-type type))
           (type-arithmeticp type))
    :enable (type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection apconvert-type-list (x)
  :guard (type-listp x)
  :returns (types1 type-listp)
  :short "Lift @(tsee apconvert-type) to lists."
  (apconvert-type x)
  ///
  (fty::deffixequiv apconvert-type-list
    :args ((x type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define adjust-type ((type typep))
  :returns (type1 typep)
  :short "Adjust a parameter type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Function parameter types are subject to an adjustment [C:6.7.6.3/7]:
     an array type is converted to a pointer type to the element type.
     Since we currently do not model type qualifiers,
     we do not need to take those into account here.
     Note that the size, if present, is lost."))
  (if (type-case type :array)
      (make-type-pointer :to (type-array->of type))
    (type-fix type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection adjust-type-list (x)
  :guard (type-listp x)
  :returns (types1 type-listp)
  :short "Lift @(tsee adjust-type) to lists."
  (adjust-type x)
  ///
  (fty::deffixequiv adjust-type-list
    :args ((x type-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ident ((id identp))
  :returns (wf? wellformed-resultp)
  :short "Check an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether the underlying ACL2 string forms a "
    (xdoc::seetopic "portable-ascii-identifiers" "portable ASCII identifier")
    "."))
  (if (paident-stringp (ident->name id))
      :wellformed
    (reserrf (list :illegal/unsupported-ident (ident-fix id))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-iconst ((ic iconstp))
  :returns (type type-resultp)
  :short "Check an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to [C:6.4.4.1/5]:
     based on the suffixes and the base,
     we find the first type that suffices to represent the value,
     in the lists indicated in the table,
     and we return that type.
     If the value is too large, the integer constant is illegal.")
   (xdoc::p
    "This is the static counterpart of @(tsee eval-iconst)."))
  (b* ((ic (iconst-fix ic))
       ((iconst ic) ic))
    (if ic.unsignedp
        (iconst-length-case
         ic.length
         :none (cond ((uint-integerp ic.value) (type-uint))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (reserrf (list :iconst-out-of-range ic))))
         :long (cond ((ulong-integerp ic.value) (type-ulong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (reserrf (list :iconst-out-of-range ic))))
         :llong (cond ((ullong-integerp ic.value) (type-ullong))
                      (t (reserrf (list :iconst-out-of-range ic)))))
      (iconst-length-case
       ic.length
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (type-sint))
                       ((slong-integerp ic.value) (type-slong))
                       ((sllong-integerp ic.value) (type-sllong))
                       (t (reserrf (list :iconst-out-of-range ic))))
               (cond ((sint-integerp ic.value) (type-sint))
                     ((uint-integerp ic.value) (type-uint))
                     ((slong-integerp ic.value) (type-slong))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((sllong-integerp ic.value) (type-sllong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (reserrf (list :iconst-out-of-range ic)))))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (type-slong))
                       ((sllong-integerp ic.value) (type-sllong))
                       (t (reserrf (list :iconst-out-of-range ic))))
               (cond ((slong-integerp ic.value) (type-slong))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((sllong-integerp ic.value) (type-sllong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (reserrf (list :iconst-out-of-range ic)))))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (type-sllong))
                        (t (reserrf (list :iconst-out-of-range ic))))
                (cond ((sllong-integerp ic.value) (type-sllong))
                      ((ullong-integerp ic.value) (type-ullong))
                      (t (reserrf (list :iconst-out-of-range ic))))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-const ((c constp))
  :returns (etype expr-type-resultp)
  :short "Check a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only accept integer constants.")
   (xdoc::p
    "We return an expression type.
     A constant is never an lvalue.")
   (xdoc::p
    "This is the static counterpart of @(tsee exec-const)."))
  (const-case c
              :int (b* (((okf type) (check-iconst c.get)))
                     (make-expr-type :type type :lvalue nil))
              :float (reserrf (list :unsupported-float-const (const-fix c)))
              :enum (reserrf (list :unsupported-enum-const (const-fix c)))
              :char (reserrf (list :unsupported-char-const (const-fix c))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tyspecseq ((tyspec tyspecseqp) (tagenv tag-envp))
  :returns (type type-resultp)
  :short "Check a type specifier sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the type denoted by the type specifier sequence.")
   (xdoc::p
    "We only accept certain type specifier sequences for now,
     namely the ones that have corresponding types in our model.
     The tag of a structure type specifier sequence
     must be in the tag environment.
     All the other (supported) type specifier sequences
     are always well-formed."))
  (tyspecseq-case
   tyspec
   :void (type-void)
   :char (type-char)
   :schar (type-schar)
   :uchar (type-uchar)
   :sshort (type-sshort)
   :ushort (type-ushort)
   :sint (type-sint)
   :uint (type-uint)
   :slong (type-slong)
   :ulong (type-ulong)
   :sllong (type-sllong)
   :ullong (type-ullong)
   :bool (reserrf (list :not-supported-bool))
   :float (reserrf (list :not-supported-float))
   :double (reserrf (list :not-supported-double))
   :ldouble (reserrf (list :not-supported-ldouble))
   :struct (b* ((info (tag-env-lookup tyspec.tag tagenv)))
             (tag-info-option-case
              info
              :some (if (tag-info-case info.val :struct)
                        (type-struct tyspec.tag)
                      (reserrf (list :struct-tag-mismatch tyspec.tag info.val)))
              :none (reserrf (list :no-tag-found tyspec.tag))))
   :union (reserrf (list :not-supported-union tyspec.tag))
   :enum (reserrf (list :not-supported-enum tyspec.tag))
   :typedef (reserrf (list :not-supported-typedef tyspec.name)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-obj-adeclor ((declor obj-adeclorp) (type typep))
  :returns (type type-resultp)
  :short "Check an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is checked with respect to a type,
     which initially is the type denoted by the type specifier sequence
     that precedes the abstract object declarator,
     and then is the type obtained by augmenting that initial type
     with the layers that form the abstract object declarator.")
   (xdoc::p
    "When we reach the end of the abstract object declarator,
     we just return the type.
     If we find a pointer layer,
     we wrap the type into a pointer type
     and we continue through the subsequent layers recursively.
     If we find an array layer,
     we ensure that the current type, which is the element type,
     is complete [C:6.2.5/20].
     If the array size is present,
     we check that it is well-formed and non-zero,
     and we use its value as the array size.
     Whether the size is present or not,
     we wrap the type into an array type
     and we continue through the subsequent layers recursively."))
  (obj-adeclor-case
   declor
   :none (type-fix type)
   :pointer (check-obj-adeclor declor.decl (type-pointer type))
   :array (b* (((unless (type-completep type))
                (reserrf (list :incomplete-array-type-element
                               (type-fix type)
                               (obj-adeclor-fix declor))))
               ((unless declor.size)
                (check-obj-adeclor declor.decl
                                   (make-type-array :of type :size nil)))
               ((okf &) (check-iconst declor.size))
               (size (iconst->value declor.size))
               ((when (equal size 0))
                (reserrf (list :zero-size-array-type
                               (type-fix type)
                               (obj-adeclor-fix declor)))))
            (check-obj-adeclor declor.decl
                               (make-type-array :of type :size size))))
  :measure (obj-adeclor-count declor)
  :hints (("Goal" :in-theory (enable o< o-p o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tyname ((tyname tynamep) (tagenv tag-envp))
  :returns (type type-resultp)
  :short "Check a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the denoted type if successful.
     We first check the type specifier sequence,
     then the abstracto object declarator."))
  (b* (((okf type) (check-tyspecseq (tyname->tyspec tyname) tagenv)))
    (check-obj-adeclor (tyname->declor tyname) type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-unary ((op unopp) (arg-expr exprp) (arg-etype expr-typep))
  :returns (etype expr-type-resultp)
  :short "Check the application of a unary operator to an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check @('arg-etype') against @('op');
     @('arg-expr') is used just for errors.
     We return the type of the unary expression.")
   (xdoc::p
    "The operand of the address operator must be an lvalue [C:6.5.3.2/1].
     The text in [C:6.5.3.2/1] talks about lvalues
     but singles out postfix @('[]') expressions and unary @('*') expressions,
     even though those are just special cases of lvalues;
     perhaps this has to do with the restriction about
     the bit-field and the @('register'),
     but since none of these are covered in our current C model,
     we can just say that, for us, the argument of @('&') must be an lvalue.
     This is why this ACL2 function takes an expression type, not just a type,
     for the argument:
     it is so that we can check the @('&') operator;
     checking the other operators only involves the type.
     If the type of the argument is @('T'),
     the type of the result is pointer to @('T')
     [C:6.5.3.2/3];
     the expression is not an lvalue.")
   (xdoc::p
    "The operand of the indirection operator must be a pointer [C:6.5.3.2/2].
     The result has the referenced type,
     and the expression is an lvalue
     [C:6.5.3.2/4].
     We return an expression type, not a type,
     so that we can represent the fact that
     an indirection expression is an lvalue.
     All the other unary expressions are not lvalues.")
   (xdoc::p
    "For unary plus and minus,
     the operand must be arithmetic,
     and the result has the promoted type.")
   (xdoc::p
    "For bitwise negation,
     the operand must be integer,
     and the result has the promoted type.")
   (xdoc::p
    "For logical negation,
     the operand must be scalar
     and the result is @('int') -- 0 or 1.")
   (xdoc::p
    "For all operators except @('&'), the argument is subjected to
     lvalue conversion [C:6.3.2.1/2]
     and array-to-pointer conversion [C:6.3.2.1/3].
     In our static semantics, lvalue conversion just amounts to
     ignoring the @('lvalue') flag of the expression type."))
  (case (unop-kind op)
    (:address (if (expr-type->lvalue arg-etype)
                  (make-expr-type
                   :type (type-pointer (expr-type->type arg-etype))
                   :lvalue nil)
                (reserrf (list :unary-mistype
                               (unop-fix op) (expr-fix arg-expr)
                               :required :lvalue
                               :supplied (expr-type-fix arg-etype)))))
    (:indir (b* ((arg-type (expr-type->type arg-etype))
                 (arg-type (apconvert-type arg-type)))
              (if (type-case arg-type :pointer)
                  (make-expr-type :type (type-pointer->to arg-type)
                                  :lvalue t)
                (reserrf (list :unary-mistype
                               (unop-fix op) (expr-fix arg-expr)
                               :required :pointer
                               :supplied arg-type)))))
    ((:plus :minus) (b* ((arg-type (expr-type->type arg-etype))
                         (arg-type (apconvert-type arg-type)))
                      (if (type-arithmeticp arg-type)
                          (make-expr-type :type (promote-type arg-type)
                                          :lvalue nil)
                        (reserrf (list :unary-mistype
                                       (unop-fix op) (expr-fix arg-expr)
                                       :required :arithmetic
                                       :supplied (type-fix arg-type))))))
    (:bitnot (b* ((arg-type (expr-type->type arg-etype))
                  (arg-type (apconvert-type arg-type)))
               (if (type-integerp arg-type)
                   (make-expr-type :type (promote-type arg-type) :lvalue nil)
                 (reserrf (list :unary-mistype
                                (unop-fix op) (expr-fix arg-expr)
                                :required :integer
                                :supplied (type-fix arg-type))))))
    (:lognot (b* ((arg-type (expr-type->type arg-etype))
                  (arg-type (apconvert-type arg-type)))
               (if (type-scalarp arg-type)
                   (make-expr-type :type (type-sint) :lvalue nil)
                 (reserrf (list :unary-mistype
                                (unop-fix op) (expr-fix arg-expr)
                                :required :scalar
                                :supplied (type-fix arg-type))))))
    (t (reserrf (impossible))))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-realp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-binary-pure ((op binopp)
                           (arg1-expr exprp) (arg1-etype expr-typep)
                           (arg2-expr exprp) (arg2-etype expr-typep))
  :guard (binop-purep op)
  :returns (etype expr-type-resultp)
  :short "Check the application of a pure binary operator to two expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check @('arg1-etype') and @('arg2-etype') against @('op');
     @('arg1-expr') and @('arg2-expr') are used just for errors.
     We return the type of the binary expression;
     a binary pure expression is never an lvalue.")
   (xdoc::p
    "For multiplication, division, and reminder,
     the operands must be arithmetic,
     and the result has the type of the usual arithmetic conversions.")
   (xdoc::p
    "For addition and subtraction,
     for now we require the operands to be arithmetic,
     and the result has the type of the usual arithmetic conversions.
     We do not yet support arithmetic involving pointers.")
   (xdoc::p
    "For left and right shifts,
     the operands must be integers,
     and the result has the type of the promoted first operand.")
   (xdoc::p
    "For the relational operators,
     for now we require the operands to be real,
     and the result has type @('int').
     We do not yet support comparisons between pointers.")
   (xdoc::p
    "For the equality operators,
     for now we require the operands to be arithmetic,
     and the result has type @('int').
     We do not yet support equalities between pointers.")
   (xdoc::p
    "For the bitwise logical operators,
     the operands must be integers,
     and the result has the type of the usual arithmetic conversions.")
   (xdoc::p
    "For the conditional logical operators,
     the operands must be scalar,
     and the result is @('int')."))
  (b* ((arg1-type (apconvert-type (expr-type->type arg1-etype)))
       (arg2-type (apconvert-type (expr-type->type arg2-etype)))
       ((okf type)
        (case (binop-kind op)
          ((:mul :div :rem :add :sub)
           (if (and (type-arithmeticp arg1-type)
                    (type-arithmeticp arg2-type))
               (uaconvert-types arg1-type arg2-type)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :arithmetic :arithmetic
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          ((:shl :shr)
           (if (and (type-integerp arg1-type)
                    (type-integerp arg2-type))
               (promote-type arg1-type)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :integer :integer
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          ((:lt :gt :le :ge)
           (if (and (type-realp arg1-type)
                    (type-realp arg2-type))
               (type-sint)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :real :real
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          ((:eq :ne)
           (if (and (type-arithmeticp arg1-type)
                    (type-arithmeticp arg2-type))
               (type-sint)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :arithmetic :arithmetic
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          ((:bitand :bitxor :bitior)
           (if (and (type-integerp arg1-type)
                    (type-integerp arg2-type))
               (uaconvert-types arg1-type arg2-type)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :integer :integer
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          ((:logand :logor)
           (if (and (type-scalarp arg1-type)
                    (type-scalarp arg2-type))
               (type-sint)
             (reserrf (list :binary-mistype
                            (binop-fix op)
                            (expr-fix arg1-expr)
                            (expr-fix arg2-expr)
                            :required :integer :integer
                            :supplied
                            (type-fix arg1-type)
                            (type-fix arg2-type)))))
          (t (reserrf (impossible))))))
    (make-expr-type :type type :lvalue nil))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-realp
                                           binop-purep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-cast ((arg-expr exprp)
                    (arg-etype expr-typep)
                    (tyname tynamep)
                    (tagenv tag-envp))
  :returns (etype expr-type-resultp)
  :short "Check a cast expression [C:6.5.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A cast is allowed between scalar types.
     The result has the type indicated in the cast.
     See [C:6.5.4]; note that the additional requirements on the type
     do not apply to our currently simplified model of C types.
     We apply lvalue conversion to the operand.
     We also apply array-to-pointer conversion,
     which could turn an array into a pointer (and thus scalar) type.
     A cast expression is never an lvalue."))
  (b* ((arg-type (expr-type->type arg-etype))
       (arg-type (apconvert-type arg-type))
       ((unless (type-scalarp arg-type))
        (reserrf (list :cast-mistype-operand (expr-fix arg-expr)
                       :required :scalar
                       :supplied arg-type)))
       ((okf type) (check-tyname tyname tagenv))
       ((unless (type-scalarp type))
        (reserrf (list :cast-mistype-type (expr-fix arg-expr)
                       :required :scalar
                       :supplied type))))
    (make-expr-type :type type :lvalue nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-cond ((test-expr exprp) (test-etype expr-typep)
                    (then-expr exprp) (then-etype expr-typep)
                    (else-expr exprp) (else-etype expr-typep))
  :returns (etype expr-type-resultp)
  :short "Check a ternary conditional expression [C:6.5.15]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The test of a conditional expression must be scalar.
     For now we require the two branches to have arithmetic types.
     According to [C:6.5.15/3],
     in this case the type of the conditional expression
     is the one resulting from the usual arithmetic conversions [C:6.5.15/5].
     This means that, at run time, in our dynamic semantics of C,
     we need to convert the branch that is executed to that type;
     but at run time we do not have information about
     the type of the other branch (the one that is not executed).
     Thus, in order to handle the execution properly,
     the static semantics should add information to the abstract syntax
     about the resulting type of the conditional expression,
     so that the dynamic semantics can perform the conversion
     while evaluating just one branch.
     (Presumably, C compilers would generate code that performs the conversion,
     if needed, for both branches of the conditional expression.)
     To avoid this complication,
     for now we make our static semantics more restrictive:
     we require the two branches to have the same promoted type.
     This means that that promoted type is also
     the type resulting from the usual arithmetic conversions,
     as can be easily seen in @(tsee uaconvert-types).
     We may relax the treatment eventually,
     but note that we would have to restructure the static semantics
     to return possibly modified abstract syntax.
     This is not surprising, as it is a used approach for compiler-like tools,
     namely annotating abstract syntax trees with additional information.
     We apply both lvalue conversion and array-to-pointer conversion.
     A conditional expression is never an lvalue.")
   (xdoc::p
    "We perform lvalue conversion and array-to-pointer conversion
     on all three operands.
     A conditional expression is never an lvalue."))
  (b* ((test-expr (expr-fix test-expr))
       (then-expr (expr-fix then-expr))
       (else-expr (expr-fix else-expr))
       (test-type (expr-type->type test-etype))
       (then-type (expr-type->type then-etype))
       (else-type (expr-type->type else-etype))
       (test-type (apconvert-type test-type))
       (then-type (apconvert-type then-type))
       (else-type (apconvert-type else-type))
       ((unless (type-scalarp test-type))
        (reserrf (list :cond-mistype-test test-expr then-expr else-expr
                       :required :scalar
                       :supplied test-type)))
       ((unless (type-arithmeticp then-type))
        (reserrf (list :cond-mistype-then test-expr then-expr else-expr
                       :required :arithmetic
                       :supplied then-type)))
       ((unless (type-arithmeticp else-type))
        (reserrf (list :cond-mistype-else test-expr then-expr else-expr
                       :required :arithmetic
                       :supplied else-type)))
       (then-type (promote-type then-type))
       (else-type (promote-type else-type))
       ((unless (equal then-type else-type))
        (reserrf (list :diff-promoted-types then-type else-type)))
       (type then-type))
    (make-expr-type :type type :lvalue nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-arrsub ((arr-expr exprp) (arr-etype expr-typep)
                      (sub-expr exprp) (sub-etype expr-typep))
  :returns (etype expr-type-resultp)
  :short "Check an array subscripting expression [C:6.5.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check @('arr-etype') and @('sub-etype');
     @('arr-expr') and @('sub-expr') are just used for errors.")
   (xdoc::p
    "We do lvalue conversion for both operands,
     via @(tsee expr-type->type).
     According to [C:6.3.2/2],
     we should not do this for if an operand has an array type;
     however, according to [C:6.3.2/3],
     we should convert the array to a pointer
     (which we do via @(tsee apconvert-type)),
     and thus in the end the result is the same:
     we have a pointer type that does not denote an lvalue,
     if the operand is an array.
     If an operand is an integer, @(tsee apconvert-type) has no effect.")
   (xdoc::p
    "The first expression must have a pointer type [C:6.5.2.1/1].
     The second expression must have an integer type [C:6.5.2.1/1].
     The type of the array subscripting expression
     is the type referenced by the pointer.
     An array subscripting expression is always an lvalue.")
   (xdoc::p
    "For now we do not allow the roles of the expressions to be swapped,
     i.e. that the second expression is a pointer and the first one an integer;
     note the symmetry in [C:6.5.2.1/2]."))
  (b* ((arr-type (apconvert-type (expr-type->type arr-etype)))
       (sub-type (apconvert-type (expr-type->type sub-etype)))
       ((unless (type-case arr-type :pointer))
        (reserrf (list :array-mistype (expr-fix arr-expr)
                       :required :pointer
                       :supplied (type-fix arr-type))))
       ((unless (type-integerp sub-type))
        (reserrf (list :subscript-mistype (expr-fix sub-expr)
                       :required :integer
                       :supplied (type-fix sub-type)))))
    (make-expr-type :type (type-pointer->to arr-type) :lvalue t))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-member ((target-expr exprp)
                      (target-etype expr-typep)
                      (name identp)
                      (tagenv tag-envp))
  :returns (etype expr-type-resultp)
  :short "Check a structure member expression [C:6.5.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the target has a structure type.
     We do not do need to do array-to-pointer conversion,
     because we require the type to be a structure type,
     which rejects both array and pointer types.
     We look up the structure type and its member.
     We return its type, and we preserve the lvalue status:
     if the target is an lvalue, so is the member;
     if the target is not an lvalue, neither is the member."))
  (b* ((target-type (expr-type->type target-etype))
       (target-lvalue (expr-type->lvalue target-etype))
       ((unless (type-case target-type :struct))
        (reserrf (list :dot-target-not-struct (expr-fix target-expr))))
       (tag (type-struct->tag target-type))
       ((okf memtype) (struct-member-lookup tag name tagenv)))
    (make-expr-type :type memtype :lvalue target-lvalue))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-memberp ((target-expr exprp)
                       (target-etype expr-typep)
                       (name identp)
                       (tagenv tag-envp))
  :returns (etype expr-type-resultp)
  :short "Check a structure pointer member expression [C:6.5.2.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the target has a pointer type to a structure type.
     We perform array-to-pointer conversion on this type,
     prior to ensuring it is a pointer to structure,
     as an array type would become a pointer type via that conversion.
     We look up the structure type and its member.
     We return the member type, with the lvalue flag set."))
  (b* ((target-type (expr-type->type target-etype))
       (target-type (apconvert-type target-type))
       ((unless (type-case target-type :pointer))
        (reserrf (list :arrow-operator-not-pointer (expr-fix target-expr))))
       (type (type-pointer->to target-type))
       ((unless (type-case type :struct))
        (reserrf (list :arrow-operator-not-pointer-to-struct
                       (expr-fix target-expr))))
       (tag (type-struct->tag type))
       ((okf memtype) (struct-member-lookup tag name tagenv)))
    (make-expr-type :type memtype :lvalue t))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-pure ((e exprp) (vartab var-tablep) (tagenv tag-envp))
  :returns (etype expr-type-resultp)
  :short "Check a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, we check whether an expression is pure and well-formed.
     If all the checks are satisfied,
     we return the expression type of the expression
     (see @(tsee expr-type)).")
   (xdoc::p
    "We disallow function calls and pre/post-increment/decrement,
     since they are not pure.
     We only allow pure binary operators.")
   (xdoc::p
    "An identifier must be in the variable table.
     Its type is looked up there.
     An identifier is always an lvalue."))
  (b* ((e (expr-fix e)))
    (expr-case
     e
     :ident (b* ((info (var-table-lookup e.get vartab))
                 ((unless info) (reserrf (list :var-not-found e.get))))
              (make-expr-type :type (var-sinfo->type info) :lvalue t))
     :const (check-const e.get)
     :arrsub (b* (((okf arr-etype) (check-expr-pure e.arr vartab tagenv))
                  ((okf sub-etype) (check-expr-pure e.sub vartab tagenv)))
               (check-arrsub e.arr arr-etype e.sub sub-etype))
     :call (reserrf (list :expr-non-pure e))
     :member (b* (((okf etype) (check-expr-pure e.target vartab tagenv)))
               (check-member e.target etype e.name tagenv))
     :memberp (b* (((okf etype) (check-expr-pure e.target vartab tagenv)))
                (check-memberp e.target etype e.name tagenv))
     :postinc (reserrf (list :expr-non-pure e))
     :postdec (reserrf (list :expr-non-pure e))
     :preinc (reserrf (list :expr-non-pure e))
     :predec (reserrf (list :expr-non-pure e))
     :unary (b* (((okf arg-etype) (check-expr-pure e.arg vartab tagenv)))
              (check-unary e.op e.arg arg-etype))
     :cast (b* (((okf arg-etype) (check-expr-pure e.arg vartab tagenv)))
             (check-cast e.arg arg-etype e.type tagenv))
     :binary (b* (((unless (binop-purep e.op))
                   (reserrf (list :binary-non-pure e)))
                  ((okf arg1-etype) (check-expr-pure e.arg1 vartab tagenv))
                  ((okf arg2-etype) (check-expr-pure e.arg2 vartab tagenv)))
               (check-binary-pure e.op e.arg1 arg1-etype e.arg2 arg2-etype))
     :cond (b* (((okf test-etype) (check-expr-pure e.test vartab tagenv))
                ((okf then-etype) (check-expr-pure e.then vartab tagenv))
                ((okf else-etype) (check-expr-pure e.else vartab tagenv)))
             (check-cond e.test test-etype
                         e.then then-etype
                         e.else else-etype))))
  :measure (expr-count e)
  :hints (("Goal" :in-theory (enable o< o-p o-finp)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-pure-list ((es expr-listp)
                              (vartab var-tablep)
                              (tagenv tag-envp))
  :returns (types type-list-resultp
                  :hints (("Goal"
                           :in-theory
                           (enable
                            typep-when-type-resultp-and-not-reserrp
                            type-listp-when-type-list-resultp-and-not-reserrp))))
  :short "Check a list of pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for arguments of function calls.
     The expression types returned by the expressions
     are subjected to lvalue conversion and array-to-pointer conversion."))
  (b* (((when (endp es)) nil)
       ((okf etype) (check-expr-pure (car es) vartab tagenv))
       (type (expr-type->type etype))
       (type (apconvert-type type))
       ((okf types) (check-expr-pure-list (cdr es) vartab tagenv)))
    (cons type types))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-call ((fun identp)
                         (args expr-listp)
                         (funtab fun-tablep)
                         (vartab var-tablep)
                         (tagenv tag-envp))
  :returns (type type-resultp)
  :short "Check an expression that is a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the argument expressions,
     which must be pure (because we restrict them to be so).
     We retrieve the function type from the function table
     and we compare the input types with the argument types;
     this is more restrictive than allowed in [C],
     but it is adequate for now.
     Prior to comparing the types,
     we perform array-to-pointer conversions on
     all parameter types:
     this is consistent with the treatment of assignments
     (namely that the left-hand side of assignment
     is subjected to this conversion [C:6.3.2.1/3]),
     given that argument passing is treated like assignment [C:6.5.2.2/2].
     Note that @(tsee check-expr-pure-list)
     already applies that conversion to the argument types,
     so there is not need to do it here.
     We return the output type as the type of the call.
     A function call is never an lvalue;
     thus, we return a plain type, not an expression type."))
  (b* ((fun (ident-fix fun))
       (args (expr-list-fix args))
       ((okf arg-types) (check-expr-pure-list args vartab tagenv))
       (arg-types (apconvert-type-list arg-types))
       (info (fun-table-lookup fun funtab))
       ((unless info) (reserrf (list :fun-not-found fun)))
       (param-types (fun-sinfo->inputs info))
       (param-types (apconvert-type-list param-types))
       ((unless (equal param-types arg-types))
        (reserrf (list :call-args-mistype fun args
                       :required param-types
                       :supplied arg-types))))
    (fun-sinfo->output info))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-call-or-pure ((e exprp)
                                 (funtab fun-tablep)
                                 (vartab var-tablep)
                                 (tagenv tag-envp))
  :returns (type type-resultp)
  :short "Check an expression that must be
          a function call or a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the expression is a function call, we check it as such.")
   (xdoc::p
    "If the expression is not a function call,
     it must be a pure expression,
     which we resort to check it as such.")
   (xdoc::p
    "We return a plain type, not an expression type,
     because the caller of this function
     do not need to differentiate between lvalues and not lvalues."))
  (if (expr-case e :call)
      (check-expr-call (expr-call->fun e)
                       (expr-call->args e)
                       funtab
                       vartab
                       tagenv)
    (b* (((okf etype) (check-expr-pure e vartab tagenv)))
      (expr-type->type etype)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-asg ((e exprp)
                        (funtab fun-tablep)
                        (vartab var-tablep)
                        (tagenv tag-envp))
  :returns (wf? wellformed-resultp)
  :short "Check an expression that must be an assignment expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now, we only allow simple assignment expressions.
     The left-hand side expression must be a pure lvalue.
     Before checking that,
     we perform an array-to-pointer conversion [C:6.3.2.1/3]:
     in doing so, we also turn off the lvalue flag of the expression type,
     as specified in [C:6.3.2.1/3];
     this means that using something of an array type
     as the left-hand side of assignment fails.
     The right-hand side must be a function call or a pure expression;
     we implicitly apply lvalue conversion to it
     (because @(tsee check-expr-call-or-pure) returns a plain type;
     we apply array-to-pointer conversion to it as well.")
   (xdoc::p
    "The two sides must have the same type,
     which is more restrictive than [C:6.5.16.1].
     Since it is an invariant (currently not formally proved)
     that variables never have @('void') type,
     the equality of types implies that,
     if the right-hand side is a function call,
     the function must not return @('void').
     We require the left type (and thus the right type)
     to be arithmetic or structure or pointer [C:6.5.16.1].
     We do not return any type information from the assignment because
     an expression statement throws away the expression's value;
     indeed, we are only interested in the side effects of assignment here."))
  (b* (((unless (expr-case e :binary))
        (reserrf (list :expr-asg-not-binary (expr-fix e))))
       (op (expr-binary->op e))
       (left (expr-binary->arg1 e))
       (right (expr-binary->arg2 e))
       ((unless (binop-case op :asg))
        (reserrf (list :expr-asg-not-asg op)))
       ((okf left-etype) (check-expr-pure left vartab tagenv))
       (left-type (expr-type->type left-etype))
       (left-etype (if (type-case left-type :array)
                       (make-expr-type :type (apconvert-type left-type)
                                       :lvalue nil)
                     left-etype))
       ((unless (expr-type->lvalue left-etype))
        (reserrf (list :asg-left-not-lvalue (expr-fix e))))
       (left-type (expr-type->type left-etype))
       ((okf right-type) (check-expr-call-or-pure right funtab vartab tagenv))
       (right-type (apconvert-type right-type))
       ((unless (equal left-type right-type))
        (reserrf (list :asg-mistype left right
                       :required left-type
                       :supplied right-type)))
       ((unless (or (type-arithmeticp left-type)
                    (type-case left-type :struct)
                    (type-case left-type :pointer)))
        (reserrf (list :expr-asg-disallowed-type left-type))))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-call-or-asg ((e exprp)
                                (funtab fun-tablep)
                                (vartab var-tablep)
                                (tagenv tag-envp))
  :returns (wf? wellformed-resultp)
  :short "Check an expression that must be a function call or an assignment."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the expression is a function call, we check it as such.
     We also ensure that it returns @('void'),
     because we apply these checks to
     expressions that form expression statements:
     while [C] allows function calls that discard values,
     we are more restrictive here for now.")
   (xdoc::p
    "If the expression is not a function call,
     it must be an assignment expression,
     which we resort to check as such.")
   (xdoc::p
    "We retun no type here,
     because we apply these checks to
     expressions that form expression statements."))
  (if (expr-case e :call)
      (b* (((okf type) (check-expr-call (expr-call->fun e)
                                        (expr-call->args e)
                                        funtab
                                        vartab
                                        tagenv))
           ((unless (type-case type :void))
            (reserrf (list :nonvoid-function-result-discarded (expr-fix e)))))
        :wellformed)
    (check-expr-asg e funtab vartab tagenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-initer ((initer initerp)
                      (funtab fun-tablep)
                      (vartab var-tablep)
                      (tagenv tag-envp)
                      (constp booleanp))
  :returns (type init-type-resultp)
  :short "Check an initializer."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the initializer is a single expression,
     we ensure that it is a well-formed pure or call expression,
     and we return the type as a single initialization type.")
   (xdoc::p
    "If the initializer is a list of expressions,
     for now we require them to be pure expressions,
     and we return their types as a list initialization type.")
   (xdoc::p
    "The parameter @('constp') passed to this ACL2 function
     is a flag indicating whether the initializer must be constant or not."))
  (initer-case
   initer
   :single
   (b* (((okf type) (check-expr-call-or-pure initer.get funtab vartab tagenv))
        ((when (and constp
                    (not (expr-constp initer.get))))
         (reserrf (list :not-constant :single initer.get))))
     (init-type-single type))
   :list
   (b* (((okf types) (check-expr-pure-list initer.get vartab tagenv))
        ((when (and constp
                    (not (expr-list-constp initer.get))))
         (reserrf (list :not-constant :multi initer.get))))
     (init-type-list types)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-type-matchp ((itype init-typep) (type typep))
  :returns (wf? wellformed-resultp)
  :short "Check if an initializer type matches a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when comparing the type of an initializer
     with the declared type of the object.")
   (xdoc::p
    "If the initializer type is a single one,
     we require its type to match the declared type.
     We perform an array-to-pointer type conversion,
     consistently with assignments for scalars [C:6.7.9/11];
     for structure types initialized via single expressions [C:6.7.9/13].")
   (xdoc::p
    "If the initializer type is a list,
     we require the declared type to be an array type
     such that all the types in the initializer list
     match the array element type.
     If the array type has a size,
     the length of the initializer list must match the array size.")
   (xdoc::p
    "Here we are a bit more restrictive than in [C:6.7.9].
     In particular, [C:6.7.9/11] allows scalars to be initialized with
     singleton lists of expressions (i.e. single expressions between braces);
     but here we insist on scalars being initialized by single expressions."))
  (init-type-case
   itype
   :single (if (type-equiv type (apconvert-type itype.get))
               :wellformed
             (reserrf (list :init-type-mismatch
                            :required (type-fix type)
                            :supplied (init-type-fix itype))))
   :list (if (and (type-case type :array)
                  (equal itype.get
                         (repeat (len itype.get)
                                 (type-array->of type)))
                  (or (not (type-array->size type))
                      (equal (type-array->size type)
                             (len itype.get))))
             :wellformed
           (reserrf (list :init-type-mismatch
                          :required (type-fix type)
                          :supplied (init-type-fix itype)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-obj-declon ((declon obj-declonp)
                          (funtab fun-tablep)
                          (vartab var-tablep)
                          (tagenv tag-envp)
                          (constp booleanp)
                          (initp booleanp))
  :returns (new-vartab var-table-resultp)
  :short "Check an object declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the type is complete [C:6.7/7];
     this is not always necessary in full C,
     but our C subset requires that.
     We also ensure that the initializer type matches the declared type,
     if the initializer is present.")
   (xdoc::p
    "If the declaration is in a file scope,
     which is the case when there is just one scope in the variable table,
     we allow the @('extern') storage class specifier;
     otherwise, we disallow it.")
   (xdoc::p
    "The @('constp') flag controls whether
     we require the initializer, if present, to be constant or not.
     If the initializer is absent, the test passes.")
   (xdoc::p
    "The @('initp') flag controls whether
     we require the initializer to be present.")
   (xdoc::p
    "We return the updated variable table.
     If there is no initializer,
     in our C subset this must be in a file scope;
     since we require no @('extern') storage class specifier for now,
     in this case this must be a tentative definition [C:6.9.2/2].
     If instead there is an intializer,
     then it is a definition,
     regardless of whether it has file scope or block scope."))
  (b* (((mv var scspec tyname init?)
        (obj-declon-to-ident+scspec+tyname+init declon))
       ((when (and (consp (cdr vartab))
                   (scspecseq-case scspec :extern)))
        (reserrf (list :block-extern-disallowed (obj-declon-fix declon))))
       ((okf type) (check-tyname tyname tagenv))
       ((okf &) (check-ident var))
       ((unless (type-completep type))
        (reserrf (list :declon-error-type-incomplete (obj-declon-fix declon))))
       ((when (not init?))
        (if initp
            (reserrf (list :declon-initializer-required
                           (obj-declon-fix declon)))
          (var-table-add-var var type (var-defstatus-tentative) vartab)))
       (init init?)
       ((okf init-type) (check-initer init funtab vartab tagenv constp))
       ((okf &) (init-type-matchp init-type type)))
    (var-table-add-var var type (var-defstatus-defined) vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines check-stmt
  :short "Check a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow
     compound statements,
     expression statements,
     conditional statements,
     @('while') statements, and
     @('return') statements with expressions.")
   (xdoc::p
    "These ACL2 functions return
     either a pair consisting of
     a non-empty set of types and a variable table
     (see @(tsee types+vartab-p)),
     or an error.")
   (xdoc::p
    "For a compound statement,
     we add a block scope to the variable table
     and then we process the list of block items.
     There is no need to explicitly remove the scope when exiting the block,
     because we only use the extended variable table
     to check the items of the block.
     Anything that follows the block is checked
     with the variable table prior to the extension.
     In fact, a compound statement does not update the variable table:
     we return the original variable table.")
   (xdoc::p
    "As expression statements, we only allow
     function calls and simple assignments to variables,
     where the assigned expression must be a function call or pure.
     We only allow function calls with pure arguments
     (see @(tsee check-expr-call)).")
   (xdoc::p
    "For a conditional statement with both branches,
     after ensuring that the test expression has scalar type,
     we check the two branches, and take the union of their return types.
     We return the initial variable table, unchanged;
     any change in the branches is local to the branches.")
   (xdoc::p
    "We treat a conditional statement with just one branch
     as one whose @('else') branch returns nothing.")
   (xdoc::p
    "For a @('while') statement,
     we ensure that the test has a scalar type,
     and we check the body.
     We put together @('void') and the return types from the body:
     the @('void') accounts for the case in which
     the body is never executed (i.e. the test is initially false).
     We return the initial variable table, unchanged;
     any change in the body is local to the body.")
   (xdoc::p
    "For a @('return') statement,
     we require an expression,
     and we return the singleton set with the type of the expression.
     The type must not be @('void') [C:6.3.2.2].")
   (xdoc::p
    "For a block item that is a declaration,
     we check the (object) declaration,
     requiring the initializer
     but without requiring it to be constant.
     We return the singleton set with @('void'),
     because a declaration never returns a value
     and proceeds with the next block item.")
   (xdoc::p
    "For a block item that is a statement, we check the statement.")
   (xdoc::p
    "If a list of block items is empty, we return
     the singleton set with @('void')
     (because execution then continues after the block)
     and the variable table unchanged.
     If the list of block items is a singleton,
     we check the first and only item,
     and return the result as the result of checking the singleton list;
     we need to treat the singleton case differently from the next,
     otherwise we would be always returning @('void') as one of the types,
     because this is what the empty list of block items returns.
     If the list of block items has two or more items,
     we check the first item and the (non-empty) rest of the block.
     We return the union of
     (i) the return types from the first block item,
     minus @('void') if present, and
     (ii) the return types from the rest of the block.
     The reason for removing @('void') from the first set
     is that @('void') just indicates that execution
     may go from the first block item to the rest of the block:
     it does not represent a possible return type of the whole block.
     Note that if @('void') is not among the first item's return types,
     it means that the rest of the block is acually dead code:
     execution never proceeds past the first block item.
     Nonetheless, as explained above,
     we also checking the rest of the block,
     and we consider its possible return types.
     This is consistent with the fact that [C]
     does not say anything any special treatment of this kind of dead code;
     it is also consistent with simple experiments with @('gcc') on Mac,
     which show that code after a @('return') is checked, not ignored."))

  (define check-stmt ((s stmtp)
                      (funtab fun-tablep)
                      (vartab var-tablep)
                      (tagenv tag-envp))
    :returns (stype types+vartab-resultp)
    (stmt-case
     s
     :labeled (reserrf (list :unsupported-labeled s.label s.body))
     :compound (b* ((ext-vartab (var-table-add-block vartab))
                    ((okf stype) (check-block-item-list s.items
                                                        funtab
                                                        ext-vartab
                                                        tagenv)))
                 (change-types+vartab stype :variables vartab))
     :expr (b* (((okf &) (check-expr-call-or-asg s.get funtab vartab tagenv)))
             (make-types+vartab :return-types (set::insert (type-void) nil)
                                :variables (var-table-fix vartab)))
     :null (reserrf :unsupported-null-stmt)
     :if (b* (((okf etype) (check-expr-pure s.test vartab tagenv))
              (type (expr-type->type etype))
              (type (apconvert-type type))
              ((unless (type-scalarp type))
               (reserrf (list :if-test-mistype s.test s.then :noelse
                              :required :scalar
                              :supplied type)))
              ((okf stype-then) (check-stmt s.then funtab vartab tagenv)))
           (make-types+vartab
            :return-types (set::union (types+vartab->return-types stype-then)
                                      (set::insert (type-void) nil))
            :variables vartab))
     :ifelse (b* (((okf etype) (check-expr-pure s.test vartab tagenv))
                  (type (expr-type->type etype))
                  (type (apconvert-type type))
                  ((unless (type-scalarp type))
                   (reserrf (list :if-test-mistype s.test s.then s.else
                                  :required :scalar
                                  :supplied type)))
                  ((okf stype-then) (check-stmt s.then funtab vartab tagenv))
                  ((okf stype-else) (check-stmt s.else funtab vartab tagenv)))
               (make-types+vartab
                :return-types (set::union (types+vartab->return-types stype-then)
                                          (types+vartab->return-types stype-else))
                :variables vartab))
     :switch (reserrf (list :unsupported-switch s.ctrl s.body))
     :while (b* (((okf etype) (check-expr-pure s.test vartab tagenv))
                 (type (expr-type->type etype))
                 (type (apconvert-type type))
                 ((unless (type-scalarp type))
                  (reserrf (list :while-test-mistype s.test s.body
                                 :required :scalar
                                 :supplied type)))
                 ((okf stype-body) (check-stmt s.body funtab vartab tagenv)))
              (make-types+vartab
               :return-types (set::insert (type-void)
                                          (types+vartab->return-types stype-body))
               :variables vartab))
     :dowhile (reserrf (list :unsupported-dowhile s.body s.test))
     :for (reserrf (list :unsupported-for s.init s.test s.next s.body))
     :goto (reserrf (list :unsupported-goto s.target))
     :continue (reserrf :unsupported-continue)
     :break (reserrf :unsupported-break)
     :return (b* (((unless s.value) (reserrf (list :unsupported-return-void)))
                  ((okf type)
                   (check-expr-call-or-pure s.value funtab vartab tagenv))
                  (type (apconvert-type type))
                  ((when (type-case type :void))
                   (reserrf (list :return-void-expression s.value))))
               (make-types+vartab :return-types (set::insert type nil)
                                  :variables vartab)))
    :measure (stmt-count s))

  (define check-block-item ((item block-itemp)
                            (funtab fun-tablep)
                            (vartab var-tablep)
                            (tagenv tag-envp))
    :returns (stype types+vartab-resultp)
    (block-item-case
     item
     :declon
     (b* (((okf vartab) (check-obj-declon item.get funtab vartab tagenv nil t)))
       (make-types+vartab :return-types (set::insert (type-void) nil)
                          :variables vartab))
     :stmt (check-stmt item.get funtab vartab tagenv))
    :measure (block-item-count item))

  (define check-block-item-list ((items block-item-listp)
                                 (funtab fun-tablep)
                                 (vartab var-tablep)
                                 (tagenv tag-envp))
    :returns (stype types+vartab-resultp)
    (b* (((when (endp items))
          (make-types+vartab :return-types (set::insert (type-void) nil)
                             :variables vartab))
         ((okf stype) (check-block-item (car items) funtab vartab tagenv))
         ((when (endp (cdr items))) stype)
         (rtypes1 (set::delete (type-void) (types+vartab->return-types stype)))
         (vartab (types+vartab->variables stype))
         ((okf stype) (check-block-item-list (cdr items) funtab vartab tagenv))
         (rtypes2 (types+vartab->return-types stype))
         (vartab (types+vartab->variables stype)))
      (make-types+vartab :return-types (set::union rtypes1 rtypes2)
                         :variables vartab))
    :measure (block-item-list-count items))

  :prepwork ((local (in-theory (enable not-reserrp-when-types+vartab-p))))

  :hints (("Goal" :in-theory (enable o< o-p o-finp)))

  :verify-guards nil ; done below
  ///
  (verify-guards check-stmt)

  (fty::deffixequiv-mutual check-stmt)

  (local
   (defthm-check-stmt-flag
     (defthm check-stmt-var-table
       (b* ((result (check-stmt s funtab vartab tagenv)))
         (implies (types+vartab-p result)
                  (equal (types+vartab->variables result)
                         (var-table-fix vartab))))
       :flag check-stmt)
     (defthm check-block-item-var-table
       t
       :rule-classes nil
       :flag check-block-item)
     (defthm check-block-item-list-var-table
       t
       :rule-classes nil
       :flag check-block-item-list)
     :hints (("Goal" :expand ((check-stmt s funtab vartab tagenv))))))

  (defrule check-stmt-var-table-no-change
    (b* ((result (check-stmt s funtab vartab tagenv)))
      (implies (types+vartab-p result)
               (equal (types+vartab->variables result)
                      (var-table-fix vartab))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-param-declon ((param param-declonp)
                            (vartab var-tablep)
                            (tagenv tag-envp))
  :returns (new-vartab var-table-resultp)
  :short "Check a parameter declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable table passed as input is the one
     engendered by the parameter declarations that precede this one.
     We check the components of the parameter declaration
     and we check that the parameter can be added to the variable table;
     the latter check fails if there is a duplicate parameter.
     Each parameter is considered defined in the variable table.
     Note that we regard each declaration as defining the variable,
     because no multiple declarations of the same parameter are allowed.
     We adjust the type [C:6.7.6.3/7].
     We also ensure that the (adjusted) type is complete [C:6.7.6.3/4].
     If all checks succeed, we return the variable table
     updated with the parameter, with the adjusted type."))
  (b* (((mv var tyname) (param-declon-to-ident+tyname param))
       ((okf type) (check-tyname tyname tagenv))
       ((okf &) (check-ident var))
       (type (adjust-type type))
       ((unless (type-completep type))
        (reserrf (list :param-type-incomplete (param-declon-fix param)))))
    (var-table-add-var var type (var-defstatus-defined) vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-param-declon-list ((params param-declon-listp)
                                 (vartab var-tablep)
                                 (tagenv tag-envp))
  :returns (new-vartab var-table-resultp)
  :short "Check a list of parameter declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each element of the list,
     calling @(tsee check-param-declon)
     and threading the variable table through."))
  (b* (((when (endp params)) (var-table-fix vartab))
       ((okf vartab) (check-param-declon (car params) vartab tagenv)))
    (check-param-declon-list (cdr params) vartab tagenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fun-declor ((declor fun-declorp)
                          (vartab var-tablep)
                          (tagenv tag-envp))
  :returns (vartab var-table-resultp)
  :short "Check a function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the pointers, if any.
     We check the identifier and the list of parameter declarations.
     We add a new block scope to the variable table,
     for the block associated to the function definition
     of which this declarator is part;
     in fact, this is also adequate for checking a function declarator
     that is part of a function declaration that is not a function definition,
     as in that case we just need to ensure that the parameters are distinct.
     We check the parameters starting with this variable table,
     which (if successful) produces a variable table
     that includes the parameters;
     this table is used when checking the function definition."))
  (fun-declor-case
   declor
   :base (b* (((okf &) (check-ident declor.name))
              (vartab (var-table-add-block vartab)))
           (check-param-declon-list declor.params vartab tagenv))
   :pointer (check-fun-declor declor.decl vartab tagenv))
  :measure (fun-declor-count declor)
  :hints (("Goal" :in-theory (enable o< o-p o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fun-declon ((declon fun-declonp)
                          (funtab fun-tablep)
                          (vartab var-tablep)
                          (tagenv tag-envp))
  :returns (new-funtab fun-table-resultp)
  :short "Check a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the type specifier sequence and the declarator.
     We extend the function table with information about the new function.")
   (xdoc::p
    "We adjust the parameter types [C:6.7.6.3/7]."))
  (b* (((fun-declon declon) declon)
       ((mv name params out-tyname)
        (tyspec+declor-to-ident+params+tyname declon.tyspec declon.declor))
       ((okf out-type) (check-tyname out-tyname tagenv))
       ((okf &) (check-fun-declor declon.declor vartab tagenv))
       ((mv & in-tynames) (param-declon-list-to-ident+tyname-lists params))
       (in-types (type-name-list-to-type-list in-tynames))
       (in-types (adjust-type-list in-types)))
    (fun-table-add-fun name in-types out-type nil funtab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fundef ((fundef fundefp)
                      (funtab fun-tablep)
                      (vartab var-tablep)
                      (tagenv tag-envp))
  :returns (new-funtab fun-table-resultp)
  :short "Check a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check type specifier sequence and declarator,
     obtaining the variable table that includes the parameters.
     Importantly, the block items are checked in this variable table,
     which has the types for the function parameters,
     without creating a new scope for the block (i.e. the compound statement):
     the reason is that the scope of function parameters
     terminates at the end of the associated block [C:6.2.1/4].")
   (xdoc::p
    "The variable table passed as parameter to this ACL2 function
     always consists of just the current file scope,
     i.e. the file-scope variables that precede the function definition
     in the translation unit.")
   (xdoc::p
    "We ensure that the return types of the body
     match the return types of the function.
     Currently, this means that the set of return types
     must be a singleton with the function's return type;
     this may be relaxed in the future.")
   (xdoc::p
    "We also extend the function table with the new function.
     It is an error if a function with the same name is already in the table.
     In general, this must be done before checking the body:
     the function is in scope, in its own body.")
   (xdoc::p
    "The scope of a function identifier goes from its declaration
     to the end of the translation unit [C:6.2.1/4].
     Thus, as we go through
     the function definitions in the translation unit in order,
     we extend the function table."))
  (b* (((fundef fundef) fundef)
       ((mv name params out-tyname)
        (tyspec+declor-to-ident+params+tyname fundef.tyspec fundef.declor))
       ((okf out-type) (check-tyname out-tyname tagenv))
       ((okf vartab) (check-fun-declor fundef.declor vartab tagenv))
       ((mv & in-tynames) (param-declon-list-to-ident+tyname-lists params))
       (in-types (type-name-list-to-type-list in-tynames))
       (in-types (adjust-type-list in-types))
       ((okf funtab) (fun-table-add-fun name in-types out-type t funtab))
       ((okf stype) (check-block-item-list fundef.body funtab vartab tagenv))
       ((unless (equal (types+vartab->return-types stype)
                       (set::insert out-type nil)))
        (reserrf (list :fundef-return-mistype name
                       :required out-type
                       :inferred (types+vartab->return-types stype)))))
    funtab)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-struct-declon-list ((declons struct-declon-listp)
                                  (tagenv tag-envp))
  :returns (members member-type-list-resultp)
  :short "Check a list of structure declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These specify the members of a structure or union type
     (see @(tsee struct-declon));
     for now we only use this for the members of a structure type,
     since we do not model union types.")
   (xdoc::p
    "We go through the declarations
     and turn each of them into member types (see @(tsee member-type)).
     We ensure that each member name is well-formed.
     We check that each type is well-formed.
     We also check that each type either is complete [C:6.7.2.1/9],
     or is an array type of unspecified size in the last member;
     the latter is a flexible array member [C:6.7.2.1/18].
     By using @(tsee member-type-add-first),
     we ensure that there are no duplicate member names."))
  (b* (((when (endp declons)) nil)
       (lastp (endp (cdr declons)))
       ((okf members) (check-struct-declon-list (cdr declons) tagenv))
       ((mv name tyname) (struct-declon-to-ident+tyname (car declons)))
       ((okf type) (check-tyname tyname tagenv))
       (completep (type-completep type))
       (flexiblep (and lastp
                       (type-case type :array)
                       (not (type-array->size type))))
       ((unless (or completep flexiblep))
        (reserrf (list :incomplete-member-type type)))
       ((okf &) (check-ident name))
       (members-opt (member-type-add-first name type members)))
    (member-type-list-option-case
     members-opt
     :some members-opt.val
     :none (reserrf (list :duplicate-member name))))
  ///

  (fty::deffixequiv check-struct-declon-list
    :args ((declons struct-declon-listp)
           (tagenv tag-envp))
    ;; for speed:
    :hints (("Goal" :in-theory (disable equal-of-error))))

  (defret consp-of-check-struct-declon-list
    (equal (consp (check-struct-declon-list declons tagenv))
           (consp declons))
    :fn check-struct-declon-list
    :hints (("Goal" :in-theory (enable member-type-list-option-some->val
                                       member-type-add-first
                                       member-type-list-option-some)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tag-declon ((declon tag-declonp) (tagenv tag-envp))
  :returns (new-tagenv tag-env-resultp)
  :short "Check a tag declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support structure type declarations,
     not union or enumeration type declarations.
     For a structure type declaration, we first check the members,
     obtaining a list of member types if successful.
     We ensure that there is at least one member [C:6.2.5/20],
     or at least two members if the last member is a flexible array member
     [C:6.2.5/18].
     We use @(tsee tag-env-add) to ensure that there is not already
     another structure or union or enumeration type with the same tag,
     since these share one name space [C:6.2.3].")
   (xdoc::p
    "C allows a form of recursion in structure type declarations,
     namely that a member can be a pointer to the structure:
     [C:6.2.1/7] says that the scope of the tag starts where it appears,
     so it includes the members;
     and [C:6.7.2.1/9] says that a member type must be complete,
     which pointer types are [C:6:2.5/20].
     However, we implicitly disallow even this form of recursion for now,
     because we check the member types against the current tag environment,
     which does not include the structure type yet."))
  (tag-declon-case
   declon
   :struct
   (b* (((okf members) (check-struct-declon-list declon.members tagenv))
        ((unless (consp members))
         (reserrf (list :empty-struct (tag-declon-fix declon))))
        ((when (b* ((member (car (last members)))
                    (type (member-type->type member)))
                 (and (type-case type :array)
                      (not (type-array->size type))
                      (endp (cdr members)))))
         (reserrf (list :struct-with-just-flexible-array-member members)))
        (info (tag-info-struct members))
        (tagenv-opt (tag-env-add declon.tag info tagenv)))
     (tag-env-option-case tagenv-opt
                          :some tagenv-opt.val
                          :none (reserrf (list :duplicate-tag declon.tag))))
   :union (reserrf (list :union-not-supported (tag-declon-fix declon)))
   :enum (reserrf (list :enum-not-supported (tag-declon-fix declon))))
  :guard-hints
  (("Goal"
    :in-theory
    (enable member-type-listp-when-member-type-list-resultp-and-not-reserrp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon ((ext ext-declonp)
                          (funtab fun-tablep)
                          (vartab var-tablep)
                          (tagenv tag-envp))
  :returns (new-funtab+vartab+tagenv funtab+vartab+tagenv-resultp)
  :short "Check an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For object declarations,
     we require the initializer to be constant if present [C:6.7.9/4],
     without requiring it to be present.")
   (xdoc::p
    "If successful, we return updated
     function table, variable table, and tag environment.")
   (xdoc::p
    "For now we reject function declarations.
     We plan to add support soon."))
  (ext-declon-case
   ext
   :fundef (b* (((okf funtab)
                 (check-fundef ext.get funtab vartab tagenv)))
             (make-funtab+vartab+tagenv :funs funtab
                                        :vars (var-table-fix vartab)
                                        :tags (tag-env-fix tagenv)))
   :fun-declon (b* (((okf funtab)
                     (check-fun-declon ext.get funtab vartab tagenv)))
                 (make-funtab+vartab+tagenv :funs funtab
                                            :vars (var-table-fix vartab)
                                            :tags (tag-env-fix tagenv)))
   :obj-declon (b* (((okf vartab)
                     (check-obj-declon ext.get funtab vartab tagenv t nil)))
                 (make-funtab+vartab+tagenv :funs (fun-table-fix funtab)
                                            :vars vartab
                                            :tags (tag-env-fix tagenv)))
   :tag-declon (b* (((okf tagenv) (check-tag-declon ext.get tagenv)))
                 (make-funtab+vartab+tagenv :funs (fun-table-fix funtab)
                                            :vars (var-table-fix vartab)
                                            :tags tagenv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon-list ((exts ext-declon-listp)
                               (funtab fun-tablep)
                               (vartab var-tablep)
                               (tagenv tag-envp))
  :returns (new-funtab+vartab+tagenv funtab+vartab+tagenv-resultp)
  :short "Check a list of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We thread through
     the function table, variable table, and tag environment."))
  (b* (((when (endp exts))
        (make-funtab+vartab+tagenv :funs (fun-table-fix funtab)
                                   :vars (var-table-fix vartab)
                                   :tags (tag-env-fix tagenv)))
       ((okf funtab+vartab+tagenv)
        (check-ext-declon (car exts) funtab vartab tagenv)))
    (check-ext-declon-list (cdr exts)
                           (funtab+vartab+tagenv->funs funtab+vartab+tagenv)
                           (funtab+vartab+tagenv->vars funtab+vartab+tagenv)
                           (funtab+vartab+tagenv->tags funtab+vartab+tagenv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-transunit ((tunit transunitp))
  :returns (wf wellformed-resultp)
  :short "Check a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the initial (empty) function table,
     we check all the external declarations,
     threading the function table through,
     and discarding the final one (it served its pupose).")
   (xdoc::p
    "We also ensure that there is at leaast one external declaration,
     according to the grammatical requirement in [C:6.9/1].")
   (xdoc::p
    "We also check that the external objects and the functions
     have no overlap in their names (identifiers).
     These are all ordinary identifiers [C:6.2.3/1],
     and therefore must be distinct in the same (file) scope.")
   (xdoc::p
    "We also check that all the functions are defined;
     we perform this check on the function table
     that results from checking the external declarations.
     This is a little stricter than [C:6.9/5],
     which allows a function to remain undefined
     if it is not called in the rest of the program.
     However, as we look at a translation unit in isolation here,
     we do not have the rest of the program,
     and thus we make the stricter check for now."))
  (b* (((transunit tunit) tunit)
       ((unless (consp tunit.declons))
        (reserrf (list :transunit-empty)))
       (funtab (fun-table-init))
       (vartab (var-table-init))
       (tagenv (tag-env-init))
       ((okf funtab+vartab+tagenv)
        (check-ext-declon-list tunit.declons funtab vartab tagenv))
       (funtab (funtab+vartab+tagenv->funs funtab+vartab+tagenv))
       (vartab (funtab+vartab+tagenv->vars funtab+vartab+tagenv))
       (overlap (set::intersect (omap::keys funtab)
                                (omap::keys (car vartab))))
       ((unless (set::emptyp overlap))
        (reserrf (list :transunit-fun-obj-overlap overlap)))
       ((unless (var-table-add-block vartab))
        (reserrf (list :transunit-has-undef-var vartab)))
       ((unless (fun-table-all-definedp funtab))
        (reserrf (list :transunit-has-undef-fun funtab))))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define preprocess ((fileset filesetp))
  :returns (tunit transunit-resultp)
  :short "Preprocess a file set [C:5.1.1.2/4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a very simplified model of C preprocessing [C:6.10].
     If there is no header, this is essentially a no-op:
     the external declarations are unwrapped from the source file
     and re-wrapped into a translation unit.
     If there is a header, as explained in @(tsee fileset),
     it is implicitly included in the source file
     (without an explicit representation of the @('#include') directive):
     we concatenate the external declarations from the header
     and the external declarations from the source file,
     and wrap the concatenation into a translation unit.
     This amounts to replacing the (implicit) @('#include')
     with the included header,
     which is assumed to be at the beginning of the source file.
     The path without extension component of the file set
     is currently ignored, because the @('#include') is implicit."))
  (b* ((h-extdecls (and (fileset->dot-h fileset)
                        (file->declons (fileset->dot-h fileset))))
       (c-extdecls (file->declons (fileset->dot-c fileset))))
    (make-transunit :declons (append h-extdecls c-extdecls)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fileset ((fileset filesetp))
  :returns (wf wellformed-resultp)
  :short "Check a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we preprocess the file set.
     If preprocessing is successful,
     we check the translation unit."))
  (b* (((okf tunit) (preprocess fileset)))
    (check-transunit tunit))
  :hooks (:fix))

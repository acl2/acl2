; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax-operations")
(include-book "portable-ascii-identifiers")
(include-book "integer-ranges")
(include-book "tag-environments")
(include-book "errors")

(include-book "kestrel/fty/defomap" :dir :system)
(include-book "kestrel/fty/defunit" :dir :system)

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

(fty::defomap var-table-scope
  :short "Fixtype of scopes of variable tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable table is a symbol table for variables.
     The table (see @(tsee var-table)) is organized as
     a sequence with one element for each nested block scope [C:6.2.1].
     This @('var-table-scope') fixtype
     contains information about such a block scope.
     The information is organized as a finite map
     from identifiers (variable names) to types.
     Using a map is adequate because
     all the variables declared in a block must have different names
     [C:6.2.1/2]."))
  :key-type ident
  :val-type type
  :pred var-table-scopep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var-table
  :short "Fixtype of variable tables, i.e. symbol tables for variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This keeps track of all the variables in scope [C:6.2.1],
     organized according to block scopes.
     The list has one element for each nested block,
     where the first element (the @(tsee car))
     corresponds to the innermost block:
     this order is natural, as blocks are added via @(tsee cons).
     The list is never empty:
     we always initialize the variable table one (empty) block.")
   (xdoc::p
    "Currently we do not support variables with file scope.
     Thus, all the scopes here are block scopes.")
   (xdoc::p
    "It is possible for two scopes in the list to have overlapping keys,
     when a variable in an inner block hides one in an outer block
     [C:6.2.1/4]."))
  :elt-type var-table-scope
  :true-listp t
  :non-emptyp t
  :elementp-of-nil t
  :pred var-tablep
  ///

  (defrule var-tablep-of-cons-alt
    (iff (var-tablep (cons a x))
         (and (var-table-scopep a)
              (or (var-tablep x)
                  (eq x nil))))
    :enable var-tablep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult var-table "variable tables")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-lookup ((var identp) (vartab var-tablep))
  :returns (type type-optionp)
  :short "Look up a variable in a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is found, we return its type;
     otherwise, we return @('nil').
     We search for the variable in the sequence of scopes in order,
     i.e. from innermost to outermost block."))
  (b* (((unless (mbt (not (endp vartab)))) nil)
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
    "This contains a single block with no variables."))
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
     This is used when a block is entered."))
  (cons nil (var-table-fix vartab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-table-add-var ((var identp) (type typep) (vartab var-tablep))
  :returns (new-vartab var-table-resultp
                       :hints (("Goal" :in-theory (enable var-table-resultp))))
  :short "Add a variable to (the innermost block of) a variable table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block already has a variable with that name, it is an error.
     Otherwise, we add the variable and return the variable table."))
  (b* ((var (ident-fix var))
       (type (type-fix type))
       (vartab (var-table-fix vartab))
       (varscope (car vartab))
       ((when (omap::in var varscope)) (error (list :duplicate-var var)))
       (new-varscope (omap::update var type varscope)))
    (cons new-varscope (cdr vartab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-type
  :short "Fixtype of function types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Function types are described in [C:6.2.5/20].
     Eventually these may be integrated into
     a broader formalized notion of C types,
     but for now we introduce this fixtype here,
     in order to use it in function tables.
     A function type consists of zero or more input types and an output type."))
  ((inputs type-list)
   (output type))
  :pred fun-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fun-type-option
  fun-type
  :short "Fixtype of optional function types."
  :pred fun-type-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap fun-table
  :short "Fixtype of function tables, i.e. symbol tables for functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We associate a function type to the function name, in a finite map."))
  :key-type ident
  :val-type fun-type
  :pred fun-tablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult fun-table "function tables")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-table-lookup ((fun identp) (funtab fun-tablep))
  :returns (fun-type fun-type-optionp
                     :hints (("Goal" :in-theory (enable fun-type-optionp))))
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

(define fun-table-add-fun ((fun identp) (type fun-typep) (funtab fun-tablep))
  :returns (new-funtab fun-table-resultp)
  :short "Add a function with a function type to a function table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the table already has a function with that name, it is an error.
     Otherwise, we add the function and return the function table."))
  (b* ((fun (ident-fix fun))
       (type (fun-type-fix type))
       (funtab (fun-table-fix funtab))
       ((when (set::in fun funtab)) (error (list :duplicate-fun fun))))
    (omap::update fun type funtab))
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
     both the @('.') and the @('->') kind."))
  (b* ((info (tag-env-lookup tag tagenv))
       ((when (tag-info-option-case info :none))
        (error (list :struct-not-found
                     (ident-fix tag)
                     (tag-env-fix tagenv))))
       (info (tag-info-option-some->val info))
       ((unless (tag-info-case info :struct))
        (error (list :tag-not-struct
                     (ident-fix tag)
                     info)))
       (members (tag-info-struct->members info))
       (type (member-type-lookup mem members))
       ((when (type-option-case type :none))
        (error (list :member-not-found
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

(defresult wellformed "the @(tsee wellformed) indicator")

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

(defresult expr-type "expression types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stmt-type
  :short "Fixtype of statement types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we use the word ``type'' in a broad sense,
     namely to describe the information inferred by the static semantics
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
      could just return a set of optional types (see above).
      However, for uniformity we have all three functions
      return also a possibly updated variable table.")))
  ((return-types type-set :reqfix (if (set::empty return-types)
                                      (set::insert (type-void) nil)
                                    return-types))
   (variables var-table))
  :require (not (set::empty return-types))
  :pred stmt-typep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult stmt-type "statement types")

;;;;;;;;;;;;;;;;;;;;

(defrule not-stmt-typep-of-error
  (not (stmt-typep (error x)))
  :enable (error stmt-typep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funtab+tagenv
  :short "Fixtype of pairs consisting of
          a function table and a tag environment."
  ((funs fun-tablep)
   (tags tag-envp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult funtab+tagenv
  "pairs consisting of a function table and a tag environment")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define promote-type ((type typep))
  :returns (promoted-type typep)
  :short "Apply the integer promotions to a type [C:6.3.1.1/2]."
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

  (defrule type-integerp-of-promote-type
    (equal (type-integerp (promote-type type))
           (type-integerp type))
    :enable (type-integerp type-unsigned-integerp type-signed-integerp)))

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

  (defruled uaconvert-types-when-same
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2)
                  (type-equiv type1 type2))
             (equal (uaconvert-types type1 type2)
                    (promote-type type1)))
    :enable (type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp
             promote-type))

  (defruled uaconvert-types-symmetry
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2))
             (equal (uaconvert-types type1 type2)
                    (uaconvert-types type2 type1)))
    :enable (type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp
             promote-type))

  (defrule type-integerp-of-uaconvert-types
    (implies (and (type-arithmeticp type1)
                  (type-arithmeticp type2))
             (equal (type-integerp (uaconvert-types type1 type2))
                    (and (type-integerp type1)
                         (type-integerp type2))))
    :enable (type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp
             promote-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apconvert-type ((type typep))
  :returns (type1 typep)
  :short "Convert array type to pointer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Under certain circumstances,
     an array is converted to a pointer to the first element of the array
     [C:6.3.2.1/3].
     Indeed, arrays are used like pointers most of the time.
     This conversion is captured, at the level of types, here.
     Non-array types are left unchanged."))
  (if (type-case type :array)
      (type-pointer (type-array->of type))
    (type-fix type))
  :hooks (:fix))

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

(define check-ident ((id identp))
  :returns (wf? wellformed-resultp)
  :short "Check an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether the underlying ACL2 string forms a "
    (xdoc::seetopic "portable-ascii-identifiers" "portable ASCII identifier")
    "."))
  (if (ident-stringp (ident->name id))
      :wellformed
    (error (list :illegal/unsupported-ident (ident-fix id))))
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
    "This is the static counterpart of @(tsee exec-iconst)."))
  (b* ((ic (iconst-fix ic))
       ((iconst ic) ic))
    (if ic.unsignedp
        (iconst-length-case
         ic.length
         :none (cond ((uint-integerp ic.value) (type-uint))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (error (list :iconst-out-of-range ic))))
         :long (cond ((ulong-integerp ic.value) (type-ulong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (error (list :iconst-out-of-range ic))))
         :llong (cond ((ullong-integerp ic.value) (type-ullong))
                      (t (error (list :iconst-out-of-range ic)))))
      (iconst-length-case
       ic.length
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (type-sint))
                       ((slong-integerp ic.value) (type-slong))
                       ((sllong-integerp ic.value) (type-sllong))
                       (t (error (list :iconst-out-of-range ic))))
               (cond ((sint-integerp ic.value) (type-sint))
                     ((uint-integerp ic.value) (type-uint))
                     ((slong-integerp ic.value) (type-slong))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((sllong-integerp ic.value) (type-sllong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (error (list :iconst-out-of-range ic)))))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (type-slong))
                       ((sllong-integerp ic.value) (type-sllong))
                       (t (error (list :iconst-out-of-range ic))))
               (cond ((slong-integerp ic.value) (type-slong))
                     ((ulong-integerp ic.value) (type-ulong))
                     ((sllong-integerp ic.value) (type-sllong))
                     ((ullong-integerp ic.value) (type-ullong))
                     (t (error (list :iconst-out-of-range ic)))))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (type-sllong))
                        (t (error (list :iconst-out-of-range ic))))
                (cond ((sllong-integerp ic.value) (type-sllong))
                      ((ullong-integerp ic.value) (type-ullong))
                      (t (error (list :iconst-out-of-range ic))))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-const ((c constp))
  :returns (type type-resultp)
  :short "Check a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only accept integer constants."))
  (const-case c
              :int (check-iconst c.get)
              :float (error (list :unsupported-float-const (const-fix c)))
              :enum (error (list :unsupported-enum-const (const-fix c)))
              :char (error (list :unsupported-char-const (const-fix c))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tyspecseq ((tyspec tyspecseqp) (tagenv tag-envp))
  :returns (wf? wellformed-resultp)
  :short "Check a type specifier sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only accept certain type specifier sequences for now,
     namely the ones that have corresponding types (see @(tsee type)).
     The tag of a structure type specifier sequence
     must be in the tag environment.
     All the other (supported) type specifier sequences
     are always well-formed."))
  (tyspecseq-case
   tyspec
   :void :wellformed
   :char :wellformed
   :schar :wellformed
   :uchar :wellformed
   :sshort :wellformed
   :ushort :wellformed
   :sint :wellformed
   :uint :wellformed
   :slong :wellformed
   :ulong :wellformed
   :sllong :wellformed
   :ullong :wellformed
   :bool :wellformed
   :float :wellformed
   :double :wellformed
   :ldouble :wellformed
   :struct (b* ((info (tag-env-lookup tyspec.tag tagenv)))
             (tag-info-option-case
              info
              :some (if (tag-info-case info.val :struct)
                        :wellformed
                      (error (list :struct-tag-mismatch tyspec.tag info.val)))
              :none (error (list :no-tag-found tyspec.tag))))
   :union (error (list :not-supported-union tyspec.tag))
   :enum (error (list :not-supported-enum tyspec.tag))
   :typedef (error (list :not-supported-typedef tyspec.name)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-obj-adeclor ((declor obj-adeclorp))
  :returns (wf? wellformed-resultp)
  :short "Check an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This boils down to checking array sizes, if present."))
  (obj-adeclor-case
   declor
   :none :wellformed
   :pointer (check-obj-adeclor declor.decl)
   :array (b* ((wf? (check-obj-adeclor declor.decl))
               ((when (errorp wf?)) wf?)
               ((unless declor.size) :wellformed)
               (type? (check-iconst declor.size))
               ((when (errorp type?)) type?))
            :wellformed))
  :measure (obj-adeclor-count declor)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-tyname ((tyname tynamep) (tagenv tag-envp))
  :returns (wf? wellformed-resultp)
  :short "Check a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The underlying type specifier sequence and declarator
     must be well-formed."))
  (b* ((wf? (check-tyspecseq (tyname->tyspec tyname) tagenv))
       ((when (errorp wf?)) wf?)
       (wf? (check-obj-adeclor (tyname->declor tyname)))
       ((when (errorp wf?)) wf?))
    :wellformed)
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
                (error (list :unary-mistype
                             (unop-fix op) (expr-fix arg-expr)
                             :required :lvalue
                             :supplied (expr-type-fix arg-etype)))))
    (:indir (b* ((arg-type (expr-type->type arg-etype))
                 (arg-type (apconvert-type arg-type)))
              (if (type-case arg-type :pointer)
                  (make-expr-type :type (type-pointer->to arg-type)
                                  :lvalue nil)
                (error (list :unary-mistype
                             (unop-fix op) (expr-fix arg-expr)
                             :required :pointer
                             :supplied arg-type)))))
    ((:plus :minus) (b* ((arg-type (expr-type->type arg-etype))
                         (arg-type (apconvert-type arg-type)))
                      (if (type-arithmeticp arg-type)
                          (make-expr-type :type (promote-type arg-type)
                                          :lvalue nil)
                        (error (list :unary-mistype
                                     (unop-fix op) (expr-fix arg-expr)
                                     :required :arithmetic
                                     :supplied (type-fix arg-type))))))
    (:bitnot (b* ((arg-type (expr-type->type arg-etype))
                  (arg-type (apconvert-type arg-type)))
               (if (type-integerp arg-type)
                   (make-expr-type :type (promote-type arg-type) :lvalue nil)
                 (error (list :unary-mistype
                              (unop-fix op) (expr-fix arg-expr)
                              :required :integer
                              :supplied (type-fix arg-type))))))
    (:lognot (b* ((arg-type (expr-type->type arg-etype))
                  (arg-type (apconvert-type arg-type)))
               (if (type-scalarp arg-type)
                   (make-expr-type :type (type-sint) :lvalue nil)
                 (error (list :unary-mistype
                              (unop-fix op) (expr-fix arg-expr)
                              :required :scalar
                              :supplied (type-fix arg-type))))))
    (t (error (impossible))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-binary-pure ((op binopp)
                           (arg1-expr exprp) (arg1-type typep)
                           (arg2-expr exprp) (arg2-type typep))
  :guard (binop-purep op)
  :returns (type type-resultp)
  :short "Check the application of a pure binary operator to two expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check @('arg1-type') and @('arg2-type') against @('op');
     @('arg1-expr') and @('arg2-expr') are used just for errors.
     We return the type of the binary expression.")
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
  (case (binop-kind op)
    ((:mul :div :rem :add :sub)
     (if (and (type-arithmeticp arg1-type)
              (type-arithmeticp arg2-type))
         (uaconvert-types arg1-type arg2-type)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :arithmetic :arithmetic
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    ((:shl :shr)
     (if (and (type-integerp arg1-type)
              (type-integerp arg2-type))
         (promote-type arg1-type)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :integer :integer
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    ((:lt :gt :le :ge)
     (if (and (type-realp arg1-type)
              (type-realp arg2-type))
         (type-sint)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :real :real
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    ((:eq :ne)
     (if (and (type-arithmeticp arg1-type)
              (type-arithmeticp arg2-type))
         (type-sint)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :arithmetic :arithmetic
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    ((:bitand :bitxor :bitior)
     (if (and (type-integerp arg1-type)
              (type-integerp arg2-type))
         (uaconvert-types arg1-type arg2-type)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :integer :integer
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    ((:logand :logor)
     (if (and (type-scalarp arg1-type)
              (type-scalarp arg2-type))
         (type-sint)
       (error (list :binary-mistype
                (binop-fix op) (expr-fix arg1-expr) (expr-fix arg2-expr)
                :required :integer :integer
                :supplied (type-fix arg1-type) (type-fix arg2-type)))))
    (t (error (impossible))))
  :guard-hints (("Goal" :in-theory (enable type-arithmeticp
                                           type-realp
                                           binop-purep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-arrsub ((arr-expr exprp) (arr-type typep)
                      (sub-expr exprp) (sub-type typep))
  :returns (type type-resultp)
  :short "Check an array subscripting expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check @('arr-type') and @('sub-type');
     @('arr-expr') and @('sub-expr') are just used for errors.
     The first expression must have a pointer type [C:6.5.2.1/1].
     The second expression must have an integer type [C:6.5.2.1/1].
     The type of the array subscripting expression
     is the type referenced by the pointer.")
   (xdoc::p
    "For now we do not allow the roles of the expressions to be swapped,
     i.e. that the second expression is a pointer and the first one an integer;
     note the symmetry in [C:6.5.2.1/2].")
   (xdoc::p
    "The pointer type may be the result of an array-to-pointer conversion,
     via @(tsee apconvert-type) in @(tsee check-expr-pure)."))
  (b* (((unless (type-case arr-type :pointer))
        (error (list :array-mistype (expr-fix arr-expr)
                     :required :pointer
                     :supplied (type-fix arr-type))))
       ((unless (type-integerp sub-type))
        (error (list :subscript-mistype (expr-fix sub-expr)
                     :required :integer
                     :supplied (type-fix sub-type)))))
    (type-pointer->to arr-type))
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
     since they are not pure.")
   (xdoc::p
    "An identifier must be in the variable table.
     Its type is looked up there.
     An identifier is always an lvalue.")
   (xdoc::p
    "A constant is never an lvalue.")
   (xdoc::p
    "For an array subscripting expression,
     we do lvalue conversion for both operands,
     via @(tsee expr-type->type).
     According to [C:6.3.2/2],
     we should not do this for the first operand,
     if it has an array type;
     however, according to [C:6.3.2/3],
     we should convert the array to a pointer
     (which we do via @(tsee apconvert-type)),
     and thus in the end the result is the same:
     we have a pointer type, which we pass to @(tsee check-arrsub).
     In fact, we use @(tsee apconvert-type) on both operands,
     because the roles of the array and index may be swapped,
     as noted in @(tsee check-arrsub),
     even though we do not handle the swapping in that function for now.
     If an operand is an integer, @(tsee apconvert-type) has no effect.
     An array subscripting expression is always an lvalue;
     recall that it is like a form of the @('*') dereferencing expression.")
   (xdoc::p
    "For unary operators,
     we do not perform any lvalue or array-to-pointer conversion here,
     because that is done in @(tsee check-unary).
     We check the argument,
     pass the expression type to @(tsee check-unary),
     and forward the returned expression type (or error).")
   (xdoc::p
    "For binary operators, we apply
     both lvalue conversion and array-to-pointer conversion to the operand(s).
     The latter is needed because some operators work on scalars,
     and array-to-pointer conversion may produce a scalar.
     Unary and binary expressions are never lvalues;
     this is the case for the unary operators that we currently cover.")
   (xdoc::p
    "A cast is allowed between scalar types.
     Since we check that the type name denotes a scalar type,
     we do not need to check its well-formedness against the tag environment.
     The result has the type indicated in the cast.
     See [C:6.5.4]; note that the additional requirements on the type
     do not apply to our currently simplified model of C types.
     We apply lvalue conversion to the operand.
     We also apply array-to-pointer conversion,
     which could turn an array into a pointer (and thus scalar) type.
     A cast expression is never an lvalue.")
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
    "For a member expression with @('.') [C:6.5.2.3],
     we first check the target, ensuring it has a structure type.
     We do not do need to do array-to-pointer conversion,
     because we require the type to be a structure type,
     which rejects both array and pointer types.
     We look up the structure type and its member.
     We return its type, and we preserve the lvalue status:
     if the target is an lvalue, so is the member;
     if the target is not an lvalue, neither is the member.")
   (xdoc::p
    "For a member expression with @('->') [C:6.5.2.3],
     we first check the target,
     ensuring it has a pointer type to a structure type.
     We perform array-to-pointer conversion on this type,
     prior to ensuring it is a pointer to structure,
     as an array type would become a pointer type via that conversion.
     We look up the structure type and its member.
     We return the member type, with the lvalue flag set."))
  (b* ((e (expr-fix e)))
    (expr-case
     e
     :ident (b* ((type (var-table-lookup e.get vartab))
                 ((unless type) (error (list :var-not-found e.get))))
              (make-expr-type :type type :lvalue t))
     :const (b* ((type (check-const e.get))
                 ((when (errorp type)) type))
              (make-expr-type :type type :lvalue nil))
     :arrsub (b* ((arr-etype (check-expr-pure e.arr vartab tagenv))
                  ((when (errorp arr-etype))
                   (error (list :arrsub e arr-etype)))
                  (arr-type (expr-type->type arr-etype))
                  (arr-type (apconvert-type arr-type))
                  (sub-etype (check-expr-pure e.sub vartab tagenv))
                  ((when (errorp sub-etype))
                   (error (list :arrsub e sub-etype)))
                  (sub-type (expr-type->type sub-etype))
                  (sub-type (apconvert-type sub-type))
                  (type (check-arrsub e.arr arr-type e.sub sub-type))
                  ((when (errorp type)) type))
               (make-expr-type :type type :lvalue t))
     :call (error (list :expr-non-pure e))
     :member (b* ((etype (check-expr-pure e.target vartab tagenv))
                  ((when (errorp etype)) etype)
                  (type (expr-type->type etype))
                  (lvalue (expr-type->lvalue etype))
                  ((unless (type-case type :struct))
                   (error (list :dot-target-not-struct e)))
                  (tag (type-struct->tag type))
                  (memtype (struct-member-lookup tag e.name tagenv))
                  ((when (errorp memtype)) memtype))
               (make-expr-type :type memtype :lvalue lvalue))
     :memberp (b* ((etype (check-expr-pure e.target vartab tagenv))
                   ((when (errorp etype)) etype)
                   (type (expr-type->type etype))
                   (type (apconvert-type type))
                   ((unless (type-case type :pointer))
                    (error (list :arrow-operator-not-pointer e)))
                   (type (type-pointer->to type))
                   ((unless (type-case type :struct))
                    (error (list :arrow-operator-not-pointer-to-struct e)))
                   (tag (type-struct->tag type))
                   (memtype (struct-member-lookup tag e.name tagenv))
                   ((when (errorp memtype)) memtype))
                (make-expr-type :type memtype :lvalue t))
     :postinc (error (list :expr-non-pure e))
     :postdec (error (list :expr-non-pure e))
     :preinc (error (list :expr-non-pure e))
     :predec (error (list :expr-non-pure e))
     :unary (b* ((arg-etype (check-expr-pure e.arg vartab tagenv))
                 ((when (errorp arg-etype))
                  (error (list :unary-error arg-etype))))
              (check-unary e.op e.arg arg-etype))
     :cast (b* ((arg-etype (check-expr-pure e.arg vartab tagenv))
                ((when (errorp arg-etype))
                 (error (list :cast-error arg-etype)))
                (arg-type (expr-type->type arg-etype))
                (arg-type (apconvert-type arg-type))
                ((unless (type-scalarp arg-type))
                 (error (list :cast-mistype-operand e
                              :required :scalar
                              :supplied arg-type)))
                (type (tyname-to-type e.type))
                ((unless (type-scalarp type))
                 (error (list :cast-mistype-type e
                              :required :scalar
                              :supplied type))))
             (make-expr-type :type type :lvalue nil))
     :binary (b* (((unless (binop-purep e.op))
                   (error (list :binary-non-pure e)))
                  (arg1-etype (check-expr-pure e.arg1 vartab tagenv))
                  ((when (errorp arg1-etype))
                   (error (list :binary-left-error arg1-etype)))
                  (arg1-type (expr-type->type arg1-etype))
                  (arg1-type (apconvert-type arg1-type))
                  (arg2-etype (check-expr-pure e.arg2 vartab tagenv))
                  ((when (errorp arg2-etype))
                   (error (list :binary-right-error arg2-etype)))
                  (arg2-type (expr-type->type arg2-etype))
                  (arg2-type (apconvert-type arg2-type))
                  (type (check-binary-pure e.op
                                           e.arg1 arg1-type
                                           e.arg2 arg2-type))
                  ((when (errorp type)) type))
               (make-expr-type :type type :lvalue nil))
     :cond (b* ((test-etype (check-expr-pure e.test vartab tagenv))
                ((when (errorp test-etype))
                 (error (list :cond-test-error test-etype)))
                (test-type (expr-type->type test-etype))
                (test-type (apconvert-type test-type))
                ((unless (type-scalarp test-type))
                 (error (list :cond-mistype-test e.test e.then e.else
                              :required :scalar
                              :supplied test-type)))
                (then-etype (check-expr-pure e.then vartab tagenv))
                ((when (errorp then-etype))
                 (error (list :cond-then-error then-etype)))
                (then-type (expr-type->type then-etype))
                (then-type (apconvert-type then-type))
                ((unless (type-arithmeticp then-type))
                 (error (list :cond-mistype-then e.test e.then e.else
                              :required :arithmetic
                              :supplied then-type)))
                (else-etype (check-expr-pure e.else vartab tagenv))
                ((when (errorp else-etype))
                 (error (list :cond-else-error else-etype)))
                (else-type (expr-type->type else-etype))
                (else-type (apconvert-type else-type))
                ((unless (type-arithmeticp else-type))
                 (error (list :cond-mistype-else e.test e.then e.else
                              :required :arithmetic
                              :supplied else-type)))
                (then-type (promote-type then-type))
                (else-type (promote-type else-type))
                ((unless (equal then-type else-type))
                 (error (list :diff-promoted-types then-type else-type)))
                (type then-type))
             (make-expr-type :type type :lvalue nil))))
  :measure (expr-count e)
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
                            typep-when-type-resultp-and-not-errorp
                            type-listp-when-type-list-resultp-and-not-errorp))))
  :short "Check a list of pure expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for arguments of function calls.
     The expression types returned by the expressions
     are subjected to lvalue conversion and array-to-pointer conversion."))
  (b* (((when (endp es)) nil)
       (etype (check-expr-pure (car es) vartab tagenv))
       ((when (errorp etype)) etype)
       (type (expr-type->type etype))
       (type (apconvert-type type))
       (types (check-expr-pure-list (cdr es) vartab tagenv))
       ((when (errorp types)) types))
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
     this corresponds to the adjustment in [C:6.7.6.3/7];
     it is also, perhaps more aptly,
     consistent with the treatment of assignments
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
       (arg-types (check-expr-pure-list args vartab tagenv))
       ((when (errorp arg-types))
        (error (list :call-args-error fun args arg-types)))
       (arg-types (apconvert-type-list arg-types))
       (ftype (fun-table-lookup fun funtab))
       ((unless ftype) (error (list :fun-not-found fun)))
       (param-types (fun-type->inputs ftype))
       (param-types (apconvert-type-list param-types))
       ((unless (equal param-types arg-types))
        (error (list :call-args-mistype fun args
                     :required param-types
                     :supplied arg-types))))
    (fun-type->output ftype))
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
    (b* ((etype (check-expr-pure e vartab tagenv))
         ((when (errorp etype)) etype))
      (expr-type->type etype)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-asg ((e exprp)
                        (funtab fun-tablep)
                        (vartab var-tablep)
                        (tagenv tag-envp))
  :returns (wf? wellformed-resultp)
  :short "Check an expression that must be an assignment exrpression."
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
        (error (list :expr-asg-not-binary (expr-fix e))))
       (op (expr-binary->op e))
       (left (expr-binary->arg1 e))
       (right (expr-binary->arg2 e))
       ((unless (binop-case op :asg))
        (error (list :expr-asg-not-asg op)))
       (left-etype (check-expr-pure left vartab tagenv))
       ((when (errorp left-etype)) left-etype)
       (left-type (expr-type->type left-etype))
       (left-etype (if (type-case left-type :array)
                       (make-expr-type :type (apconvert-type left-type)
                                       :lvalue nil)
                     left-etype))
       ((unless (expr-type->lvalue left-etype))
        (error (list :asg-left-not-lvalue (expr-fix e))))
       (left-type (expr-type->type left-etype))
       (right-type (check-expr-call-or-pure right funtab vartab tagenv))
       ((when (errorp right-type)) right-type)
       (right-type (apconvert-type right-type))
       ((unless (equal left-type right-type))
        (error (list :asg-mistype left right
                     :required left-type
                     :supplied right-type)))
       ((unless (or (type-arithmeticp left-type)
                    (type-case left-type :struct)
                    (type-case left-type :pointer)))
        (error (list :expr-asg-disallowed-type left-type))))
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
      (b* ((type (check-expr-call (expr-call->fun e)
                                  (expr-call->args e)
                                  funtab
                                  vartab
                                  tagenv))
           ((when (errorp type)) type)
           ((unless (type-case type :void))
            (error (list :nonvoid-function-result-discarded (expr-fix e)))))
        :wellformed)
    (check-expr-asg e funtab vartab tagenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-initer ((initer initerp)
                      (funtab fun-tablep)
                      (vartab var-tablep)
                      (tagenv tag-envp))
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
     and we return their types as a list initialization type."))
  (initer-case
   initer
   :single
   (b* ((type (check-expr-call-or-pure initer.get funtab vartab tagenv))
        ((when (errorp type)) type))
     (init-type-single type))
   :list
   (b* ((types (check-expr-pure-list initer.get vartab tagenv))
        ((when (errorp types)) types))
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
    "Fow now we require the initializer type to be a single one,
     and to be equal to the declared type after array-to-pointer conversion.
     Thus, for now we only support initialization of scalars:
     if the declared type was an array type,
     it would never be equal to
     the array-to-pointer conversion of the initializer type,
     which turns an array type into a pointer type.
     Even though [C:6.7.9/11] allows scalars to be initialized with
     singleton lists of expressions (i.e. single expressions between braces),
     we are more strict here and require a single expression.")
   (xdoc::p
    "We will extend this to declared array types
     and to list initializer types."))
  (init-type-case
   itype
   :single (if (type-equiv type (apconvert-type itype.get))
               :wellformed
             (error (list :init-type-mismatch
                          :required (type-fix type)
                          :supplied (init-type-fix itype))))
   :list (error (list :init-type-unsupported (init-type-fix itype))))
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
    "These ACL2 functions return a statement type or an error;
     see @(tsee stmt-type).")
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
     we ensure that it is a variable (not a structure type) declaration.
     We ensure that the type is not @('void'),
     because the type must be complete [C:6.7/7],
     and @('void') is incomplete [C:6.2.5/19].
     We also ensure that the initializer has the same type as the variable
     (which is more restrictive than [C:6.7.9]),
     and we extend and return the variable table with the variable.
     We return the singleton set with @('void'),
     because a declaration never returns a value
     and proceeds with the next block item;
     note that we do not return the empty set of return types.")
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
    :returns (stype stmt-type-resultp)
    (stmt-case
     s
     :labeled (error (list :unsupported-labeled s.label s.body))
     :compound (b* ((ext-vartab (var-table-add-block vartab))
                    (stype (check-block-item-list s.items
                                                  funtab
                                                  ext-vartab
                                                  tagenv))
                    ((when (errorp stype))
                     (error (list :stmt-compound-error stype))))
                 (change-stmt-type stype :variables vartab))
     :expr (b* ((wf (check-expr-call-or-asg s.get funtab vartab tagenv))
                ((when (errorp wf)) (error (list :expr-stmt-error wf))))
             (make-stmt-type :return-types (set::insert (type-void) nil)
                             :variables (var-table-fix vartab)))
     :null (error :unsupported-null-stmt)
     :if (b* ((etype (check-expr-pure s.test vartab tagenv))
              ((when (errorp etype)) (error (list :if-test-error etype)))
              (type (expr-type->type etype))
              (type (apconvert-type type))
              ((unless (type-scalarp type))
               (error (list :if-test-mistype s.test s.then :noelse
                            :required :scalar
                            :supplied type)))
              (stype-then (check-stmt s.then funtab vartab tagenv))
              ((when (errorp stype-then))
               (error (list :if-then-error stype-then))))
           (make-stmt-type
            :return-types (set::union (stmt-type->return-types stype-then)
                                      (set::insert (type-void) nil))
            :variables vartab))
     :ifelse (b* ((etype (check-expr-pure s.test vartab tagenv))
                  ((when (errorp etype)) (error (list :if-test-error etype)))
                  (type (expr-type->type etype))
                  (type (apconvert-type type))
                  ((unless (type-scalarp type))
                   (error (list :if-test-mistype s.test s.then s.else
                                :required :scalar
                                :supplied type)))
                  (stype-then (check-stmt s.then funtab vartab tagenv))
                  ((when (errorp stype-then))
                   (error (list :if-then-error stype-then)))
                  (stype-else (check-stmt s.else funtab vartab tagenv))
                  ((when (errorp stype-else))
                   (error (list :if-else-error stype-else))))
               (make-stmt-type
                :return-types (set::union (stmt-type->return-types stype-then)
                                          (stmt-type->return-types stype-else))
                :variables vartab))
     :switch (error (list :unsupported-switch s.ctrl s.body))
     :while (b* ((etype (check-expr-pure s.test vartab tagenv))
                 ((when (errorp etype)) (error (list :while-test-error etype)))
                 (type (expr-type->type etype))
                 (type (apconvert-type type))
                 ((unless (type-scalarp type))
                  (error (list :while-test-mistype s.test s.body
                               :required :scalar
                               :supplied type)))
                 (stype-body (check-stmt s.body funtab vartab tagenv))
                 ((when (errorp stype-body))
                  (error (list :while-error stype-body))))
              (make-stmt-type
               :return-types (set::insert (type-void)
                                          (stmt-type->return-types stype-body))
               :variables vartab))
     :dowhile (error (list :unsupported-dowhile s.body s.test))
     :for (error (list :unsupported-for s.init s.test s.next s.body))
     :goto (error (list :unsupported-goto s.target))
     :continue (error :unsupported-continue)
     :break (error :unsupported-break)
     :return (b* (((unless s.value) (error (list :unsupported-return-void)))
                  (type (check-expr-call-or-pure s.value funtab vartab tagenv))
                  ((when (errorp type)) (error (list :return-error type)))
                  (type (apconvert-type type))
                  ((when (type-case type :void))
                   (error (list :return-void-expression s.value))))
               (make-stmt-type :return-types (set::insert type nil)
                               :variables vartab)))
    :measure (stmt-count s))

  (define check-block-item ((item block-itemp)
                            (funtab fun-tablep)
                            (vartab var-tablep)
                            (tagenv tag-envp))
    :returns (stype stmt-type-resultp)
    (block-item-case
     item
     :declon
     (b* (((mv var tyname init) (obj-declon-to-ident+tyname+init item.get))
          (wf (check-tyname tyname tagenv))
          ((when (errorp wf)) (error (list :declon-error-type wf)))
          (wf (check-ident var))
          ((when (errorp wf)) (error (list :declon-error-var wf)))
          (type (tyname-to-type tyname))
          ((when (type-case type :void))
           (error (list :declon-error-type-void item.get)))
          (init-type (check-initer init funtab vartab tagenv))
          ((when (errorp init-type))
           (error (list :declon-error-init init-type)))
          (wf? (init-type-matchp init-type type))
          ((when (errorp wf?)) wf?)
          (vartab (var-table-add-var var type vartab))
          ((when (errorp vartab)) (error (list :declon-error vartab))))
       (make-stmt-type :return-types (set::insert (type-void) nil)
                       :variables vartab))
     :stmt (check-stmt item.get funtab vartab tagenv))
    :measure (block-item-count item))

  (define check-block-item-list ((items block-item-listp)
                                 (funtab fun-tablep)
                                 (vartab var-tablep)
                                 (tagenv tag-envp))
    :returns (stype stmt-type-resultp)
    (b* (((when (endp items))
          (make-stmt-type :return-types (set::insert (type-void) nil)
                          :variables vartab))
         (stype (check-block-item (car items) funtab vartab tagenv))
         ((when (errorp stype)) (error (list :block-item-error stype)))
         ((when (endp (cdr items))) stype)
         (rtypes1 (set::delete (type-void) (stmt-type->return-types stype)))
         (vartab (stmt-type->variables stype))
         (stype (check-block-item-list (cdr items) funtab vartab tagenv))
         ((when (errorp stype)) (error (list :block-item-list-error stype)))
         (rtypes2 (stmt-type->return-types stype))
         (vartab (stmt-type->variables stype)))
      (make-stmt-type :return-types (set::union rtypes1 rtypes2)
                      :variables vartab))
    :measure (block-item-list-count items))

  :verify-guards nil ; done below
  ///
  (verify-guards check-stmt)

  (fty::deffixequiv-mutual check-stmt)

  (local
   (defthm-check-stmt-flag
     (defthm check-stmt-var-table
       (b* ((result (check-stmt s funtab vartab tagenv)))
         (implies (stmt-typep result)
                  (equal (stmt-type->variables result)
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
      (implies (stmt-typep result)
               (equal (stmt-type->variables result)
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
     and that the parameter can be added to the variable table;
     the latter check fails if there is a duplicate parameter.
     If all checks succeed, we return the variable table
     updated with the parameter.")
   (xdoc::p
    "We disallow @('void') as type of a parameter,
     because parameters must have complete types [C:6.7.6.3/4],
     but @('void') is incomplete [C:6.2.5/19]."))
  (b* (((mv var tyname) (param-declon-to-ident+tyname param))
       (wf (check-tyname tyname tagenv))
       ((when (errorp wf)) (error (list :param-type-error wf)))
       (wf (check-ident var))
       ((when (errorp wf)) (error (list :param-error wf)))
       (type (tyname-to-type tyname))
       ((when (type-case type :void))
        (error (list :param-error-void (param-declon-fix param)))))
    (var-table-add-var var type vartab))
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
       (vartab (check-param-declon (car params) vartab tagenv))
       ((when (errorp vartab)) (error (list :param-error vartab))))
    (check-param-declon-list (cdr params) vartab tagenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fun-declor ((declor fun-declorp) (tagenv tag-envp))
  :returns (vartab var-table-resultp)
  :short "Check a function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the pointers, if any.
     We check the identifier and the list of parameter declarations.
     We start with the empty variable table,
     and we return the final variable table that contains the parameters.
     This table is used when checking function definitions."))
  (fun-declor-case
   declor
   :base (b* ((wf (check-ident declor.name))
              ((when (errorp wf)) wf))
           (check-param-declon-list declor.params (var-table-init) tagenv))
   :pointer (check-fun-declor declor.decl tagenv))
  :measure (fun-declor-count declor)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fun-declon ((declon fun-declonp) (tagenv tag-envp))
  :returns (wf wellformed-resultp)
  :short "Check a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the type specifier sequence and the declarator.
     We do not return anything, because a function declaration,
     unlike a function definition, does not have a body to check
     (for which we need the variable table that contains the parameters)."))
  (b* (((fun-declon declon) declon)
       (wf (check-tyspecseq declon.tyspec tagenv))
       ((when (errorp wf)) wf)
       (vartab (check-fun-declor declon.declor tagenv))
       ((when (errorp vartab)) vartab))
    :wellformed)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-fundef ((fundef fundefp) (funtab fun-tablep) (tagenv tag-envp))
  :returns (new-funtab fun-table-resultp)
  :short "Check a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check type specifier sequence and declarator,
     obtaining the variable table that contains the parameters.
     Importantly, the block items are checked in the initial variable table,
     which has the types for the function parameters,
     without creating a new scope for the block (i.e. the compound statement):
     the reason is that the scope of function parameters
     terminates at the end of the associated block [C:6.2.1/4].")
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
       (wf (check-tyname out-tyname tagenv))
       ((when (errorp wf))
        (error (list :bad-fun-out-type name wf)))
       (out-type (tyname-to-type out-tyname))
       (vartab (check-fun-declor fundef.declor tagenv))
       ((when (errorp vartab)) (error (list :fundef-param-error vartab)))
       ((mv & in-tynames) (param-declon-list-to-ident+tyname-lists params))
       (in-types (type-name-list-to-type-list in-tynames))
       (ftype (make-fun-type :inputs in-types :output out-type))
       (funtab (fun-table-add-fun name ftype funtab))
       ((when (errorp funtab)) (error (list :fundef funtab)))
       (stype (check-block-item-list fundef.body funtab vartab tagenv))
       ((when (errorp stype)) (error (list :fundef-body-error stype)))
       ((unless (equal (stmt-type->return-types stype)
                       (set::insert out-type nil)))
        (error (list :fundef-return-mistype name
                     :required out-type
                     :inferred (stmt-type->return-types stype)))))
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
     (see @(tsee struct-declon)).
     We go through the declarations
     and turn each of them into member types (see @(tsee member-type)).
     We ensure that each member name is well-formed;
     we will also need to check that each member type is well-formed,
     but we need to extend our static semantics for that.
     By using @(tsee member-type-add-first),
     we ensure that there are no duplicate member names."))
  (b* (((when (endp declons)) nil)
       (members (check-struct-declon-list (cdr declons) tagenv))
       ((when (errorp members)) members)
       ((mv name tyname) (struct-declon-to-ident+tyname (car declons)))
       (wf (check-tyname tyname tagenv))
       ((when (errorp wf)) (error (list :bad-member-type wf)))
       (wf (check-ident name))
       ((when (errorp wf)) (error (list :bad-member-name wf)))
       (type (tyname-to-type tyname))
       (members-opt (member-type-add-first name type members)))
    (member-type-list-option-case members-opt
                                  :some members-opt.val
                                  :none (error (list :duplicate-member name))))
  :hooks (:fix))

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
     We ensure that there is at least one member [C:6.2.5/20].
     We use @(tsee tag-env-add) to ensure that there is not already
     another structure or union or enumeration type with the same tag,
     since these share one name space [C:6.2.3]."))
  (tag-declon-case
   declon
   :struct
   (b* ((members (check-struct-declon-list declon.members tagenv))
        ((when (errorp members)) members)
        ((unless (consp members))
         (error (list :empty-struct (tag-declon-fix declon))))
        (info (tag-info-struct members))
        (tagenv-opt (tag-env-add declon.tag info tagenv)))
     (tag-env-option-case tagenv-opt
                          :some tagenv-opt.val
                          :none (error (list :duplicate-tag declon.tag))))
   :union (error (list :union-not-supported (tag-declon-fix declon)))
   :enum (error (list :enum-not-supported (tag-declon-fix declon))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon ((ext ext-declonp)
                          (funtab fun-tablep)
                          (tagenv tag-envp))
  :returns (new-funtab+tagenv funtab+tagenv-resultp)
  :short "Check an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow function definitions and tag declarations.")
   (xdoc::p
    "If successful, we return updated function table and tag environment."))
  (ext-declon-case
   ext
   :fundef (b* ((funtab (check-fundef ext.get funtab tagenv))
                ((when (errorp funtab)) funtab))
             (make-funtab+tagenv :funs funtab
                                 :tags (tag-env-fix tagenv)))
   :obj-declon (error
                (list :file-level-object-declaraion-not-supported ext.get))
   :tag-declon (b* ((tagenv (check-tag-declon ext.get tagenv))
                    ((when (errorp tagenv)) tagenv))
                 (make-funtab+tagenv :funs (fun-table-fix funtab)
                                     :tags tagenv)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ext-declon-list ((exts ext-declon-listp)
                               (funtab fun-tablep)
                               (tagenv tag-envp))
  :returns (new-funtab+tagenv funtab+tagenv-resultp)
  :short "Check a list of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We thread the function table and tag environment through."))
  (b* (((when (endp exts))
        (make-funtab+tagenv :funs (fun-table-fix funtab)
                            :tags (tag-env-fix tagenv)))
       (funtab+tagenv (check-ext-declon (car exts) funtab tagenv))
       ((when (errorp funtab+tagenv))
        (error (list :ext-declon-error funtab+tagenv))))
    (check-ext-declon-list (cdr exts)
                           (funtab+tagenv->funs funtab+tagenv)
                           (funtab+tagenv->tags funtab+tagenv)))
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
     and discarding the final one (it served its pupose)."))
  (b* (((transunit tunit) tunit)
       (funtab (fun-table-init))
       (tagenv (tag-env-init))
       (funtab+tagenv (check-ext-declon-list tunit.declons funtab tagenv))
       ((when (errorp funtab+tagenv))
        (error (list :transunit-error funtab+tagenv))))
    :wellformed)
  :hooks (:fix))

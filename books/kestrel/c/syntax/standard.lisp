; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ standard
  :parents (syntax-for-tools)
  :short "Standard syntax (i.e. without GCC extensions)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax includes constructs for GCC extensions.
     Standard C syntax corresponds to a subset of our abstract syntax.
     Here we define predicates that characterize the standard subset.")
   (xdoc::p
    "In the future, we might defines predicates for subsets
     corresponding to different versions of standard C,
     different GCC extensions, etc.
     For now we just have a boolean choice (GCC extensions or not),
     and the full abstract syntax corresponds to including GCC extensions,
     while the predicates defined here correspond to excluding them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce standardp
  :short "Definition of the predicates that check whether
          the abstract syntax is standard C,
          i.e. without any GCC extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
   (xdoc::p
    "We use @('t') as @(':default') because
     there are more standard constructs than GCC extensions.")
   (xdoc::p
    "The @(':combine') operator is @(tsee and),
     because we need to check all the identifiers, recursively.")
   (xdoc::p
    "We override predicates for types that may involve GCC extensions.
     We exclude the @('\\%') simple escape,
     the variant keywords with underscores,
     absent `then' branchs in conditional expressions,
     statement epxressions,
     built-in functions that take type names as inputs,
     expressions preceded by @('__extension__'),
     the GCC type specifiers,
     the GCC declaration specifiers,
     GCC attributes,
     the empty structure declaration,
     and ranges in @('case')s.")
   (xdoc::p
    "Since we intend to use this predicate only on disambiguated ASTs,
     we add overridings for ambiguous constructs that thrown hard errors.
     Once @(tsee fty::deffold-reduce) is extended to support guards,
     we will add a guard saying that the AST are unambiguous instead."))
  :types (simple-escape
          escape
          c-char
          c-char-list
          cconst
          const
          s-char
          s-char-list
          stringlit
          stringlit-list
          type-qual
          fun-spec
          exprs/decls/stmts
          fundef
          extdecl
          extdecl-list
          transunit
          filepath-transunit-map
          transunit-ensemble)
  :result booleanp
  :default t
  :combine and
  :override
  ((simple-escape :percent nil)
   (type-qual :restrict (keyword-uscores-case
                         (type-qual-restrict->uscores type-qual) :none))
   (type-qual :volatile (keyword-uscores-case
                         (type-qual-volatile->uscores type-qual) :none))
   (fun-spec :inline (keyword-uscores-case
                      (fun-spec-inline->uscores fun-spec) :none))
   (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
                              (expr-fix expr)))
   (expr :alignof (and (tyname-standardp (expr-alignof->type expr))
                       (keyword-uscores-case
                        (expr-alignof->uscores expr) :none)))
   (expr :cond (and (expr-standardp (expr-cond->test expr))
                    (expr-option-case (expr-cond->then expr) :some)
                    (expr-standardp (expr-option-some->val
                                     (expr-cond->then expr)))
                    (expr-standardp (expr-cond->else expr))))
   (expr :cast/call-ambig (raise "Internal error: ambiguous ~x0."
                                 (expr-fix expr)))
   (expr :cast/mul-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/add-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/sub-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :cast/and-ambig (raise "Internal error: ambiguous ~x0."
                                (expr-fix expr)))
   (expr :stmt nil)
   (expr :tycompat nil)
   (expr :offsetof nil)
   (expr :va-arg nil)
   (expr :extension nil)
   (type-spec :signed (keyword-uscores-case
                       (type-spec-signed->uscores type-spec) :none))
   (type-spec :int128 nil)
   (type-spec :float32 nil)
   (type-spec :float32x nil)
   (type-spec :float64 nil)
   (type-spec :float64x nil)
   (type-spec :float128 nil)
   (type-spec :float128x nil)
   (type-spec :builtin-va-list nil)
   (type-spec :struct-empty nil)
   (type-spec :typeof-expr nil)
   (type-spec :typeof-type nil)
   (type-spec :typeof-ambig (raise "Internal error: ambiguous ~x0."
                                   (type-spec-fix type-spec)))
   (type-spec :auto-type nil)
   (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                     (align-spec-fix align-spec)))
   (decl-spec :attrib nil)
   (decl-spec :stdcall nil)
   (decl-spec :declspec nil)
   (typequal/attribspec :attrib nil)
   (dirabsdeclor :dummy-base (raise "Internal error: ~
                                     dummy base case of ~
                                     direct abstract declarator."))
   (struct-declon :member
                  (and (not (struct-declon-member->extension struct-declon))
                       (spec/qual-list-standardp
                        (struct-declon-member->specquals struct-declon))
                       (struct-declor-list-standardp
                        (struct-declon-member->declors struct-declon))
                       (endp (struct-declon-member->attrib struct-declon))))
   (struct-declon :empty nil)
   (attrib nil)
   (attrib-spec nil)
   (initdeclor (and (declor-standardp (initdeclor->declor initdeclor))
                    (not (initdeclor->asm? initdeclor))
                    (endp (initdeclor->attribs initdeclor))
                    (initer-option-standardp (initdeclor->init? initdeclor))))
   (decl :decl (and (not (decl-decl->extension decl))
                    (decl-spec-list-standardp (decl-decl->specs decl))
                    (initdeclor-list-standardp (decl-decl->init decl))))
   (label :casexpr (and (const-expr-standardp (label-casexpr->expr label))
                        (const-expr-option-case
                         (label-casexpr->range? label) :none)))
   (asm-output nil)
   (asm-input nil)
   (asm-stmt nil)
   (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                           (stmt-fix stmt)))
   (stmt :asm nil)
   (block-item :ambig (raise "Internal error: ambiguous ~x0."
                             (block-item-fix block-item)))
   (amb-expr/tyname (raise "Internal error: ambiguous ~x0."
                           (amb-expr/tyname-fix amb-expr/tyname)))
   (amb-declor/absdeclor (raise "Internal error: ambiguous ~x0."
                                (amb-declor/absdeclor-fix
                                 amb-declor/absdeclor)))
   (amb-decl/stmt (raise "Internal error: ambiguous ~x0."
                         (amb-decl/stmt-fix amb-decl/stmt)))
   (fundef (and (not (fundef->extension fundef))
                (decl-spec-list-standardp (fundef->spec fundef))
                (declor-standardp (fundef->declor fundef))
                (asm-name-spec-option-case (fundef->asm? fundef) :none)
                (endp (fundef->attribs fundef))
                (decl-list-standardp (fundef->decls fundef))
                (block-item-list-standardp (fundef->body fundef))))
   (extdecl :empty nil)
   (extdecl :asm nil)))

; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ purity
  :parents (syntax-for-tools)
  :short "Pure (i.e. side-effect-free) constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define predicates over ASTs that say whether
     the ASTs are pure, i.e. without side effects."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce purep
  :short "Definition of the predicates that check whether
          the abstract syntax is pure, i.e. without side effects."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee fty::deffold-reduce) to define these predicates concisely.")
   (xdoc::p
    "We use @('t') as @(':default') because
     non-recursive constructs (e.g. variables, constants) tend to be pure.")
   (xdoc::p
    "The @(':combine') operator is @(tsee and),
     because we need to check all sub-expressions.")
   (xdoc::p
    "We generate predicates for the unary and binary operators
     so that they are automatically used in unary and binary expressions.
     We exclude assignments as well as pre/post increment/decrement.")
   (xdoc::p
    "We generate predicates for expressions and related entities,
     but not for function definitions, external declarations, etc.,
     because the notion of purity does not really apply to them.")
   (xdoc::p
    "We conservatively exclude function calls,
     even though, depending on the called function,
     the call may be actually free of side effects.
     But this requires a more complicated analysis.")
   (xdoc::p
    "We exclude structure, union, and enumeration specifiers,
     which may bring new types into existence.")
   (xdoc::p
    "We exclude (parameter and plain) declarations,
     which may bring new entities into existence.
     This implies that block items that are declarations are excluded too.")
   (xdoc::p
    "We exclude assembler statements,
     because they may have side effects."))
  :types (unop
          binop
          exprs/decls/stmts)
  :result booleanp
  :default t
  :combine and
  :override
  ((unop :preinc nil)
   (unop :predec nil)
   (unop :postinc nil)
   (unop :postdec nil)
   (binop :asg nil)
   (binop :asg-mul nil)
   (binop :asg-div nil)
   (binop :asg-rem nil)
   (binop :asg-add nil)
   (binop :asg-sub nil)
   (binop :asg-shl nil)
   (binop :asg-shr nil)
   (binop :asg-and nil)
   (binop :asg-xor nil)
   (binop :asg-ior nil)
   (expr :funcall nil)
   (expr :sizeof-ambig (raise "Internal error: ambiguous ~x0."
                              (expr-fix expr)))
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
   (type-spec :struct nil)
   (type-spec :union nil)
   (type-spec :enum nil)
   (type-spec :struct-empty nil)
   (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                     (align-spec-fix align-spec)))
   (param-declon nil)
   (decl nil)
   (asm-stmt nil)
   (stmt :for-ambig (raise "Internal error: ambiguous ~x0."
                           (stmt-fix stmt)))
   (block-item :ambig (raise "Internal error: ambiguous ~x0."
                             (block-item-fix block-item)))
   (amb-expr/tyname (raise "Internal error: ambiguous ~x0."
                           (amb-expr/tyname-fix amb-expr/tyname)))
   (amb-declor/absdeclor (raise "Internal error: ambiguous ~x0."
                                (amb-declor/absdeclor-fix
                                 amb-declor/absdeclor)))
   (amb-decl/stmt (raise "Internal error: ambiguous ~x0."
                         (amb-decl/stmt-fix amb-decl/stmt)))))

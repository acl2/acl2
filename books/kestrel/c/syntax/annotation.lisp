; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "defpred")
(include-book "validator")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ annotation
  :parents (syntax-for-tools)
  :short "Annotation of the C abstract syntax of tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our @(see validator) adds some information (`annotations')
     to the abstract syntax constructs if it successfully validates them.
     We introduce predicates over the abstract syntax,
     to check that the annotations from the validator are present.
     This is not the same as saying that the constructs are validated;
     the predicates just say that information of the right type is present."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpred annop
  :short "Definition of the annotation predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee defpred) to define these predicates concisely.")
   (xdoc::p
    "The @(':default') value is @('t'),
     meaning that there are no constraints by default.")
   (xdoc::p
    "For now the only annotations added by the validator consist of
     a type in the information field of variables.
     As we extend the validator to generate more annotations,
     we will extend these predicates accordingly.")
   (xdoc::p
    "Since for now the validator accepts GCC attribute and other extensions
     without actually checking them and their constituents,
     we also have the annotation predicates accept those constructs.
     These are the cases overridden to return @('t')
     in the @(tsee defpred) for the ambiguity predicates.")
   (xdoc::p
    "The validator operates on unambiguous abstract syntax,
     which satisfies the @(see unambiguity) predicates.
     Ideally, the annotation predicates should use
     the unambiguity predicates as guards,
     but @(tsee defpred) does not support that feature yet.
     Thus, for now we add run-time checks, in the form of @(tsee raise),
     for the cases in which the unambiguity predicates do not hold;
     note that @(tsee raise) is logically @('nil'),
     so the annotation predicates are false on ambiguous constructs."))
  :default t
  :override
  ((expr :ident (typep expr.info))
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
   (type-spec :typeof-ambig (raise "Internal error: ambiguous ~x0."
                                   (type-spec-fix type-spec)))
   (align-spec :alignas-ambig (raise "Internal error: ambiguous ~x0."
                                     (align-spec-fix align-spec)))
   (dirabsdeclor :dummy-base (raise "Internal error: ~
                                       dummy base case of ~
                                       direct abstract declarator."))
   (attrib t)
   (attrib-spec t)
   (asm-output t)
   (asm-input t)
   (asm-stmt t)
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

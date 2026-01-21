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

(include-book "types")
(include-book "literals")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ expressions
  :parents (abstract-syntax)
  :short "Leo expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize an abstract syntactic representation
     of all the Leo expressions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unop
  :short "Fixtype of Leo unary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are logical negation,
     arithmetic negation (i.e. unary minus),
     and doubling.")
   (xdoc::p
    "This type does not distinguish between different
     syntaxes that can be used to create a unary operator;
     for example, @('!x') and @('x.not()') both create an
     expression of kind @(':unary) with op @('(unop-not)').
     This is because these two syntaxes have the same
     meaning.  However, if we wish to capture such
     information we could do that here.")
   (xdoc::p
    "See @(see unop-for-opcall-name) for more information."))
  ;; these have both prefix and operator call syntaxes:
  (:neg ())
  (:not ())
  ;; these have only operator call syntax:
  (:abs ())
  (:abs-wrapped ())
  (:double ())
  (:inv ())
  (:square-root ())
  (:square ())
  :pred unopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult unop-result
  :short "Fixtype of errors and Leo unary operators."
  :ok unop
  :pred unop-resultp
  :prepwork ((local (in-theory (e/d (unop-kind) (unopp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum binop
  :short "Fixtype of Leo binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are
     the four boolean operations,
     the six comparisons,
     the three bitwise operations,
     the four shift operations,
     the ten arithmetic operations,
     and two raise-to-power operations.")
   (xdoc::p
    "This type does not distinguish between different
     syntaxes that can be used to create a binary operator;
     for example, @('a>b') and @('a.gt(b)') both create an
     expression of kind @(':binary) with op @('(binop-gt)').
     This is because these two syntaxes have the same
     meaning.  However, if we wish to capture such
     information we could do that here.")
   (xdoc::p
    "See @(see binop-for-opcall-name) for more information."))

  ;; --------------------
  ;; these have only infix syntax:
  (:and ())
  (:or ())

  ;; --------------------
  ;; these have both infix and operator call syntaxes:
  (:eq ())
  (:ne ())
  (:ge ())
  (:gt ())
  (:le ())
  (:lt ())
  ;; witwise operations
  (:bitxor ())
  (:bitior ())
  (:bitand ())
  ;; shift operations
  (:shl ())
  (:shr ())
  ;; arithmetic operations
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:rem ())
  ;; raise-to-power operation
  (:pow ())

  ;; --------------------
  ;; These have only operator call syntax

  ;; Addtional boolean ops (single bit only)
  ;; (Short-circuiting status unknown, fill in later.)
  (:nand ())
  (:nor ())
  ;; Additional shift operations
; semantics needs clarification; also problem with SnarkVM, dot in Identifier 'shl.w'
  (:shl-wrapped ())
  (:shr-wrapped ())
  ;; Additional arithmetic operations
  (:add-wrapped ())
  (:sub-wrapped ())
  (:mul-wrapped ())
  (:div-wrapped ())
  (:rem-wrapped ())
  ;; Additional raise-to-power-operation
  (:pow-wrapped ())

  :pred binopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult binop-result
  :short "Fixtype of errors and Leo binary operators."
  :ok binop
  :pred binop-resultp
  :prepwork ((local (in-theory (e/d (binop-kind) (binopp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes expression-fixtypes
  :short "Mutually recursive fixtypes of Leo expressions."

  (fty::deftagsum expression
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of Leo expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "There are
       literals,
       identifiers (i.e. variables and free constants),
       associated constants,
       unary expressions,
       binary expressions,
       conditional (ternary) expressions,
       unit expressions,
       tuple expressions,
       tuple component expressions,
       struct expressions,
       struct component expressions,
       and free function calls.")
     (xdoc::p
      "At the level of abstract syntax,
       there is no need to represent paranthesized expressions.
       The tree structure of the abstract syntax provides the grouping.")
     (xdoc::p
      "A unit expression is used instead of a tuple expression of zero components.")
     (xdoc::p
      "Even though tuple expressions
       are required to have two or more components in the grammar,
       we do not have this restriction at the level of abstract syntax.")
     (xdoc::p
      "Even though struct expressions
       are prohibited from having no components in the grammar,
       we do not have this restriction at the level of abstract syntax."))
    (:literal ((get literal)))
    (:var/const ((name identifier)))
    (:assoc-const ((type type
                         :reqfix
                         (if (type-namedp type)
                             type
                           (make-type-internal-named
                            :get (identifier-fix :irrelevant)
                            :recordp nil)))
                   (name identifier))
                  :require (type-namedp type))
    (:unary ((op unop)
             (arg expression)))
    (:binary ((op binop)
              (arg1 expression)
              (arg2 expression)))
    (:cond ((test expression)
            (then expression)
            (else expression)))
    (:unit ())
    (:tuple ((components expression-list)))
    (:tuple-component ((tuple expression)
                       (index nat)))
    (:struct ((type identifier)
               (components struct-init-list)))
    (:struct-component ((struct expression)
                         (component identifier)))
    (:internal-call ((fun identifier)
                     (args expression-list)))
    (:external-call ((fun locator)
                     (args expression-list)))
    ;; Note that the following allows :external-named types
    ;; as the type field.
    ;; We are not sure those will be needed, however.
    (:static-call ((type type
                         :reqfix
                         (if (type-namedp type)
                             type
                           (make-type-internal-named
                            :get (identifier-fix :irrelevant)
                            :recordp nil)))
                   (fun identifier)
                   (args expression-list))
                  :require (type-namedp type))
    :pred expressionp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist expression-list
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of lists of Leo expressions."
    :elt-type expression
    :true-listp t
    :elementp-of-nil nil
    :pred expression-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod struct-init
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of Leo struct component initializers."
    :long
    (xdoc::topstring
     (xdoc::p
      "Here we represent them in canonical form,
       i.e. as an identifier and an expression.
       The abbreviated form is just a concrete syntax convenience."))
    ((name identifier)
     (expr expression))
    :pred struct-initp
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist struct-init-list
    :parents (abstract-syntax expression-fixtypes)
    :short "Fixtype of lists of Leo struct component initializers."
    :elt-type struct-init
    :true-listp t
    :elementp-of-nil nil
    :pred struct-init-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption expression-option
  expression
  :short "Fixtype of optional Leo expressions."
  :pred expression-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-result
  :short "Fixtype of errors and Leo expressions."
  :ok expression
  :pred expression-resultp
  :prepwork ((local (in-theory (e/d (expression-kind) (expressionp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-list-result
  :short "Fixtype of errors and lists of Leo expressions."
  :ok expression-list
  :pred expression-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expression-option-result
  :short "Fixtype of errors and optional Leo expressions."
  :ok expression-option
  :pred expression-option-resultp
  :prepwork ((local (in-theory (enable expressionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult struct-init-result
  :short "Fixtype of errors and Leo struct initializers."
  :ok struct-init
  :pred struct-init-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult struct-init-list-result
  :short "Fixtype of errors and lists of Leo struct initializers."
  :ok struct-init-list
  :pred struct-init-list-resultp)

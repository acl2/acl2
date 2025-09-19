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

(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-irrelevants
  :parents (abstract-syntax)
  :short "Irrelevant values of the abstract syntax fixtypes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are nullary operations that return
     ``irrelevant'' values of the fixtypes that form the abstract syntax,
     i.e. values that are never actually used.
     For instance, an ACL2 function that returns multiple results,
     the first one of which is an error indication,
     while the other results include abstract syntax entities,
     could return irrelevant values as the latter results
     when the first result indicates an error.")
   (xdoc::p
    "The definitions are mostly boilerplate,
     except that in some places we put something conveying irrelevance,
     e.g. in the definition of @(tsee irr-ident).
     However, this is really unnecessary, and it should be possible to
     define all of these according to boilerplate.
     This could be an extension of the FTY library;
     perhaps every fixtype definition could also generate
     some kind of ``default'' value of the fixtype,
     which could be used as an irrelevant value in the sense explained above.")
   (xdoc::p
    "For now, we collect these nullary functions in this file and XDOC topic,
     to keep the file and XDOC topic of the abstract syntax tidier.")
   (xdoc::p
    "Note that some fixtypes do not have an irrelevant value defined here,
     because there are already very short built-in values that can be used,
     such as @('nil') for list and option types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ident
  :short "An irrelevant identifier."
  :type identp
  :body (ident "IRRELEVANT"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-iconst
  :short "An irrelevant integer constant."
  :type iconstp
  :body (make-iconst :core (dec/oct/hex-const-dec 1)
                     :suffix? nil
                     :info nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dec-expo-prefix
  :short "An irrelevant decimal exponent prefix."
  :type dec-expo-prefixp
  :body (dec-expo-prefix-locase-e))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-bin-expo-prefix
  :short "An irrelevant binary exponent prefix."
  :type bin-expo-prefixp
  :body (bin-expo-prefix-locase-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dec-expo
  :short "An irrelevant decimal exponent."
  :type dec-expop
  :body (make-dec-expo :prefix (irr-dec-expo-prefix)
                       :sign? nil
                       :digits nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-bin-expo
  :short "An irrelevant binary exponent."
  :type bin-expop
  :body (make-bin-expo :prefix (irr-bin-expo-prefix)
                       :sign? nil
                       :digits nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-hex-quad
  :short "An irrelevant quadruple of hexadecimal digits."
  :type hex-quad-p
  :body (make-hex-quad :1st #\0 :2nd #\0 :3rd #\0 :4th #\0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-escape
  :short "An irrelevant escape."
  :type escapep
  :body (escape-hex nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-const
  :short "An irrelevant constant."
  :type constp
  :body (const-enum (ident "IRRELEVANT")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-stringlit
  :short "An irrelevant string literal."
  :type stringlitp
  :body (make-stringlit :prefix? nil :schars nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-header-name
  :short "An irrelevant header name."
  :type header-namep
  :body (header-name-angles nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-unop
  :short "An irrelevant unary operator."
  :type unopp
  :body (unop-address))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-binop
  :short "An irrelevant binary operator."
  :type binopp
  :body (binop-asg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-stor-spec
  :short "An irrelevant storage class specifier."
  :type stor-specp
  :body (stor-spec-typedef))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-type-qual
  :short "An irrelevant type qualifier."
  :type type-qualp
  :body (type-qual-const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-fun-spec
  :short "An irrelevant function specifier."
  :type fun-specp
  :body (fun-spec-noreturn))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-name-spec
  :short "An irrelevant assembler name specifier."
  :type asm-name-specp
  :body (asm-name-spec nil (keyword-uscores-none)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-qual
  :short "An irrelevant assembler qualifier."
  :type asm-qualp
  :body (asm-qual-goto))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-clobber
  :short "An irrelevant assembler clobber."
  :type asm-clobberp
  :body (asm-clobber nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr
  :short "An irrelevant expression."
  :type exprp
  :body (make-expr-ident :ident (irr-ident) :info nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-const-expr
  :short "An irrelevant constant expression."
  :type const-exprp
  :body (const-expr (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-genassoc
  :short "An irrelevant generic association."
  :type genassocp
  :body (genassoc-default (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-member-designor
  :short "An irrelevant member designator."
  :type member-designorp
  :body (member-designor-ident (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-type-spec
  :short "An irrelevant type specifier."
  :type type-specp
  :body (type-spec-void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-spec/qual
  :short "An irrelevant type specifier or type qualifier."
  :type spec/qual-p
  :body (spec/qual-typespec (irr-type-spec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-align-spec
  :short "An irrelevant alignment specifier."
  :type align-specp
  :body (align-spec-alignas-expr (irr-const-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-decl-spec
  :short "An irrelevant declaration specifier."
  :type decl-specp
  :body (decl-spec-typespec (irr-type-spec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-typequal/attribspec
  :short "An irrelevant type qualifier or attribute specifier."
  :type typequal/attribspec-p
  :body (typequal/attribspec-type (irr-type-qual)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer
  :short "An irrelevant initializer."
  :type initerp
  :body (initer-single (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-desiniter
  :short "An irrelevant initializer with optional designation."
  :type desiniterp
  :body (make-desiniter :designors nil :initer (irr-initer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-designor
  :short "An irrelevant designator."
  :type designorp
  :body (designor-dot (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-declor
  :short "An irrelevant declarator."
  :type declorp
  :body (make-declor :pointers nil :direct (dirdeclor-ident (irr-ident))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dirdeclor
  :short "An irrelevant direct declarator."
  :type dirdeclorp
  :body (dirdeclor-ident (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-absdeclor
  :short "An irrelevant abstract declarator."
  :type absdeclorp
  :body (make-absdeclor :pointers nil :direct? nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dirabsdeclor
  :short "An irrelevant direct abstract declarator."
  :type dirabsdeclorp
  :body (dirabsdeclor-paren (irr-absdeclor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-param-declon
  :short "An irrelevant parameter declaration."
  :type param-declonp
  :body (make-param-declon :specs nil
                           :declor (param-declor-none)
                           :attribs nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-param-declor
  :short "An irrelevant parameter declarator."
  :type param-declorp
  :body (param-declor-none))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyname
  :short "An irrelevant type name."
  :type tynamep
  :body (tyname nil nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-struni-spec
  :short "An irrelevant structure or union specifier."
  :type struni-specp
  :body (make-struni-spec :name? nil :members nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-struct-declon
  :short "An irrelevant structure declaration."
  :type struct-declonp
  :body (make-struct-declon-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-struct-declor
  :short "An irrelevant structure declarator."
  :type struct-declorp
  :body (make-struct-declor :declor? nil :expr? nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-enum-spec
  :short "An irrelevant enumeration specifier."
  :type enum-specp
  :body (make-enum-spec :name nil :list nil :final-comma nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-enumer
  :short "An irrelevant enumerator."
  :type enumerp
  :body (make-enumer :name (irr-ident) :value nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-statassert
  :short "An irrelevant static assertion declaration."
  :type statassertp
  :body (make-statassert :test (irr-const-expr)
                         :message (list (irr-stringlit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-attrib-name
  :short "An irrelevant attribute name."
  :type attrib-namep
  :body (attrib-name-ident (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-attrib
  :short "An irrelevant attribute."
  :type attribp
  :body (attrib-name-only (irr-attrib-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-attrib-spec
  :short "An irrelevant attribute specifier."
  :type attrib-specp
  :body (attrib-spec nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initdeclor
  :short "An irrelevant initializer declarator."
  :type initdeclorp
  :body (make-initdeclor :declor (irr-declor)
                         :asm? nil
                         :attribs nil
                         :init? nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-decl
  :short "An irrelevant declaration."
  :type declp
  :body (make-decl-decl :extension nil
                        :specs nil
                        :init nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-label
  :short "An irrelevant label."
  :type labelp
  :body (label-default))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-output
  :short "An irrelevant assembler output operand."
  :type asm-outputp
  :body (make-asm-output :name nil :constraint nil :lvalue (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-input
  :short "An irrelevant assembler input operand."
  :type asm-inputp
  :body (make-asm-input :name nil :constraint nil :rvalue (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-asm-stmt
  :short "An irrelevant assembler statement."
  :type asm-stmtp
  :body (make-asm-stmt :uscores (keyword-uscores-none)
                       :quals nil
                       :template nil
                       :num-colons 0
                       :outputs nil
                       :inputs nil
                       :clobbers nil
                       :labels nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-stmt
  :short "An irrelevant statement."
  :type stmtp
  :body (stmt-compound nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-block-item
  :short "An irrelevant block item."
  :type block-itemp
  :body (block-item-stmt (irr-stmt) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr/tyname
  :short "An irrelevant expression or type name."
  :type expr/tyname-p
  :body (expr/tyname-expr (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-declor/absdeclor
  :short "An irrelevant declarator or abstract declarator."
  :type declor/absdeclor-p
  :body (declor/absdeclor-declor (irr-declor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-decl/stmt
  :short "An irrelevant declaration or statement."
  :type decl/stmt-p
  :body (decl/stmt-decl (irr-decl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-amb?-expr/tyname
  :short "An irrelevant possibly ambiguous expression or type name."
  :type amb?-expr/tyname-p
  :body (amb?-expr/tyname-expr (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-amb?-declor/absdeclor
  :short "An irrelevant possibly ambiguous declarators or abstract declarators."
  :type amb?-declor/absdeclor-p
  :body (amb?-declor/absdeclor-declor (irr-declor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-amb?-decl/stmt
  :short "An irrelevant possibly ambiguous declaration or statement."
  :type amb?-decl/stmt-p
  :body (amb?-decl/stmt-stmt (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-fundef
  :short "An irrelevant function definition."
  :type fundefp
  :body (make-fundef :extension nil
                     :spec nil
                     :declor (irr-declor)
                     :asm? nil
                     :attribs nil
                     :decls nil
                     :body nil
                     :info nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-extdecl
  :short "An irrelevant external declaration."
  :type extdeclp
  :body (extdecl-decl (irr-decl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit
  :short "An irrelevant translation unit."
  :type transunitp
  :body (transunit nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit-ensemble
  :short "An irrelevant ensemble of translation units."
  :type transunit-ensemblep
  :body (transunit-ensemble nil))

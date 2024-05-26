; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (abstract-syntax)
  :short "Operations on the abstract syntax."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-unary/postfix/primary-p ((expr exprp))
  :returns (yes/no booleanp)
  :short "Check if an expression is unary or postfix or primary."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar definition,
     unary expressions include postfix and primary expressions;
     the grammar defines expressions hierarchically.
     So this test, performed on abstract syntax,
     is equivalent to testing whether the expression
     is a unary one according to the grammar."))
  (and (member-eq (expr-kind expr)
                  '(:ident
                    :const
                    :string
                    :paren
                    :gensel
                    :arrsub
                    :funcall
                    :member
                    :memberp
                    :complit
                    :unary
                    :sizeof
                    :sizeof-ambig
                    :alignof))
       t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ident
  :short "An irrelevant identifier."
  :type identp
  :body (ident "IRRELEVANT"))

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
  :body (make-stringlit :prefix nil :schars nil))

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

(defirrelevant irr-stoclaspec
  :short "An irrelevant storage class specifier."
  :type stoclaspecp
  :body (stoclaspec-tydef))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyqual
  :short "An irrelevant type qualifier."
  :type tyqualp
  :body (tyqual-const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-funspec
  :short "An irrelevant function specifier."
  :type funspecp
  :body (funspec-inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr
  :short "An irrelevant expression."
  :type exprp
  :body (expr-ident (irr-ident)))

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

(defirrelevant irr-tyspec
  :short "An irrelevant type specifier."
  :type tyspecp
  :body (tyspec-void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-specqual
  :short "An irrelevant type specifier or type qualifier."
  :type specqualp
  :body (specqual-tyspec (irr-tyspec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-alignspec
  :short "An irrelevant alignment specifier."
  :type alignspecp
  :body (alignspec-alignas-ambig (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-declspec
  :short "An irrelevant declaration specifier."
  :type declspecp
  :body (declspec-tyspec (irr-tyspec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer
  :short "An irrelevant initializer."
  :type initerp
  :body (initer-single (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-desiniter
  :short "An irrelevant initializer with optional designation."
  :type desiniterp
  :body (make-desiniter :design nil :init (irr-initer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-designor
  :short "An irrelevant designator."
  :type designorp
  :body (designor-dot (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-declor
  :short "An irrelevant declarator."
  :type declorp
  :body (make-declor :pointers nil :decl (dirdeclor-ident (irr-ident))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dirdeclor
  :short "An irrelevant direct declarator."
  :type dirdeclorp
  :body (dirdeclor-ident (irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-absdeclor
  :short "An irrelevant abstract declarator."
  :type absdeclorp
  :body (make-absdeclor :pointers nil :decl? nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dirabsdeclor
  :short "An irrelevant direct abstract declarator."
  :type dirabsdeclorp
  :body (dirabsdeclor-dummy-base))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-paramdecl
  :short "An irrelevant parameter declaration."
  :type paramdeclp
  :body (make-paramdecl-nonabstract :spec nil :decl (irr-declor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyname
  :short "An irrelevant type name."
  :type tynamep
  :body (tyname nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-strunispec
  :short "An irrelevant structure or union specifier."
  :type strunispecp
  :body (make-strunispec :name nil :members nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-structdeclor
  :short "An irrelevant structure declarator."
  :type structdeclorp
  :body (make-structdeclor :declor (irr-declor) :expr (irr-const-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-structdecl
  :short "An irrelevant structure declaration."
  :type structdeclp
  :body (make-structdecl-member :specqual nil :declor nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-enumspec
  :short "An irrelevant enumeration specifier."
  :type enumspecp
  :body (make-enumspec :name nil :list nil :final-comma nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-enumer
  :short "An irrelevant enumerator."
  :type enumerp
  :body (make-enumer :name (irr-ident) :value nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-statassert
  :short "An irrelevant static assertion declaration."
  :type statassertp
  :body (make-statassert :test (irr-const-expr) :message (irr-stringlit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-decl
  :short "An irrelevant declaration."
  :type declp
  :body (make-decl-decl :specs nil :init nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-extdecl
  :short "An irrelevant external declaration."
  :type extdeclp
  :body (extdecl-decl (irr-decl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit
  :short "An irrelevant translation unit."
  :type transunitp
  :body (transunit nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit-ensemble
  :short "An irrelevant ensemble of translation units."
  :type transunit-ensemblep
  :body (transunit-ensemble nil))

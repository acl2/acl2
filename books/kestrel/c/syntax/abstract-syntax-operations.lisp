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

(include-book "std/util/defirrelevant" :dir :system)

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
  :body (make-stringlit :prefix? nil :schars nil))

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
  :body (make-absdeclor :pointers nil :decl? nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-dirabsdeclor
  :short "An irrelevant direct abstract declarator."
  :type dirabsdeclorp
  :body (dirabsdeclor-paren (irr-absdeclor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-paramdecl
  :short "An irrelevant parameter declaration."
  :type paramdeclp
  :body (make-paramdecl :spec nil :decl (paramdeclor-none)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-paramdeclor
  :short "An irrelevant parameter declarator."
  :type paramdeclorp
  :body (paramdeclor-none))

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

(defirrelevant irr-structdecl
  :short "An irrelevant structure declaration."
  :type structdeclp
  :body (make-structdecl-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-structdeclor
  :short "An irrelevant structure declarator."
  :type structdeclorp
  :body (make-structdeclor :declor? nil :expr? nil))

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
  :body (block-item-stmt (irr-stmt)))

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
                     :body (irr-stmt)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringlit-list->prefix?-list ((strlits stringlit-listp))
  :returns (prefixes eprefix-option-listp)
  :short "Lift @(tsee stringlit->prefix?) to lists."
  (cond ((endp strlits) nil)
        (t (cons (stringlit->prefix? (car strlits))
                 (stringlit-list->prefix?-list (cdr strlits)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-postfix/primary-p ((expr exprp))
  :returns (yes/no booleanp)
  :short "Check if an expression is postfix or primary."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the grammar definition,
     postfix expressions include primary expressions;
     the grammar defines expressions hierarchically.
     So this test, performed on abstract syntax,
     is equivalent to testing whether the expression
     is a postfix one according to the grammar."))
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
                    :stmt
                    :tycompat
                    :offsetof
                    :va-arg
                    :extension))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                    :alignof
                    :stmt
                    :tycompat
                    :offsetof
                    :va-arg
                    :extension))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expr-priority
  :short "Fixtype of expression priorities."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar defines different kinds of expressions
     in order to specify their relative priorities.
     This fixtype corresponds to those kinds/priorities of expressions,
     straighforwardly derived from the grammar.
     The @(':expr') case is for top-level expressions,
     i.e. the rule name @('expression') in the ABNF grammar."))
  (:primary ())
  (:postfix ())
  (:unary ())
  (:cast ())
  (:mul ())
  (:add ())
  (:sh ())
  (:rel ())
  (:eq ())
  (:and ())
  (:xor ())
  (:ior ())
  (:logand ())
  (:logor ())
  (:cond ())
  (:asg ())
  (:expr ())
  :pred expr-priorityp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop->priority ((op binopp))
  :returns (priority expr-priorityp)
  :short "Priority of (binary expressions with) operators."
  (binop-case
   op
   :mul (expr-priority-mul)
   :div (expr-priority-mul)
   :rem (expr-priority-mul)
   :add (expr-priority-add)
   :sub (expr-priority-add)
   :shl (expr-priority-sh)
   :shr (expr-priority-sh)
   :lt (expr-priority-rel)
   :gt (expr-priority-rel)
   :le (expr-priority-rel)
   :ge (expr-priority-rel)
   :eq (expr-priority-eq)
   :ne (expr-priority-eq)
   :bitand (expr-priority-and)
   :bitxor (expr-priority-xor)
   :bitior (expr-priority-ior)
   :logand (expr-priority-logand)
   :logor (expr-priority-logor)
   :asg (expr-priority-asg)
   :asg-mul (expr-priority-asg)
   :asg-div (expr-priority-asg)
   :asg-rem (expr-priority-asg)
   :asg-add (expr-priority-asg)
   :asg-sub (expr-priority-asg)
   :asg-shl (expr-priority-asg)
   :asg-shr (expr-priority-asg)
   :asg-and (expr-priority-asg)
   :asg-xor (expr-priority-asg)
   :asg-ior (expr-priority-asg))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr->priority ((expr exprp))
  :returns (priority expr-priorityp)
  :short "Priorities of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each expression in the abstract syntax
     has an associated priority (see @(tsee expr-priority)),
     straightforwardly according to the grammar.")
   (xdoc::p
    "An ambiguous @('sizeof') has the same priority as an unambiguous one.
     An ambiguous cast/call expression is given
     the higher priority of the two possibilities,
     i.e. the priority of a postfix expression.
     Ambiguous cast/binary expressions are given
     the higher priority of the two possibilities,
     i.e. the priority of a cast expression."))
  (expr-case
   expr
   :ident (expr-priority-primary)
   :const (expr-priority-primary)
   :string (expr-priority-primary)
   :paren (expr-priority-primary)
   :gensel (expr-priority-primary)
   :arrsub (expr-priority-postfix)
   :funcall (expr-priority-postfix)
   :member (expr-priority-postfix)
   :memberp (expr-priority-postfix)
   :complit (expr-priority-postfix)
   :unary (expr-priority-unary)
   :sizeof (expr-priority-unary)
   :sizeof-ambig (expr-priority-unary)
   :alignof (expr-priority-unary)
   :cast (expr-priority-cast)
   :binary (binop->priority expr.op)
   :cond (expr-priority-cond)
   :comma (expr-priority-expr)
   :cast/call-ambig (expr-priority-postfix)
   :cast/mul-ambig (expr-priority-cast)
   :cast/add-ambig (expr-priority-cast)
   :cast/sub-ambig (expr-priority-cast)
   :cast/and-ambig (expr-priority-cast)
   :stmt (expr-priority-primary)
   :tycompat (expr-priority-primary)
   :offsetof (expr-priority-primary)
   :va-arg (expr-priority-primary)
   :extension (expr-priority-primary))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-priority-<= ((prio1 expr-priorityp) (prio2 expr-priorityp))
  :returns (yes/no booleanp)
  :short "Total order on expression priorities: less than or equal to."
  :long
  (xdoc::topstring
   (xdoc::p
    "We assign a unique numeric index to each priority,
     and we compare the numbers.
     The higher the priority, the higher the number.
     The exact numbers do not matter;
     only their relative magnitude does.")
   (xdoc::p
    "This total order on expression priorities is
     the reflexive and transitive closure of the binary relation
     that consists of the pairs @('priority1 < priority2') such that
     there is a grammar (sub)rule <i>nonterm1: nonterm2</i>
     saying that the nonterminal <i>nonterm1</i>
     corresponding to @('priority1')
     may expand to the nonterminal <i>nonterm2</i>
     corresponding to @('priority2').
     For instance, @('priority2') is the priority of multiplicative expressions
     and @('priority1') is the priority of additive expressions,
     because there is a (sub)rule
     <i>additive-expression: multiplicative-expression</i> in the grammar.
     (Here by `subrule' we mean a rule not necessarily in the grammar
     but obtainable by selecting just some of the alternatives in the definiens
     that are on different lines in [C].)
     The nonterminal <i>additive-expression</i> also has other alternatives,
     but those are not single nonterminals;
     here we are only concerned with single nonterminals as rule definientia."))
  (<= (expr-priority-number prio1)
      (expr-priority-number prio2))
  :hooks (:fix)

  :prepwork
  ((define expr-priority-number ((prio expr-priorityp))
     :returns (number natp)
     :parents nil
     (expr-priority-case
      prio
      :primary 16
      :postfix 15
      :unary 14
      :cast 13
      :mul 12
      :add 11
      :sh 10
      :rel 9
      :eq 8
      :and 7
      :xor 6
      :ior 5
      :logand 4
      :logor 3
      :cond 2
      :asg 1
      :expr 0)
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;

(define expr-priority->= ((prio1 expr-priorityp) (prio2 expr-priorityp))
  :returns (yes/no booleanp)
  :short "Total order on expression priorities: greater than or equal to."
  (expr-priority-<= prio2 prio1)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define expr-priority-< ((prio1 expr-priorityp) (prio2 expr-priorityp))
  :returns (yes/no booleanp)
  :short "Total order on expression priorities: less than."
  (not (expr-priority-<= prio2 prio1))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define expr-priority-> ((prio1 expr-priorityp) (prio2 expr-priorityp))
  :returns (yes/no booleanp)
  :short "Total order on expression priorities: greater than."
  (not (expr-priority-<= prio1 prio2))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-expected-priorities ((op binopp))
  :returns (mv (left-prio expr-priorityp)
               (right-prio expr-priorityp))
  :short "Expected expression priorities
          of the operands of the binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are straightforwardly based on the grammar rules."))
  (binop-case op
              :mul (mv (expr-priority-mul) (expr-priority-cast))
              :div (mv (expr-priority-mul) (expr-priority-cast))
              :rem (mv (expr-priority-mul) (expr-priority-cast))
              :add (mv (expr-priority-add) (expr-priority-mul))
              :sub (mv (expr-priority-add) (expr-priority-mul))
              :shl (mv (expr-priority-sh) (expr-priority-add))
              :shr (mv (expr-priority-sh) (expr-priority-add))
              :lt (mv (expr-priority-rel) (expr-priority-sh))
              :gt (mv (expr-priority-rel) (expr-priority-sh))
              :le (mv (expr-priority-rel) (expr-priority-sh))
              :ge (mv (expr-priority-rel) (expr-priority-sh))
              :eq (mv (expr-priority-eq) (expr-priority-rel))
              :ne (mv (expr-priority-eq) (expr-priority-rel))
              :bitand (mv (expr-priority-and) (expr-priority-eq))
              :bitxor (mv (expr-priority-xor) (expr-priority-and))
              :bitior (mv (expr-priority-ior) (expr-priority-xor))
              :logand (mv (expr-priority-logand) (expr-priority-ior))
              :logor (mv (expr-priority-logor) (expr-priority-logand))
              :asg (mv (expr-priority-unary) (expr-priority-asg))
              :asg-mul (mv (expr-priority-unary) (expr-priority-asg))
              :asg-div (mv (expr-priority-unary) (expr-priority-asg))
              :asg-rem (mv (expr-priority-unary) (expr-priority-asg))
              :asg-add (mv (expr-priority-unary) (expr-priority-asg))
              :asg-sub (mv (expr-priority-unary) (expr-priority-asg))
              :asg-shl (mv (expr-priority-unary) (expr-priority-asg))
              :asg-shr (mv (expr-priority-unary) (expr-priority-asg))
              :asg-and (mv (expr-priority-unary) (expr-priority-asg))
              :asg-xor (mv (expr-priority-unary) (expr-priority-asg))
              :asg-ior (mv (expr-priority-unary) (expr-priority-asg)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-zerop ((expr exprp))
  :returns (yes/no booleanp)
  :short "Check if an expression is zero."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are syntactically different expressions in C
     that evaluate to ``zero'' in a broad sense.
     For now we only include
     the octal integer constant @('0') without suffixes
     and with just one digit.
     So this operation is very limited in scope,
     but sufficient for its current usage (elsewhere)."))
  (b* (((unless (expr-case expr :const)) nil)
       (const (expr-const->const expr))
       ((unless (const-case const :int)) nil)
       ((iconst iconst) (const-int->unwrap const))
       ((when iconst.suffix?) nil)
       ((unless (dec/oct/hex-const-case iconst.core :oct)) nil)
       ((dec/oct/hex-const-oct doh) iconst.core)
       ((unless (= doh.leading-zeros 1)) nil)
       ((unless (= doh.value 0)) nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines declor->ident
  :short "Identifier of a declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "A declarator always contains an identifier at its core.
     This function returns it,
     together with a companion function that operates on direct declarators,
     which is mutually recursive with the one for declarators."))

  (define declor->ident ((declor declorp))
    :returns (ident identp)
    (dirdeclor->ident (declor->direct declor))
    :measure (declor-count declor))

  (define dirdeclor->ident ((dirdeclor dirdeclorp))
    :returns (ident identp)
    (dirdeclor-case
     dirdeclor
     :ident dirdeclor.unwrap
     :paren (declor->ident dirdeclor.unwrap)
     :array (dirdeclor->ident dirdeclor.decl)
     :array-static1 (dirdeclor->ident dirdeclor.decl)
     :array-static2 (dirdeclor->ident dirdeclor.decl)
     :array-star (dirdeclor->ident dirdeclor.decl)
     :function-params (dirdeclor->ident dirdeclor.decl)
     :function-names (dirdeclor->ident dirdeclor.decl))
    :measure (dirdeclor-count dirdeclor))

  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dirabsdeclor-decl?-nil-p ((dirabsdeclor dirabsdeclorp))
  :returns (yes/no booleanp)
  :short "Check if a direct abstract declarator has
          a @('decl?') component that is @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This excludes the base case(s) of direct abstract declarators.
     All the other recursive cases have a @('decl?') component."))
  (dirabsdeclor-case
   dirabsdeclor
   :dummy-base nil
   :paren nil
   :array (not dirabsdeclor.decl?)
   :array-static1 (not dirabsdeclor.decl?)
   :array-static2 (not dirabsdeclor.decl?)
   :array-star (not dirabsdeclor.decl?)
   :function (not dirabsdeclor.decl?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define combine-dirabsdeclor-into-dirabsdeclor ((dirabsdeclor1 dirabsdeclorp)
                                                (dirabsdeclor2 dirabsdeclorp))
  :guard (dirabsdeclor-decl?-nil-p dirabsdeclor2)
  :returns (dirabsdeclor dirabsdeclorp)
  :short "Combine a direct abstract declarator into another."
  :long
  (xdoc::topstring
   (xdoc::p
    "A direct abstract declarator has, except for the base case(s),
     a slot @('decl?') for another optional direct abstract declarator;
     this follows the structure of the grammar.
     The real base case is just one, a parenthesized abstract declarator;
     the other base case is a dummy one (see @(tsee dirabsdeclor)).")
   (xdoc::p
    "This function stores @('dirabsdeclor1')
     into the @('decl?') slot of @('dirabsdeclor2'),
     obtaining a new combined direct abstract declarator,
     provided that @('dirabsdeclor2') has that slot and contains @('nil'),
     as required by the guard."))
  (b* ((dirabsdeclor1 (dirabsdeclor-fix dirabsdeclor1)))
    (dirabsdeclor-case
     dirabsdeclor2
     :dummy-base (prog2$ (impossible) (irr-dirabsdeclor))
     :paren (prog2$ (impossible) (irr-dirabsdeclor))
     :array (change-dirabsdeclor-array dirabsdeclor2
                                       :decl? (dirabsdeclor-fix dirabsdeclor1))
     :array-static1 (change-dirabsdeclor-array-static1 dirabsdeclor2
                                                       :decl? dirabsdeclor1)
     :array-static2 (change-dirabsdeclor-array-static2 dirabsdeclor2
                                                       :decl? dirabsdeclor1)
     :array-star (change-dirabsdeclor-array-star dirabsdeclor2
                                                 :decl? dirabsdeclor1)
     :function (change-dirabsdeclor-function dirabsdeclor2
                                             :decl? dirabsdeclor1)))
  :guard-hints (("Goal" :in-theory (enable dirabsdeclor-decl?-nil-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-ident ((expr exprp))
  :returns (ident? ident-optionp)
  :short "Check if an expression is an identifier,
          returning the identifier if the check passes."
  (and (expr-case expr :ident)
       (expr-ident->ident expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-iconst ((expr exprp))
  :returns (iconst? iconst-optionp)
  :short "Check if an expression is an integer constant,
          returning the integer constant if the check passes."
  (b* (((unless (expr-case expr :const)) nil)
       (const (expr-const->const expr))
       ((unless (const-case const :int)))
       (iconst (const-int->unwrap const)))
    iconst)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-binary ((expr exprp))
  :returns (mv (yes/no booleanp) (op binopp) (arg1 exprp) (arg2 exprp))
  :short "Check if an expression is a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, return its operator and sub-expressions."))
  (if (expr-case expr :binary)
      (mv t
          (expr-binary->op expr)
          (expr-binary->arg1 expr)
          (expr-binary->arg2 expr))
    (mv nil (irr-binop) (irr-expr) (irr-expr)))
  :hooks (:fix)

  ///

  (defret expr-count-of-check-expr-binary-arg1
    (implies yes/no
             (< (expr-count arg1)
                (expr-count expr)))
    :rule-classes :linear)

  (defret expr-count-of-check-expr-binary-arg2
    (implies yes/no
             (< (expr-count arg2)
                (expr-count expr)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-mul ((expr exprp))
  :returns (mv (yes/no booleanp) (arg1 exprp) (arg2 exprp))
  :short "Check if an expression is a multiplication."
  :long
  (xdoc::topstring
   (xdoc::p
    "If it is, return its two sub-expressions."))
  (if (and (expr-case expr :binary)
           (binop-case (expr-binary->op expr) :mul))
      (mv t (expr-binary->arg1 expr) (expr-binary->arg2 expr))
    (mv nil (irr-expr) (irr-expr)))
  :hooks (:fix)

  ///

  (defret expr-count-of-check-expr-mul-arg1
    (implies yes/no
             (< (expr-count arg1)
                (expr-count expr)))
    :rule-classes :linear)

  (defret expr-count-of-check-expr-mul-arg2
    (implies yes/no
             (< (expr-count arg2)
                (expr-count expr)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-strunispec-no-members ((strunispec strunispecp))
  :returns (ident? ident-optionp)
  :short "Check if a structure or union specifier has no members,
          returning the name if the check passes."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the specifier is empty (i.e. has no members or name),
     we throw a hard error,
     because the specifier does not conform to the concrete syntax."))
  (b* (((strunispec strunispec) strunispec)
       ((when strunispec.members) nil)
       ((unless strunispec.name)
        (raise "Misusage error: empty structure or union specifier.")))
    strunispec.name)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-enumspec-no-list ((enumspec enumspecp))
  :returns (ident? ident-optionp)
  :short "Check if an enumeration union specifier has no enumerators,
          returning the name if the check passes."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the specifier is empty (i.e. has no enumerators or name),
     we throw a hard error,
     because the specifier does not conform to the concrete syntax."))
  (b* (((enumspec enumspec) enumspec)
       ((when enumspec.list) nil)
       ((unless enumspec.name)
        (raise "Misusage error: empty enumeration specifier.")))
    enumspec.name)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-decl-spec-list-all-typespec ((declspecs decl-spec-listp))
  :returns (mv (yes/no booleanp) (tyspecs type-spec-listp))
  :short "Check if all the declaration specifiers in a list
          are type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check succeeds,
     also return the list of type specifiers, in the same order."))
  (b* (((when (endp declspecs)) (mv t nil))
       (declspec (car declspecs))
       ((unless (decl-spec-case declspec :typespec)) (mv nil nil))
       ((mv yes/no tyspecs) (check-decl-spec-list-all-typespec (cdr declspecs))))
    (if yes/no
        (mv t (cons (decl-spec-typespec->spec declspec) tyspecs))
      (mv nil nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-decl-spec-list-all-typespec/stoclass ((declspecs decl-spec-listp))
  :returns (mv (yes/no booleanp)
               (tyspecs type-spec-listp)
               (stor-specs stor-spec-listp))
  :short "Check if all the declaration specifiers in a list
          are type specifiers or storage class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check succeeds,
     also return the lists of type specifiers and storage class specifiers,
     in the same order."))
  (b* (((when (endp declspecs)) (mv t nil nil))
       (declspec (car declspecs))
       ((when (decl-spec-case declspec :typespec))
        (b* (((mv yes/no tyspecs stor-specs)
              (check-decl-spec-list-all-typespec/stoclass (cdr declspecs))))
          (if yes/no
              (mv t
                  (cons (decl-spec-typespec->spec declspec) tyspecs)
                  stor-specs)
            (mv nil nil nil))))
       ((when (decl-spec-case declspec :stoclass))
        (b* (((mv yes/no tyspecs stor-specs)
              (check-decl-spec-list-all-typespec/stoclass (cdr declspecs))))
          (if yes/no
              (mv t
                  tyspecs
                  (cons (decl-spec-stoclass->spec declspec) stor-specs))
            (mv nil nil nil)))))
    (mv nil nil nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-spec/qual-list-all-typespec ((specquals spec/qual-listp))
  :returns (mv (yes/no booleanp) (tyspecs type-spec-listp))
  :short "Check if all the specifiers and qualifiers in a list
          are type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check succeeds,
     also return the list of type specifiers, in the same order."))
  (b* (((when (endp specquals)) (mv t nil))
       (specqual (car specquals))
       ((unless (spec/qual-case specqual :typespec)) (mv nil nil))
       ((mv yes/no tyspecs) (check-spec/qual-list-all-typespec (cdr specquals))))
    (if yes/no
        (mv t (cons (spec/qual-typespec->spec specqual) tyspecs))
      (mv nil nil)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-spec-list-to-type-spec-list ((declspecs decl-spec-listp))
  :returns (tyspecs type-spec-listp)
  :short "Extract the list of type specifiers
          from a list of declaration specifiers,
          preserving the order."
  (b* (((when (endp declspecs)) nil)
       (declspec (car declspecs)))
    (if (decl-spec-case declspec :typespec)
        (cons (decl-spec-typespec->spec declspec)
              (decl-spec-list-to-type-spec-list (cdr declspecs)))
      (decl-spec-list-to-type-spec-list (cdr declspecs))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-spec-list-to-stor-spec-list ((declspecs decl-spec-listp))
  :returns (stor-specs stor-spec-listp)
  :short "Extract the list of storage class specifiers
          from a list of declaration specifiers,
          preserving the order."
  (b* (((when (endp declspecs)) nil)
       (declspec (car declspecs)))
    (if (decl-spec-case declspec :stoclass)
        (cons (decl-spec-stoclass->spec declspec)
              (decl-spec-list-to-stor-spec-list (cdr declspecs)))
      (decl-spec-list-to-stor-spec-list (cdr declspecs))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define spec/qual-list-to-type-spec-list ((specquals spec/qual-listp))
  :returns (tyspecs type-spec-listp)
  :short "Extract the list of type specifiers
          from a list of type specifiers and qualifiers,
          preserving the order."
  (b* (((when (endp specquals)) nil)
       (specqual (car specquals)))
    (if (spec/qual-case specqual :typespec)
        (cons (spec/qual-typespec->spec specqual)
              (spec/qual-list-to-type-spec-list (cdr specquals)))
      (spec/qual-list-to-type-spec-list (cdr specquals))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-pre-inc/dec-ops ((ops inc/dec-op-listp) (expr exprp))
  :returns (new-expr exprp)
  :short "Apply a sequence of pre-increment and pre-decrement operators
          to an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first one in the list will be the outermost,
     and the last one in the list will be the innermost."))
  (b* (((when (endp ops)) (expr-fix expr))
       (op (car ops))
       (expr (apply-pre-inc/dec-ops (cdr ops) expr)))
    (inc/dec-op-case
     op
     :inc (make-expr-unary :op (unop-preinc) :arg expr)
     :dec (make-expr-unary :op (unop-predec) :arg expr)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define apply-post-inc/dec-ops ((expr exprp) (ops inc/dec-op-listp))
  :returns (new-expr exprp)
  :short "Apply a sequence of post-increment and post-decrement operators
          to an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first one in the list will be the innermost,
     and the last one in the list will be the outermost."))
  (b* (((when (endp ops)) (expr-fix expr))
       (op (car ops))
       (expr (inc/dec-op-case
              op
              :inc (make-expr-unary :op (unop-postinc) :arg expr)
              :dec (make-expr-unary :op (unop-postdec) :arg expr))))
    (apply-post-inc/dec-ops expr (cdr ops)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-to-asg-expr-list ((expr exprp))
  :returns (asg-exprs expr-listp)
  :short "Turn an expression into a list of assignment expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the grammar, an expression is defined as
     a comma-separated sequence of one or more assignment expressions.
     If there are no commas, then the expression is an assignment expression.")
   (xdoc::p
    "In abstract syntax,
     we flatten the expression according to the @(':comma')s.
     We do it for both sub-expressions of each @(':comma'),
     recursively, regardless of the nesting resulting from the parser."))
  (if (expr-case expr :comma)
      (append (expr-to-asg-expr-list (expr-comma->first expr))
              (expr-to-asg-expr-list (expr-comma->next expr)))
    (list (expr-fix expr)))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-paths ((tunits transunit-ensemblep))
  :returns (paths filepath-setp)
  :short "Set of file paths in a translation unit ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys of the map from file paths to translation units.")
   (xdoc::p
    "It is more concise, and more abstract,
     than extracting the map and then the keys.")
   (xdoc::p
    "Together with @(tsee transunit-at-path),
     it can be used as an API to inspect translation unit ensembles."))
  (omap::keys (transunit-ensemble->unwrap tunits))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-at-path ((path filepathp) (tunits transunit-ensemblep))
  :guard (set::in path (transunit-ensemble-paths tunits))
  :returns (tunit transunitp)
  :short "Translation unit at a certain path in a translation unit ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value associated to the key (path) in the map,
     which the guard requires to be in the translation unit ensemble.")
   (xdoc::p
    "It is more concise, and more abstract,
     than accessing the map and then looking up the path.")
   (xdoc::p
    "Together with @(tsee transunit-ensemble-paths),
     it can be used an as API to inspect a file set."))
  (transunit-fix
   (omap::lookup (filepath-fix path) (transunit-ensemble->unwrap tunits)))
  :guard-hints (("Goal" :in-theory (enable omap::assoc-to-in-of-keys
                                           transunit-ensemble-paths)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-permp ((tyspecs1 type-spec-listp)
                              (tyspecs2 type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of type specifiers are permutations."
  (b* (((when (endp tyspecs1)) (endp tyspecs2))
       (tyspec (car tyspecs1))
       ((unless (member-equal tyspec tyspecs2)) nil))
    (type-spec-list-permp (cdr tyspecs1) (remove1-equal tyspec tyspecs2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('char')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-char)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed char') or @('char signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-char)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-char)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-char))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned char') or @('char unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-char)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('short')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-short)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed short') or @('short signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-short)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-short)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-short))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('short int') or @('int short')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-short)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed short int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-short)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-short)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-short)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned short') or @('short unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-short)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned short int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-short)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('int')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('signed'),
          including the GCC underscore variations of @('signed')."
  (or (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-none))))
      (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-start))))
      (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-both)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed int') or @('int signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('unsigned')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-unsigned)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned int') or @('int unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('long')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long') or @('long signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long int') or @('int long')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long') or @('long unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('long long')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-long)
               (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long long') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long long int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long long') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('float')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('double')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-double)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long double') or @('double long')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-double)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('float _Complex') or @('_Complex float')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('double _Complex') or @('_Complex double')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-double)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-double-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long double _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-double)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-typedef-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('typedef')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-typedef)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-extern-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('extern')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-extern)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-static-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('static')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-static)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-threadloc-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('_Thread_local')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-threadloc)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-auto-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('auto')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-auto)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-register-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('register')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-register)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-extern-threadloc-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('extern _Thread_local') or @('_Thread_local extern')."
  (or (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-extern)
                   (stor-spec-threadloc)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-threadloc)
                   (stor-spec-extern))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-static-threadloc-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('static _Thread_local') or @('_Thread_local static')."
  (or (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-static)
                   (stor-spec-threadloc)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-threadloc)
                   (stor-spec-static))))
  :hooks (:fix))

; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")

(include-book "../language/abstract-syntax")

(include-book "kestrel/fty/string-option" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mapping-from-language-definition
  :parents (syntax-for-tools)
  :short "Mapping from the language definition to the tool-oriented syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse mapping of "
    (xdoc::seetopic
     "mapping-to-language-definition"
     "the one from the tool-oriented syntax to the language definition")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-ident ((ident c::identp))
  :returns (ident1 identp)
  :short "Map an identifier in the language definition
          to an identifier in the syntax for tools."
  (ident (c::ident->name ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-iconst ((iconst c::iconstp))
  :returns (iconst iconstp)
  :short "Map an integer constant in the language definition
          to an integer constant in the syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "The AST of the language definition may use a decimal base for 0.
     Thus, we need to map that case to an octal constant."))
  (b* (((c::iconst iconst) iconst)
       (suffix? (if iconst.unsignedp
                    (c::iconst-length-case
                     iconst.length
                     :none (isuffix-u (usuffix-upcase-u))
                     :long (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                            :length (lsuffix-upcase-l))
                     :llong (make-isuffix-ul :unsigned (usuffix-upcase-u)
                                             :length (lsuffix-upcase-ll)))
                  (c::iconst-length-case
                   iconst.length
                   :none nil
                   :long (isuffix-l (lsuffix-upcase-l))
                   :llong (isuffix-l (lsuffix-upcase-l))))))
    (c::iconst-base-case
     iconst.base
     :dec (if (= iconst.value 0)
              (make-iconst
               :core (make-dec/oct/hex-const-oct
                      :leading-zeros 1
                      :value 0)
               :suffix? suffix?
               :info nil)
            (make-iconst
             :core (dec/oct/hex-const-dec iconst.value)
             :suffix? suffix?
             :info nil))
     :oct (make-iconst
           :core (make-dec/oct/hex-const-oct
                  :leading-zeros 1
                  :value iconst.value)
           :suffix? suffix?
           :info nil)
     :hex (make-iconst
           :core (make-dec/oct/hex-const-hex
                  :prefix (hprefix-locase-0x)
                  :digits (str::nat-to-hex-chars iconst.value))
           :suffix? suffix?
           :info nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-const ((const c::constp))
  :returns (const1 constp)
  :short "Map a constant in the language definition
          to a constant in the syntax for tools."
  (c::const-case
   const
   :int (const-int (ildm-iconst (c::const-int->get const)))
   :otherwise (prog2$ (raise "Unsupported non-integer constant ~x0."
                             (c::const-fix const))
                      (irr-const)))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-tyspecseq ((tyspecs c::tyspecseqp))
  :returns (tyspecs1 type-spec-listp)
  :short "Map a type specifier sequence in the language definition
          to a list of type specifiers in the syntax for tools."
  (c::tyspecseq-case
   tyspecs
   :void (list (type-spec-void))
   :char (list (type-spec-char))
   :schar (list (type-spec-signed (keyword-uscores-none))
                (type-spec-char))
   :uchar (list (type-spec-unsigned)
                (type-spec-char))
   :sshort (if tyspecs.signed
               (if tyspecs.int
                   (list (type-spec-short)
                         (type-spec-signed (keyword-uscores-none))
                         (type-spec-int))
                 (list (type-spec-short)
                       (type-spec-signed (keyword-uscores-none))))
             (if tyspecs.int
                 (list (type-spec-short)
                       (type-spec-int))
               (list (type-spec-short))))
   :ushort (if tyspecs.int
               (list (type-spec-unsigned)
                     (type-spec-short)
                     (type-spec-int))
             (list (type-spec-unsigned)
                   (type-spec-short)))
   :sint (if tyspecs.signed
             (if tyspecs.int
                 (list (type-spec-signed (keyword-uscores-none))
                       (type-spec-int))
               (list (type-spec-signed (keyword-uscores-none))))
           (if tyspecs.int
               (list (type-spec-int))
             (impossible)))
   :uint (if tyspecs.int
             (list (type-spec-unsigned)
                   (type-spec-int))
           (list (type-spec-unsigned)))
   :slong (if tyspecs.signed
              (if tyspecs.int
                  (list (type-spec-long)
                        (type-spec-signed (keyword-uscores-none))
                        (type-spec-int))
                (list (type-spec-long)
                      (type-spec-signed (keyword-uscores-none))))
            (if tyspecs.int
                (list (type-spec-long)
                      (type-spec-int))
              (list (type-spec-long))))
   :ulong (if tyspecs.int
              (list (type-spec-unsigned)
                    (type-spec-long)
                    (type-spec-int))
            (list (type-spec-unsigned)
                  (type-spec-long)))
   :sllong (if tyspecs.signed
               (if tyspecs.int
                   (list (type-spec-long)
                         (type-spec-long)
                         (type-spec-signed (keyword-uscores-none))
                         (type-spec-int))
                 (list (type-spec-long)
                       (type-spec-long)
                       (type-spec-signed (keyword-uscores-none))))
             (if tyspecs.int
                 (list (type-spec-long)
                       (type-spec-long)
                       (type-spec-int))
               (list (type-spec-long)
                     (type-spec-long))))
   :ullong (if tyspecs.int
               (list (type-spec-unsigned)
                     (type-spec-long)
                     (type-spec-long)
                     (type-spec-int))
             (list (type-spec-unsigned)
                   (type-spec-long)
                   (type-spec-long)))
   :bool (list (type-spec-bool))
   :float (if tyspecs.complex
              (list (type-spec-float)
                    (type-spec-complex))
            (list (type-spec-float)))
   :double (if tyspecs.complex
               (list (type-spec-double)
                     (type-spec-complex))
             (list (type-spec-double)))
   :ldouble (if tyspecs.complex
                (list (type-spec-long)
                      (type-spec-double)
                      (type-spec-complex))
              (list (type-spec-long)
                    (type-spec-double)))
   :struct (list (type-spec-struct
                  (make-struni-spec :attribs nil
                                    :name? (ildm-ident tyspecs.tag)
                                    :members nil)))
   :union (list (type-spec-union
                 (make-struni-spec :attribs nil
                                   :name? (ildm-ident tyspecs.tag)
                                   :members nil)))
   :enum (list (type-spec-enum
                (make-enum-spec :name? (ildm-ident tyspecs.tag)
                                :enumers nil
                                :final-comma nil)))
   :typedef (list (type-spec-typedef (ildm-ident tyspecs.name))))
  :guard-hints (("Goal"
                 :use (:instance c::tyspecseq-sint-requirements (x tyspecs))
                 :in-theory (disable c::tyspecseq-sint-requirements))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-scspecseq ((scspecs c::scspecseqp))
  :returns (scspecs1 stor-spec-listp)
  :short "Map a storage class specifier sequence in the language definition
          to a list of storage class specifiers in the syntax for tools."
  (c::scspecseq-case
   scspecs
   :none nil
   :extern (list (stor-spec-extern))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-obj-declor ((declor c::obj-declorp))
  :returns (declor1 declorp)
  :short "Map an object declarator in the language definition
          to a declarator in the syntax for tools."
  (c::obj-declor-case
   declor
   :ident (make-declor
           :pointers nil
           :direct (dirdeclor-ident (ildm-ident declor.get)))
   :pointer (b* (((declor inner-declor) (ildm-obj-declor declor.decl)))
              (make-declor
               :pointers (cons nil inner-declor.pointers)
               :direct inner-declor.direct))
   :array (b* (((declor inner-declor) (ildm-obj-declor declor.decl)))
            (make-declor
             :pointers nil
             :direct (make-dirdeclor-array
                      :declor (declor-to-dirdeclor inner-declor)
                      :qualspecs nil
                      :size? (if declor.size
                                 (make-expr-const
                                  :const (const-int (ildm-iconst declor.size))
                                  :info nil)
                               nil)))))
  :measure (c::obj-declor-count declor)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-obj-adeclor ((adeclor c::obj-adeclorp))
  :returns (adeclor1 absdeclorp)
  :short "Map an abstract object declarator in the language definition
          to an abstract declarator in the syntax for tools."
  (c::obj-adeclor-case
   adeclor
   :none (make-absdeclor
          :pointers nil
          :direct? nil)
   :pointer (b* (((absdeclor inner-adeclor) (ildm-obj-adeclor adeclor.decl)))
              (make-absdeclor
               :pointers (cons nil inner-adeclor.pointers)
               :direct? inner-adeclor.direct?))
   :array (b* (((absdeclor inner-adeclor) (ildm-obj-adeclor adeclor.decl)))
            (make-absdeclor
             :pointers nil
             :direct? (make-dirabsdeclor-array
                       :declor? (absdeclor-to-dirabsdeclor? inner-adeclor)
                       :qualspecs nil
                       :size? (if adeclor.size
                                  (make-expr-const
                                   :const (const-int (ildm-iconst adeclor.size))
                                   :info nil)
                                nil)))))
  :measure (c::obj-adeclor-count adeclor)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-tyname ((tyname c::tynamep))
  :returns (tyname1 tynamep)
  :short "Map a type name in the language definition
          to a type name in the syntax for tools."
  (b* (((c::tyname tyname) tyname)
       (tyspecs (ildm-tyspecseq tyname.tyspec))
       (specquals (spec/qual-typespec-list tyspecs))
       (declor? (ildm-obj-adeclor tyname.declor)))
    (make-tyname :specquals specquals
                 :declor? declor?
                 :info nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-unop ((unop c::unopp))
  :returns (unop1 unopp)
  :short "Map a unary operator in the language definition
          to a unary operator in the syntax for tools."
  (c::unop-case unop
                :address (unop-address)
                :indir (unop-indir)
                :plus (unop-plus)
                :minus (unop-minus)
                :bitnot (unop-bitnot)
                :lognot (unop-lognot)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-binop ((binop c::binopp))
  :returns (binop1 binopp)
  :short "Map a binary operator in the language definition
          to a binary operator in the syntax for tools."
  (c::binop-case binop
                 :mul (binop-mul)
                 :div (binop-div)
                 :rem (binop-rem)
                 :add (binop-add)
                 :sub (binop-sub)
                 :shl (binop-shl)
                 :shr (binop-shr)
                 :lt (binop-lt)
                 :gt (binop-gt)
                 :le (binop-le)
                 :ge (binop-ge)
                 :eq (binop-eq)
                 :ne (binop-ne)
                 :bitand (binop-bitand)
                 :bitxor (binop-bitxor)
                 :bitior (binop-bitior)
                 :logand (binop-logand)
                 :logor (binop-logor)
                 :asg (binop-asg)
                 :asg-mul (binop-asg-mul)
                 :asg-div (binop-asg-div)
                 :asg-rem (binop-asg-rem)
                 :asg-add (binop-asg-add)
                 :asg-sub (binop-asg-sub)
                 :asg-shl (binop-asg-shl)
                 :asg-shr (binop-asg-shr)
                 :asg-and (binop-asg-and)
                 :asg-xor (binop-asg-xor)
                 :asg-ior (binop-asg-ior)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ildm-exprs
  :short "Map expressions in the language definition
          to expressions in the syntax for tools."

  (define ildm-expr ((expr c::exprp))
    :returns (expr1 exprp)
    :parents (mapping-from-language-definition ildm-exprs)
    :short "Map an expression in the language definition
            to an expression in the syntax for tools."
    (c::expr-case
     expr
     :ident (make-expr-ident :ident (ildm-ident expr.get)
                             :info nil)
     :const (make-expr-const :const (ildm-const expr.get)
                             :info nil)
     :arrsub (make-expr-arrsub :arg1 (ildm-expr expr.arr)
                               :arg2 (ildm-expr expr.sub))
     :call (make-expr-funcall :fun (make-expr-ident :ident (ildm-ident expr.fun)
                                                    :info nil)
                              :args (ildm-expr-list expr.args))
     :member (make-expr-member :arg (ildm-expr expr.target)
                               :name (ildm-ident expr.name))
     :memberp (make-expr-memberp :arg (ildm-expr expr.target)
                                 :name (ildm-ident expr.name))
     :postinc (make-expr-unary :op (unop-postinc)
                               :arg (ildm-expr expr.arg)
                               :info nil)
     :postdec (make-expr-unary :op (unop-postdec)
                               :arg (ildm-expr expr.arg)
                               :info nil)
     :preinc (make-expr-unary :op (unop-preinc)
                              :arg (ildm-expr expr.arg)
                              :info nil)
     :predec (make-expr-unary :op (unop-predec)
                              :arg (ildm-expr expr.arg)
                              :info nil)
     :unary (make-expr-unary :op (ildm-unop expr.op)
                             :arg (ildm-expr expr.arg)
                             :info nil)
     :cast (make-expr-cast :type (ildm-tyname expr.type)
                           :arg (ildm-expr expr.arg))
     :binary (make-expr-binary :op (ildm-binop expr.op)
                               :arg1 (ildm-expr expr.arg1)
                               :arg2 (ildm-expr expr.arg2))
     :cond (make-expr-cond :test (ildm-expr expr.test)
                           :then (ildm-expr expr.then)
                           :else (ildm-expr expr.else)))
    :measure (c::expr-count expr))

  (define ildm-expr-list ((exprs c::expr-listp))
    :returns (exprs1 expr-listp)
    :parents (mapping-from-language-definition ildm-exprs)
    :short "Map a list of expressions in the language definition
            to a list of expressions in the syntax for tools."
    (cond ((endp exprs) nil)
          (t (cons (ildm-expr (car exprs))
                   (ildm-expr-list (cdr exprs)))))
    :measure (c::expr-list-count exprs))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual ildm-exprs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-expr-option ((expr? c::expr-optionp))
  :returns (expr?1 expr-optionp)
  :short "Map an optional expression in the language definition
          to an optional expression in the syntax for tools."
  (c::expr-option-case expr?
                       :some (ildm-expr expr?.val)
                       :none nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-struct-declon ((sdeclon c::struct-declonp))
  :returns (sdeclon1 struct-declonp)
  :short "Map a structure declaration in the language definition
          to a structure declaration in the syntax for tools."
  (b* (((c::struct-declon sdeclon) sdeclon)
       (tyspecs (ildm-tyspecseq sdeclon.tyspec))
       (specquals (spec/qual-typespec-list tyspecs))
       (declor (ildm-obj-declor sdeclon.declor))
       (sdeclor (make-struct-declor :declor? declor :expr? nil)))
    (make-struct-declon-member :extension nil
                               :specquals specquals
                               :declors (list sdeclor)
                               :attribs nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-struct-declon-list ((sdeclons c::struct-declon-listp))
  :returns (sdeclons struct-declon-listp)
  :short "Map a list of structure declarations in the language definition
          to a list of structure declarations in the syntax for tools."
  (cond ((endp sdeclons) nil)
        (t (cons (ildm-struct-declon (car sdeclons))
                 (ildm-struct-declon-list (cdr sdeclons))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-enumer-list ((enumers c::ident-listp))
  :returns (enumers1 enumer-listp)
  :short "Map a list of enumerators in the language definition
          to a list of enumerators in the syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the abstract syntax of the language definition,
     enumerators are just identifiers."))
  (cond ((endp enumers) nil)
        (t (cons (make-enumer :name (ildm-ident (car enumers)) :value? nil)
                 (ildm-enumer-list (cdr enumers)))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-tag-declon ((declon c::tag-declonp))
  :returns (declon1 declonp)
  :short "Map a tag declaration in the language definition
          to a declaration in the syntax for tools."
  (b* ((tyspec
        (c::tag-declon-case
         declon
         :struct (b* ((strunispec
                       (make-struni-spec
                        :attribs nil
                        :name? (ildm-ident declon.tag)
                        :members (ildm-struct-declon-list declon.members))))
                   (type-spec-struct strunispec))
         :union (b* ((strunispec
                      (make-struni-spec
                       :attribs nil
                       :name? (ildm-ident declon.tag)
                       :members (ildm-struct-declon-list declon.members))))
                  (type-spec-union strunispec))
         :enum (b* ((enumspec (make-enum-spec
                               :name? (ildm-ident declon.tag)
                               :enumers (ildm-enumer-list declon.enumerators)
                               :final-comma nil)))
                 (type-spec-enum enumspec))))
       (declspec (decl-spec-typespec tyspec)))
    (make-declon-declon :extension nil
                        :specs (list declspec)
                        :declors nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-param-declon ((pdeclon c::param-declonp))
  :returns (pdeclon1 param-declonp)
  :short "Map a parameter declaration in the language definition
          to a parameter declaration in th syntax for tools."
  (b* (((c::param-declon pdeclon) pdeclon)
       (tyspecs (ildm-tyspecseq pdeclon.tyspec))
       (declspecs (decl-spec-typespec-list tyspecs)))
    (make-param-declon :specs declspecs
                       :declor (param-declor-none)
                       :attribs nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-param-declon-list ((pdeclons c::param-declon-listp))
  :returns (pdeclons1 param-declon-listp)
  :short "Map a list of parameter declarations in the language definition
          to a list of parameter declarations in the syntax for tools."
  (cond ((endp pdeclons) nil)
        (t (cons (ildm-param-declon (car pdeclons))
                 (ildm-param-declon-list (cdr pdeclons))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-fun-declor ((declor c::fun-declorp))
  :returns (declor declorp)
  :short "Map a function declarator in the language definition
          to a declarator in the syntax for tools."
  (c::fun-declor-case
   declor
   :base (make-declor
          :pointers nil
          :direct (if declor.params
                      (make-dirdeclor-function-params
                       :declor (dirdeclor-ident (ildm-ident declor.name))
                       :params (ildm-param-declon-list declor.params)
                       :ellipsis nil)
                    (make-dirdeclor-function-names
                     :declor (dirdeclor-ident (ildm-ident declor.name))
                     :names nil)))
   :pointer (b* (((declor declor1) (ildm-fun-declor declor.decl)))
              (make-declor :pointers (cons nil declor1.pointers)
                           :direct declor1.direct)))
  :measure (c::fun-declor-count declor)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-fun-adeclor ((adeclor c::fun-adeclorp))
  :returns (adeclor absdeclorp)
  :short "Map an abstract function declarator in the language definition
          to an abstract declarator in the syntax for tools."
  (c::fun-adeclor-case
   adeclor
   :base (make-absdeclor
          :pointers nil
          :direct? (make-dirabsdeclor-function
                    :declor? nil
                    :params (ildm-param-declon-list adeclor.params)
                    :ellipsis nil))
   :pointer (b* (((absdeclor adeclor1) (ildm-fun-adeclor adeclor.decl)))
              (make-absdeclor :pointers (cons nil adeclor1.pointers)
                              :direct? adeclor1.direct?)))
  :measure (c::fun-adeclor-count adeclor)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-fun-declon ((declon c::fun-declonp))
  :returns (declon1 declonp)
  :short "Map a function declaration in the language definition
          to a declaration in the syntax for tools."
  (b* (((c::fun-declon declon) declon)
       (tyspecs (ildm-tyspecseq declon.tyspec))
       (declspecs (decl-spec-typespec-list tyspecs))
       (declor (ildm-fun-declor declon.declor))
       (ideclor (make-init-declor :declor declor
                                  :asm? nil
                                  :attribs nil
                                  :initer? nil
                                  :info nil)))
    (make-declon-declon :extension nil
                        :specs declspecs
                        :declors (list ideclor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-desiniter-list ((exprs c::expr-listp))
  :returns (desiniters desiniter-listp)
  :short "Map a list of initializers with optional designations
          in the language definition
          to a list of initializers with optional designations
          in the syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the abstract syntax of the language definition,
     initializers with optional designations
     are represented just as expressions."))
  (cond ((endp exprs) nil)
        (t (cons (make-desiniter
                  :designors nil
                  :initer (initer-single (ildm-expr (car exprs))))
                 (ildm-desiniter-list (cdr exprs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-initer ((initer c::initerp))
  :returns (initer1 initerp)
  :short "Map an initializer in the language definition
          to an initializer in the syntax for tools."
  (c::initer-case
   initer
   :single (initer-single (ildm-expr initer.get))
   :list (make-initer-list
          :elems (ildm-desiniter-list initer.get)
          :final-comma nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-initer-option ((initer? c::initer-optionp))
  :returns (initer?1 initer-optionp)
  :short "Map an optional initializer in the language definition
          to an optional initializer in the syntax for tools."
  (c::initer-option-case initer?
                         :some (ildm-initer initer?.val)
                         :none nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-obj-declon ((declon c::obj-declonp))
  :returns (declon1 declonp)
  :short "Map an object declaration in the language definition
          to a declaration in the syntax for tools."
  (b* (((c::obj-declon declon) declon)
       (scspecs (ildm-scspecseq declon.scspec))
       (tyspecs (ildm-tyspecseq declon.tyspec))
       (declspecs (append (decl-spec-stoclass-list scspecs)
                          (decl-spec-typespec-list tyspecs)))
       (declor (ildm-obj-declor declon.declor))
       (initer? (ildm-initer-option declon.init?))
       (ideclor (make-init-declor
                 :declor declor
                 :asm? nil
                 :attribs nil
                 :initer? initer?
                 :info nil)))
    (make-declon-declon :extension nil
                        :specs declspecs
                        :declors (list ideclor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-label ((label c::labelp))
  :returns (label1 labelp)
  :short "Map a label in the language definition
          to a label in the syntax for tools."
  (c::label-case
   label
   :name (make-label-name :name (ildm-ident label.get)
                          :attribs nil)
   :cas (make-label-casexpr :expr (const-expr (ildm-expr label.get))
                            :range? nil)
   :default (label-default)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines ildm-stmts
  :short "Map statements in the language definition
          to statements in the syntax for tools."

  (define ildm-stmt ((stmt c::stmtp))
    :returns (stmt1 stmtp)
    :parents (mapping-from-language-definition ildm-stmts)
    :short "Map a statement in the language definition
            to a statement in the syntax for tools."
    (c::stmt-case
     stmt
     :labeled (make-stmt-labeled :label (ildm-label stmt.label)
                                 :stmt (ildm-stmt stmt.body))
     :compound (stmt-compound
                (make-comp-stmt :labels nil
                                :items (ildm-block-item-list stmt.items)))
     :expr (make-stmt-expr :expr? (ildm-expr stmt.get)
                           :info nil)
     :null (make-stmt-expr :expr? nil
                           :info nil)
     :if (make-stmt-if :test (ildm-expr stmt.test)
                       :then (ildm-stmt stmt.then))
     :ifelse (make-stmt-ifelse :test (ildm-expr stmt.test)
                               :then (ildm-stmt stmt.then)
                               :else (ildm-stmt stmt.else))
     :switch (make-stmt-switch :target (ildm-expr stmt.ctrl)
                               :body (ildm-stmt stmt.body))
     :while (make-stmt-while :test (ildm-expr stmt.test)
                             :body (ildm-stmt stmt.body))
     :dowhile (make-stmt-dowhile :body (ildm-stmt stmt.body)
                                 :test (ildm-expr stmt.test))
     :for (make-stmt-for-expr :init (ildm-expr-option stmt.init)
                              :test (ildm-expr-option stmt.test)
                              :next (ildm-expr-option stmt.next)
                              :body (ildm-stmt stmt.body))
     :goto (stmt-goto (ildm-ident stmt.target))
     :continue (stmt-continue)
     :break (stmt-break)
     :return (make-stmt-return :expr? (ildm-expr-option stmt.value)
                               :info nil))
    :measure (c::stmt-count stmt))

  (define ildm-block-item ((item c::block-itemp))
    :returns (item1 block-itemp)
    :parents (mapping-from-language-definition ildm-stmts)
    :short "Map a block item in the language definition
            to a block item in the syntax for tools."
    (c::block-item-case
     item
     :declon (make-block-item-declon
              :declon (ildm-obj-declon item.get)
              :info nil)
     :stmt (make-block-item-stmt
            :stmt (ildm-stmt item.get)
            :info nil))
    :measure (c::block-item-count item))

  (define ildm-block-item-list ((items c::block-item-listp))
    :returns (items1 block-item-listp)
    :parents (mapping-from-language-definition ildm-stmts)
    :short "Map a list of block items in the language definition
            to a list of block items in the syntax for tools."
    (cond ((endp items) nil)
          (t (cons (ildm-block-item (car items))
                   (ildm-block-item-list (cdr items)))))
    :measure (c::block-item-list-count items))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual ildm-stmts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-fundef ((fundef c::fundefp))
  :returns (fundef1 fundefp)
  :short "Map a function definition in the language definition
          to a function definition in the syntax for tools."
  (b* (((c::fundef fundef) fundef)
       (tyspecs (ildm-tyspecseq fundef.tyspec))
       (declspecs (decl-spec-typespec-list tyspecs))
       (declor (ildm-fun-declor fundef.declor))
       (items (ildm-block-item-list fundef.body)))
    (make-fundef :extension nil
                 :specs declspecs
                 :declor declor
                 :asm? nil
                 :attribs nil
                 :declons nil
                 :body (make-comp-stmt :labels nil :items items)
                 :info nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-ext-declon ((edeclon c::ext-declonp))
  :returns (edeclon1 ext-declonp)
  :short "Map an external declaration in the language definition
          to an external declaration in the syntax for tools."
  (c::ext-declon-case
   edeclon
   :fundef (ext-declon-fundef (ildm-fundef edeclon.get))
   :fun-declon (ext-declon-declon (ildm-fun-declon edeclon.get))
   :obj-declon (ext-declon-declon (ildm-obj-declon edeclon.get))
   :tag-declon (ext-declon-declon (ildm-tag-declon edeclon.get))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-ext-declon-list ((edeclons c::ext-declon-listp))
  :returns (edeclons1 ext-declon-listp)
  :short "Map a list of external declarations in the language definition
          to a list of external declarations in the syntax for tools."
  (cond ((endp edeclons) nil)
        (t (cons (ildm-ext-declon (car edeclons))
                 (ildm-ext-declon-list (cdr edeclons))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chars-to-q-chars ((chars character-listp))
  :returns (qchars q-char-listp)
  :short "Map a list of ACL2 characters to a list of @(tsee q-chars) values."
  (cond ((endp chars) nil)
        (t (cons (q-char (char-code (car chars)))
                 (chars-to-q-chars (cdr chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-q-header-name ((str stringp))
  :returns (hname header-namep)
  :short "Map an ACL2 string to a header name with double quotes."
  (header-name-quotes (chars-to-q-chars (str::explode str))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-transunit ((file-name string-optionp) (tunit c::transunitp))
  :returns (tunit1 transunitp)
  :short "Map a translation unit in the language definition
          to a translation unit in the syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "The optional file name passed as input represents (if present)
     an implicit @('#include') in the translation unit
     for a header with that name, to which we add the @('.h') extension.
     See @(tsee ildm-transunit-ensemble)."))
  (make-transunit
   :comment nil
   :includes (and file-name
                  (list (string-to-q-header-name (str::cat file-name ".h"))))
   :declons (ildm-ext-declon-list (c::transunit->declons tunit))
   :info nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ildm-transunit-ensemble ((file-name stringp)
                                 (tunits c::transunit-ensemblep))
  :returns (tunits1 transunit-ensemblep)
  :short "Map a translation unit ensemble in the language definition
          to a translation unit ensemble in the syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string input represents the name of the file or files,
     without extension."))
  (b* (((c::transunit-ensemble tunits) tunits)
       (file-name (str-fix file-name)))
    (make-transunit-ensemble
     :units (b* ((map-with-source-file
                  (omap::update (filepath (str::cat file-name ".c"))
                                (ildm-transunit (and tunits.dot-h
                                                     file-name)
                                                tunits.dot-c)
                                nil))
                 (map-with-all-files
                  (if tunits.dot-h
                      (omap::update (filepath (str::cat file-name ".h"))
                                    (ildm-transunit nil tunits.dot-h)
                                    map-with-source-file)
                    map-with-source-file)))
              map-with-all-files)
     :info nil)))

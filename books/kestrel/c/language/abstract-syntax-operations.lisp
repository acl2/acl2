; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")

(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-operations
  :parents (abstract-syntax)
  :short "Operations on the C abstract syntax."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unop-nonpointerp ((op unopp))
  :returns (yes/no booleanp)
  :short "Check if a unary operator does not involve pointers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are unary plus, unary minus, and bitwise/logical negation/complement.
     The other two, address and indirection, involve pointers."))
  (and (member-eq (unop-kind op) '(:plus :minus :bitnot :lognot)) t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-strictp ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is strict."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except logical conjunction and disjunction
     are strict."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :asg
                        :asg-mul
                        :asg-div
                        :asg-rem
                        :asg-add
                        :asg-sub
                        :asg-shl
                        :asg-shr
                        :asg-and
                        :asg-xor
                        :asg-ior))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-purep ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is pure."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the binary operators except (simple and compound) assignments
     are pure."))
  (and (member-eq (binop-kind op)
                  (list :mul
                        :div
                        :rem
                        :add
                        :sub
                        :shl
                        :shr
                        :lt
                        :gt
                        :le
                        :ge
                        :eq
                        :ne
                        :bitand
                        :bitxor
                        :bitior
                        :logand
                        :logor))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj-declor-to-ident+adeclor ((declor obj-declorp))
  :returns (mv (id identp) (adeclor obj-adeclorp))
  :short "Decompose an object declarator into
          an identifier and an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This abstracts an object declarator to an abstract object declarator,
     by removing the identifier and also returning it.
     See @(tsee obj-adeclor)."))
  (obj-declor-case
   declor
   :ident (mv declor.get (obj-adeclor-none))
   :pointer (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.decl)))
              (mv id (make-obj-adeclor-pointer :decl sub)))
   :array (b* (((mv id sub) (obj-declor-to-ident+adeclor declor.decl)))
            (mv id (make-obj-adeclor-array :decl sub :size declor.size))))
  :measure (obj-declor-count declor)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+adeclor-to-obj-declor ((id identp) (adeclor obj-adeclorp))
  :returns (declor obj-declorp)
  :short "Compose an identifier and an abstract object declarator
          into an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee obj-declor-to-ident+adeclor)."))
  (obj-adeclor-case
   adeclor
   :none (obj-declor-ident id)
   :pointer (make-obj-declor-pointer
             :decl (ident+adeclor-to-obj-declor id adeclor.decl))
   :array (make-obj-declor-array
           :decl (ident+adeclor-to-obj-declor id adeclor.decl)
           :size adeclor.size))
  :measure (obj-adeclor-count adeclor)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule ident+adeclor-to-obj-declor-of-obj-declor-to-ident+adeclor
    (b* (((mv id adeclor) (obj-declor-to-ident+adeclor declor)))
      (equal (ident+adeclor-to-obj-declor id adeclor)
             (obj-declor-fix declor)))
    :induct t
    :enable obj-declor-to-ident+adeclor)

  (defrule obj-declor-to-ident+adeclor-of-ident+adeclor-to-obj-declor
    (equal (obj-declor-to-ident+adeclor
            (ident+adeclor-to-obj-declor id adeclor))
           (mv (ident-fix id) (obj-adeclor-fix adeclor)))
    :induct t
    :enable obj-declor-to-ident+adeclor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-declor-to-ident+adeclor ((declor fun-declorp))
  :returns (mv (id identp) (adeclor fun-adeclorp))
  :short "Decompose a function declarator into
          an identifier and an abstract function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This abstracts a function declarator to an abstract function declarator,
     by removing the identifier and also returning it.
     See @(tsee fun-adeclor)."))
  (fun-declor-case
   declor
   :base (mv declor.name (fun-adeclor-base declor.params))
   :pointer (b* (((mv id sub) (fun-declor-to-ident+adeclor declor.decl)))
              (mv id (fun-adeclor-pointer sub))))
  :measure (fun-declor-count declor)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+adeclor-to-fun-declor ((id identp) (adeclor fun-adeclorp))
  :returns (declor fun-declorp)
  :short "Compose an identifier and an abstract function declarator
          into a function declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee fun-declor-to-ident+adeclor)."))
  (fun-adeclor-case
   adeclor
   :base (make-fun-declor-base :name id :params adeclor.params)
   :pointer (make-fun-declor-pointer
             :decl (ident+adeclor-to-fun-declor id adeclor.decl)))
  :measure (fun-adeclor-count adeclor)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :verify-guards :after-returns
  :hooks (:fix)
  ///

  (defrule ident+adeclor-to-fun-declor-of-fun-declor-to-ident+adeclor
    (b* (((mv id adeclor) (fun-declor-to-ident+adeclor declor)))
      (equal (ident+adeclor-to-fun-declor id adeclor)
             (fun-declor-fix declor)))
    :induct t
    :enable fun-declor-to-ident+adeclor)

  (defrule fun-declor-to-ident+adeclor-of-ident+adeclor-to-fun-declor
    (equal (fun-declor-to-ident+adeclor
            (ident+adeclor-to-fun-declor id adeclor))
           (mv (ident-fix id) (fun-adeclor-fix adeclor)))
    :induct t
    :enable fun-declor-to-ident+adeclor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-adeclor-to-params+declor ((declor fun-adeclorp))
  :returns (mv (params param-declon-listp)
               (declor obj-adeclorp))
  :short "Decompose an abstract function declarator into
          a list of parameter declarations and an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The inverse of this is not well-defined
     for every abstract object declarator,
     because the latter may include array declarators,
     which are not allowed in function declarators.
     We could define the inverse on object declarators
     that are restricted not to use array declarators;
     but we do not need the inverse for now."))
  (fun-adeclor-case
   declor
   :base (mv declor.params (obj-adeclor-none))
   :pointer (b* (((mv params sub) (fun-adeclor-to-params+declor declor.decl)))
              (mv params (make-obj-adeclor-pointer :decl sub))))
  :measure (fun-adeclor-count declor)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspec+declor-to-ident+tyname ((tyspec tyspecseqp)
                                       (declor obj-declorp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Turn a type specifier sequence and an object declarator
          into an identifier and a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the declarator into an identifier and an abstract declarator,
     and we form a type name with the latter and the type specifier sequence.")
   (xdoc::p
    "The name of this ACL2 function does not mention @('obj') explicitly,
     but the fact that it deals with object declarators
     is implicit in the fact that it returns an identifier and a type name.")
   (xdoc::p
    "In essence, we turn (the constituents of) an object declaration
     into its name and type, which are somewhat mixed in the C syntax."))
  (b* (((mv id adeclor) (obj-declor-to-ident+adeclor declor)))
    (mv id (make-tyname :tyspec tyspec :declor adeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident+tyname-to-tyspec+declor ((id identp) (tyname tynamep))
  :returns (mv (tyspec tyspecseqp) (declor obj-declorp))
  :short "Turn an identifier and a type name
          into a type specifier sequence and an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the type name into
     a type specifier sequence and an abstract object declarator,
     and we compose the latter with the identifier into an object declarator.")
   (xdoc::p
    "Given an identifier and a type (name),
     this function provides the constituents for declaring it.")
   (xdoc::p
    "This is the inverse of @(tsee tyspec+declor-to-ident+tyname)."))
  (b* (((tyname tyname) tyname))
    (mv tyname.tyspec (ident+adeclor-to-obj-declor id tyname.declor)))
  :hooks (:fix)
  ///

  (defrule ident+tyname-to-tyspec+declor-of-tyspec+declor-to-ident+tyname
    (b* (((mv id tyname) (tyspec+declor-to-ident+tyname tyspec declor)))
      (equal (ident+tyname-to-tyspec+declor id tyname)
             (mv (tyspecseq-fix tyspec) (obj-declor-fix declor))))
    :enable tyspec+declor-to-ident+tyname)

  (defrule tyspec+declor-to-ident+tyname-of-ident+tyname-to-tyspec+declor
    (b* (((mv tyspec declor) (ident+tyname-to-tyspec+declor id tyname)))
      (equal (tyspec+declor-to-ident+tyname tyspec declor)
             (mv (ident-fix id) (tyname-fix tyname))))
    :enable tyspec+declor-to-ident+tyname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspec+declor-to-ident+params+tyname ((tyspec tyspecseqp)
                                              (declor fun-declorp))
  :returns (mv (id identp) (params param-declon-listp) (tyname tynamep))
  :short "Turn a type specifier sequence and a function declarator into
          an identifier, a list of parameter declarations, and a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose the declarator into an identifier and an abstract declarator,
     and we form a type name with the latter and the type specifier sequence.")
   (xdoc::p
    "The name of this ACL2 function does not mention @('fun') explicitly,
     but the fact that it deals with function declarators
     is implicit in the fact that it returns
     an identifier, a list of parameter declarations, and a type name.")
   (xdoc::p
    "In essence, we turn (the constituents of) a function declaration
     into its name and parameters and type,
     which are somewhat mixed in the C syntax.")
   (xdoc::p
    "The inverse of this is not well-defined for every type name,
     because the latter may include array declarators,
     which are not allowed in function declarators.
     We could define the inverse on type names
     that are restricted not to use array declarators;
     but we do not need the inverse for now."))
  (b* (((mv id fun-adeclor) (fun-declor-to-ident+adeclor declor))
       ((mv params obj-adeclor) (fun-adeclor-to-params+declor fun-adeclor)))
    (mv id params (make-tyname :tyspec tyspec :declor obj-adeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-declon-to-ident+tyname ((declon struct-declonp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Decompose a structure declaration into an identifier and a type name."
  (b* (((struct-declon declon) declon))
    (tyspec+declor-to-ident+tyname declon.tyspec declon.declor))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-to-ident+tyname ((declon param-declonp))
  :returns (mv (id identp) (tyname tynamep))
  :short "Decompose a parameter declaration into an identifier and a type name."
  (b* (((param-declon declon) declon))
    (tyspec+declor-to-ident+tyname declon.tyspec declon.declor))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-list-to-ident+tyname-lists
  ((declons param-declon-listp))
  :returns (mv (ids ident-listp) (tynames tyname-listp))
  :short "Lift @(tsee param-declon-to-ident+tyname) to lists."
  (b* (((when (endp declons)) (mv nil nil))
       ((mv id tyname) (param-declon-to-ident+tyname (car declons)))
       ((mv ids tynames) (param-declon-list-to-ident+tyname-lists
                          (cdr declons))))
    (mv (cons id ids) (cons tyname tynames)))
  :hooks (:fix)
  ///

  (defret len-of-param-declon-list-to-ident+tyname-lists.ids
    (equal (len ids)
           (len declons))
    :hints (("Goal" :induct t)))

  (defret len-of-param-declon-list-to-ident+tyname-lists.tynames
    (equal (len tynames)
           (len declons))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj-declon-to-ident+scspec+tyname+init ((declon obj-declonp))
  :returns (mv (id identp)
               (scspec scspecseqp)
               (tyname tynamep)
               (init initer-optionp))
  :short "Decompose an object declaration into
          an identifier,
          a storage class specifier sequence,
          a type name,
          and an optional initializer."
  (b* (((obj-declon declon) declon)
       ((mv id tyname) (tyspec+declor-to-ident+tyname declon.tyspec
                                                      declon.declor)))
    (mv id declon.scspec tyname declon.init?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-declon-list->fundef-list ((exts ext-declon-listp))
  :returns (defs fundef-listp)
  :short "Extract from a list of external declarations
          the list of function definitions, in the same order."
  :long
  (xdoc::topstring
   (xdoc::p
    "Declarations are discarded. Only function definitions are projected."))
  (b* (((when (endp exts)) nil)
       (ext (car exts)))
    (ext-declon-case ext
                     :fundef (cons (ext-declon-fundef->get ext)
                                   (ext-declon-list->fundef-list (cdr exts)))
                     :fun-declon (ext-declon-list->fundef-list (cdr exts))
                     :obj-declon (ext-declon-list->fundef-list (cdr exts))
                     :tag-declon (ext-declon-list->fundef-list (cdr exts))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef->name ((fundef fundefp))
  :returns (name identp)
  :short "Name of a function in a definition."
  (b* (((mv name &) (fun-declor-to-ident+adeclor (fundef->declor fundef))))
    name)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fundef-list->name-list (x)
  :guard (fundef-listp x)
  :returns (names ident-listp)
  :short "Lift @(tsee fundef->name) to lists."
  (fundef->name x)
  ///
  (fty::deffixequiv fundef-list->name-list
    :args ((x fundef-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-constp ((e exprp))
  :returns (yes/no booleanp)
  :short "Check if an expression is constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This concept is described in [C17:6.6],
     which does not provide a detailed definition,
     but here we define a notion that should be
     at least as strict as that (possibly stricter),
     for our current C subset."))
  (expr-case
   e
   :ident nil
   :const t
   :arrsub nil
   :call nil
   :member nil
   :memberp nil
   :postinc nil
   :postdec nil
   :preinc nil
   :predec nil
   :unary (and (member-eq (unop-kind e.op)
                          '(:plus
                            :minus
                            :bitnot
                            :lognot))
               (expr-constp e.arg))
   :cast (expr-constp e.arg)
   :binary (and (member-eq (binop-kind e.op)
                           '(:mul
                             :div
                             :rem
                             :add
                             :sub
                             :shl
                             :shr
                             :lt
                             :gt
                             :le
                             :ge
                             :eq
                             :ne
                             :bitand
                             :bitxor
                             :bitior
                             :logand
                             :logor))
                (expr-constp e.arg1)
                (expr-constp e.arg2))
   :cond (and (expr-constp e.test)
              (expr-constp e.then)
              (expr-constp e.else)))
  :measure (expr-count e)
  :hints (("Goal" :in-theory (enable o< o-finp o-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-constp (x)
  :guard (expr-listp x)
  :short "Lift @(tsee expr-constp) to lists."
  (expr-constp x)
  :true-listp nil
  :elementp-of-nil nil
  ///

  (fty::deffixequiv expr-list-constp
    :args ((x expr-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-to-fun-declon ((fundef fundefp))
  :returns (declon fun-declonp)
  :short "Function declaration of a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "As also explained in @(tsee fundef),
     a function definition is essentially a function declaration plus a body,
     but it is not quite defined like that
     for the technical reasons explained there.
     But this ACL2 function explicates that mapping."))
  (make-fun-declon :tyspec (fundef->tyspec fundef)
                   :declor (fundef->declor fundef))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection fundef-list-to-fun-declon-list (x)
  :guard (fundef-listp x)
  :returns (declons fun-declon-listp)
  :short "Lift @(tsee fundef-to-fun-declon) to lists."
  (fundef-to-fun-declon x)
  ///
  (fty::deffixequiv fundef-list-to-fun-declon-list
    :args ((x fundef-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-nocallsp ((expr exprp))
  :returns (yes/no booleanp)
  :short "Check if an expression does not contain any function calls."
  (expr-case
   expr
   :ident t
   :const t
   :arrsub (and (expr-nocallsp expr.arr)
                (expr-nocallsp expr.sub))
   :call nil
   :member (expr-nocallsp expr.target)
   :memberp (expr-nocallsp expr.target)
   :postinc (expr-nocallsp expr.arg)
   :postdec (expr-nocallsp expr.arg)
   :preinc (expr-nocallsp expr.arg)
   :predec (expr-nocallsp expr.arg)
   :unary (expr-nocallsp expr.arg)
   :cast (expr-nocallsp expr.arg)
   :binary (and (expr-nocallsp expr.arg1)
                (expr-nocallsp expr.arg2))
   :cond (and (expr-nocallsp expr.test)
              (expr-nocallsp expr.then)
              (expr-nocallsp expr.else)))
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o-p o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-list-nocallsp (x)
  :guard (expr-listp x)
  :short "Check if a list of expressions does not contain any function calls."
  (expr-nocallsp x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv expr-list-nocallsp
    :args ((x expr-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-option-nocallsp ((expr? expr-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional expression does not contain any function calls."
  (expr-option-case
   expr?
   :some (expr-nocallsp expr?.val)
   :none t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-nocallsp ((initer initerp))
  :returns (yes/no booleanp)
  :short "Check if an initializer does not contain any function calls."
  (initer-case
   initer
   :single (expr-nocallsp initer.get)
   :list (expr-list-nocallsp initer.get))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-option-nocallsp ((initer? initer-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional initializer does not contain any function calls."
  (initer-option-case
   initer?
   :some (initer-nocallsp initer?.val)
   :none t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj-declon-nocallsp ((declon obj-declonp))
  :returns (yes/no booleanp)
  :short "Check if an object declaration does not contain any function calls."
  (initer-option-nocallsp (obj-declon->init? declon))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define label-nocallsp ((label labelp))
  :returns (yes/no booleanp)
  :short "Check if a label does not contain any function calls."
  (label-case
   label
   :name t
   :cas (expr-nocallsp label.get)
   :default t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmts/blocks-nocallsp
  :short "Check if statements, block items, and lists of block items
          do not contain any function calls."

  (define stmt-nocallsp ((stmt stmtp))
    :returns (yes/no booleanp)
    :parents (abstract-syntax-operations stmts/blocks-nocallsp)
    :short "Check if a statement does not contain any function calls."
    (stmt-case
     stmt
     :labeled (and (label-nocallsp stmt.label)
                   (stmt-nocallsp stmt.body))
     :compound (block-item-list-nocallsp stmt.items)
     :expr (expr-nocallsp stmt.get)
     :null t
     :if (and (expr-nocallsp stmt.test)
              (stmt-nocallsp stmt.then))
     :ifelse (and (expr-nocallsp stmt.test)
                  (stmt-nocallsp stmt.then)
                  (stmt-nocallsp stmt.else))
     :switch (and (expr-nocallsp stmt.ctrl)
                  (stmt-nocallsp stmt.body))
     :while (and (expr-nocallsp stmt.test)
                 (stmt-nocallsp stmt.body))
     :dowhile (and (stmt-nocallsp stmt.body)
                   (expr-nocallsp stmt.test))
     :for (and (expr-option-nocallsp stmt.init)
               (expr-option-nocallsp stmt.test)
               (expr-option-nocallsp stmt.next)
               (stmt-nocallsp stmt.body))
     :goto t
     :continue t
     :break t
     :return (expr-option-nocallsp stmt.value))
    :measure (stmt-count stmt))

  (define block-item-nocallsp ((item block-itemp))
    :returns (yes/no booleanp)
    :parents (abstract-syntax-operations stmts/blocks-nocallsp)
    :short "Check if a block item does not contain any function calls."
    (block-item-case
     item
     :declon (obj-declon-nocallsp item.get)
     :stmt (stmt-nocallsp item.get))
    :measure (block-item-count item))

  (define block-item-list-nocallsp ((items block-item-listp))
    :returns (yes/no booleanp)
    :parents (abstract-syntax-operations stmts/blocks-nocallsp)
    :short "Check if a list of block items does not contain any function calls."
    (or (endp items)
        (and (block-item-nocallsp (car items))
             (block-item-list-nocallsp (cdr items))))
    :measure (block-item-list-count items))

  :hints (("Goal" :in-theory (enable o-p o-finp o<)))

  ///

  (fty::deffixequiv-mutual stmts/blocks-nocallsp)

  (std::deflist block-item-list-nocalls (x)
    :guard (block-item-listp x)
    :parents nil
    (block-item-nocallsp x)
    :elementp-of-nil t))

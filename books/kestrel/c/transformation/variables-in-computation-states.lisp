; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../language/object-type-preservation")
(include-book "../language/variable-resolution-preservation")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variables-in-computation-states
  :parents (transformation-tools)
  :short "Notions and theorems about variables in the computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Transformations may need facts about certain variables
     being in the computation state and having values of certain types.
     Here we introduce a predicate to state that fact,
     along with some theorems about how execution relates to that predicate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define c::compustate-has-var-with-type-p ((var c::identp)
                                           (type c::typep)
                                           (compst c::compustatep))
  :returns (yes/no booleanp)
  :short "Check if a computation state includes
          a variable with a given name
          containing a value of the given type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This predicate may belong to a more general place,
     perhaps in the language formalization;
     this is why we put it into the @('\"C\"') package."))
  (b* ((objdes (c::objdesign-of-var var compst)))
    (and objdes
         (b* ((val (c::read-object objdes compst)))
           (equal (c::type-of-value val) (c::type-fix type)))))
  :guard-hints
  (("Goal" :in-theory (enable c::valuep-of-read-object-of-objdesign-of-var)))
  :hooks (:fix)

  ///

  (defruled c::not-errorp-when-compustate-has-var-with-type-p
    (implies (c::compustate-has-var-with-type-p var type compst)
             (not (c::errorp
                   (c::read-object (c::objdesign-of-var var compst)
                                   compst))))
    :enable (c::valuep-of-read-object-of-objdesign-of-var
             c::not-errorp-when-valuep))

  (defruled c::type-of-value-when-compustate-has-var-with-type-p
    (implies (c::compustate-has-var-with-type-p var type compst)
             (equal (c::type-of-value
                     (c::read-object (c::objdesign-of-var var compst)
                                     compst))
                    (c::type-fix type))))

  (defruled c::compustate-has-var-with-type-p-of-create-other-var
    (b* ((compst1 (c::create-var var1 val compst)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var)
                    (c::identp var1)
                    (not (equal var var1))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::objdesign-of-var-of-create-var
             c::read-object-of-create-var-when-auto/static/alloc
             c::objdesign-static->name-of-objdesign-of-var
             c::objdesign-auto->name-of-objdesign-of-var)
    :use (:instance c::objdesign-kind-of-objdesign-of-var
                    (var var)
                    (compst compst))
    :disable c::objdesign-kind-of-objdesign-of-var)

  (defruled c::compustate-has-var-with-type-p-of-create-same-var
    (b* ((compst1 (c::create-var var val compst)))
      (implies (and (not (c::errorp compst1))
                    (c::identp var)
                    (equal type (c::type-of-value val)))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::objdesign-of-var-of-create-var
             c::read-object-of-create-var-when-auto/static/alloc
             nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled c::compustate-has-var-with-type-p-of-enter-scope
  :short "Preservation of @(tsee c::compustate-has-var-with-type-p)
          under @(tsee c::enter-scope)."
  (implies (c::compustate-has-var-with-type-p var type compst)
           (c::compustate-has-var-with-type-p var type (c::enter-scope compst)))
  :enable (c::compustate-has-var-with-type-p
           c::objdesign-of-var-of-enter-scope
           c::read-object-of-enter-scope
           c::not-errorp-when-valuep
           c::valuep-of-read-object-of-objdesign-of-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-compustate-vars-theorems
  :short "Theorems about variables in computation states w.r.t. execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "These theorems are about @(tsee c::compustate-has-var-with-type-p),
     and how the execution of constructs preserve and/or modify it."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defrulel objdesign-kind-of-objdesign-of-var-is-auto/static/alloc
    (b* ((objdes (c::objdesign-of-var var compst)))
      (implies objdes
               (member-equal (c::objdesign-kind objdes)
                             '(:auto :static :alloc))))
    :disable c::objdesign-kind-of-objdesign-of-var
    :use (:instance c::objdesign-kind-of-objdesign-of-var
                    (var var)
                    (compst compst)))

  (local (in-theory (disable acl2::member-of-cons)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled expr-ident-compustate-vars
    (b* ((expr (c::expr-ident var))
         (result (c::exec-expr-pure expr compst))
         (value (c::expr-value->value result)))
      (implies (c::compustate-has-var-with-type-p var type compst)
               (equal (c::type-of-value value) (c::type-fix type))))
    :enable (c::exec-expr-pure
             c::exec-ident
             c::compustate-has-var-with-type-p))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled expr-binary-asg-compustate-vars
    (b* ((op (c::expr-binary->op asg))
         (var-expr (c::expr-binary->arg1 asg))
         (var (c::expr-ident->get var-expr))
         (expr (c::expr-binary->arg2 asg))
         (compst1 (c::exec-expr-asg asg compst fenv limit))
         (type-var (c::type-of-value
                    (c::read-object
                     (c::objdesign-of-var var compst)
                     compst)))
         (type-expr (c::type-of-value
                     (c::expr-value->value
                      (c::exec-expr-pure expr compst)))))
      (implies (and (equal (c::expr-kind asg) :binary)
                    (equal op (c::binop-asg))
                    (equal (c::expr-kind var-expr) :ident)
                    (not (equal (c::expr-kind expr) :call))
                    (not (c::errorp compst1))
                    (equal type-var type-expr)
                    (c::type-nonchar-integerp type-expr)
                    (c::compustate-has-var-with-type-p var1 type compst))
               (c::compustate-has-var-with-type-p var1 type compst1)))
    :enable (c::compustate-has-var-with-type-p
             c::var-resolve-of-exec-expr-asg
             c::object-type-of-exec-expr-asg
             c::not-errorp-when-valuep
             c::valuep-of-read-object-of-objdesign-of-var))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled initer-single-pure-compustate-vars
    (b* ((expr (c::initer-single->get initer))
         ((mv result compst1)
          (c::exec-initer initer compst fenv limit))
         (type-expr (c::type-of-value
                     (c::expr-value->value
                      (c::exec-expr-pure expr compst)))))
      (implies (and (equal (c::initer-kind initer) :single)
                    (not (equal (c::expr-kind expr) :call))
                    (> (c::compustate-frames-number compst) 0)
                    (not (c::errorp result))
                    (c::type-nonchar-integerp type-expr)
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::compustate-has-var-with-type-p
             c::var-resolve-of-exec-initer
             c::object-type-of-exec-initer
             c::not-errorp-when-valuep
             c::valuep-of-read-object-of-objdesign-of-var))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-null-compustate-vars
    (b* (((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :null)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::compustate-has-var-with-type-p
             c::exec-stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-expr-asg-compustate-vars
    (b* ((expr (c::stmt-expr->get stmt))
         (compst0 (c::exec-expr-asg expr compst fenv (- limit 2)))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :expr)
                    (not (equal (c::expr-kind expr) :call))
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst0))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-stmt stmt compst fenv limit)
    :enable (c::exec-expr-call-or-asg))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-return-compustate-vars
    (b* ((expr? (c::stmt-return->value stmt))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :return)
                    (or (not expr?)
                        (not (equal (c::expr-kind expr?) :call)))
                    (> (c::compustate-frames-number compst) 0)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::compustate-has-var-with-type-p
             c::var-resolve-of-exec-stmt
             c::object-type-of-exec-stmt
             c::not-errorp-when-valuep
             c::valuep-of-read-object-of-objdesign-of-var))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-if-compustate-vars
    (b* ((test (c::stmt-if->test stmt))
         (then (c::stmt-if->then stmt))
         (test-result (c::exec-expr-pure test compst))
         (test-value (c::expr-value->value test-result))
         ((mv & compst0) (c::exec-stmt then compst fenv (1- limit)))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :if)
                    (not (c::errorp result))
                    (c::type-nonchar-integerp (c::type-of-value test-value))
                    (or (and (c::test-value test-value)
                             (c::compustate-has-var-with-type-p var
                                                                type
                                                                compst0))
                        (and (not (c::test-value test-value))
                             (c::compustate-has-var-with-type-p var
                                                                type
                                                                compst))))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-stmt stmt compst fenv limit)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-ifelse-compustate-vars
    (b* ((test (c::stmt-ifelse->test stmt))
         (then (c::stmt-ifelse->then stmt))
         (else (c::stmt-ifelse->else stmt))
         (test-result (c::exec-expr-pure test compst))
         (test-value (c::expr-value->value test-result))
         ((mv & then-compst) (c::exec-stmt then compst fenv (1- limit)))
         ((mv & else-compst) (c::exec-stmt else compst fenv (1- limit)))
         ((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :ifelse)
                    (not (c::errorp result))
                    (c::type-nonchar-integerp (c::type-of-value test-value))
                    (or (and (c::test-value test-value)
                             (c::compustate-has-var-with-type-p var
                                                                type
                                                                then-compst))
                        (and (not (c::test-value test-value))
                             (c::compustate-has-var-with-type-p var
                                                                type
                                                                else-compst))))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-stmt stmt compst fenv limit)
    :enable (c::apconvert-expr-value-when-not-array
             c::value-kind-not-array-when-value-integerp))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled stmt-compound-compustate-vars
    (b* (((mv result compst1) (c::exec-stmt stmt compst fenv limit)))
      (implies (and (equal (c::stmt-kind stmt) :compound)
                    (> (c::compustate-frames-number compst) 0)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::compustate-has-var-with-type-p
             c::var-resolve-of-exec-stmt
             c::object-type-of-exec-stmt
             c::not-errorp-when-valuep
             c::valuep-of-read-object-of-objdesign-of-var))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled decl-decl-compustate-vars-old
    (b* ((declor (c::obj-declon->declor declon))
         (var (c::obj-declor-ident->get declor))
         (initer (c::obj-declon->init? declon))
         ((mv & compst0) (c::exec-initer initer compst fenv (1- limit)))
         (compst1 (c::exec-obj-declon declon compst fenv limit)))
      (implies (and (equal (c::obj-declon->scspec declon) (c::scspecseq-none))
                    (equal (c::obj-declor-kind declor) :ident)
                    (not (c::errorp compst1))
                    (c::identp var1)
                    (not (equal var var1))
                    (c::compustate-has-var-with-type-p var1 type compst0))
               (c::compustate-has-var-with-type-p var1 type compst1)))
    :expand (c::exec-obj-declon declon compst fenv limit)
    :enable (c::obj-declon-to-ident+scspec+tyname+init
             c::tyspec+declor-to-ident+tyname
             c::obj-declor-to-ident+adeclor
             c::compustate-has-var-with-type-p-of-create-other-var))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled decl-decl-compustate-vars-new
    (b* ((declor (c::obj-declon->declor declon))
         (tyspecs (c::obj-declon->tyspec declon))
         (compst1 (c::exec-obj-declon declon compst fenv limit)))
      (implies (and (equal (c::obj-declon->scspec declon) (c::scspecseq-none))
                    (equal (c::obj-declor-kind declor) :ident)
                    (equal type (c::tyspecseq-to-type tyspecs))
                    (equal var (c::obj-declor-ident->get declor))
                    (not (c::errorp compst1)))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-obj-declon declon compst fenv limit)
    :enable (c::compustate-has-var-with-type-p-of-create-same-var
             c::obj-declon-to-ident+scspec+tyname+init
             c::tyspec+declor-to-ident+tyname
             c::obj-declor-to-ident+adeclor
             c::tyname-to-type
             c::tyname-to-type-aux
             c::init-value-to-value))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled block-item-stmt-compustate-vars
    (b* ((stmt (c::block-item-stmt->get item))
         ((mv & compst0) (c::exec-stmt stmt compst fenv (1- limit)))
         ((mv result compst1) (c::exec-block-item item compst fenv limit)))
      (implies (and (equal (c::block-item-kind item) :stmt)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst0))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-block-item item compst fenv limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled block-item-decl-compustate-vars
    (b* ((declon (c::block-item-declon->get item))
         (compst0 (c::exec-obj-declon declon compst fenv (1- limit)))
         ((mv result compst1) (c::exec-block-item item compst fenv limit)))
      (implies (and (equal (c::block-item-kind item) :declon)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst0))
               (c::compustate-has-var-with-type-p var type compst1)))
    :expand (c::exec-block-item item compst fenv limit))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled block-item-list-empty-compustate-vars
    (b* (((mv result compst1)
          (c::exec-block-item-list items compst fenv limit)))
      (implies (and (equal items nil)
                    (not (c::errorp result))
                    (c::compustate-has-var-with-type-p var type compst))
               (c::compustate-has-var-with-type-p var type compst1)))
    :enable (c::exec-block-item-list
             c::compustate-has-var-with-type-p))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defruled block-item-list-cons-compustate-vars
    (b* ((item (car item+items))
         (items (cdr item+items))
         ((mv result0 compst0)
          (c::exec-block-item item compst fenv (1- limit)))
         ((mv & compst1)
          (c::exec-block-item-list items compst0 fenv (1- limit)))
         ((mv result2 compst2)
          (c::exec-block-item-list item+items compst fenv limit)))
      (implies (and (consp item+items)
                    (not (c::errorp result2))
                    (or (and (equal (c::stmt-value-kind result0) :return)
                             (c::compustate-has-var-with-type-p
                              var type compst0))
                        (and (equal (c::stmt-value-kind result0) :none)
                             (c::compustate-has-var-with-type-p
                              var type compst1))))
               (c::compustate-has-var-with-type-p var type compst2)))
    :enable c::exec-block-item-list))

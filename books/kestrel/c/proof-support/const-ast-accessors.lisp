; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/abstract-syntax")

(include-book "std/util/defval" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ const-ast-accessors
  :parents (proof-support)
  :short "Executable counterparts of the AST accessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "When doing symbolic execution on concrete code represented as ASTs,
     it is normally necessary to enable the executable counterpart
     of the accessors of the ASTs,
     so that the execution functions can get to sub-constructs.
     Here we provide a list of these rules,
     as well as a ruleset with these rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *const-ast-accessors*
  :short "List of the executable counterparts of the AST accessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "For product types,
     we include the field accessors.
     For sum types,
     we include the kind discriminator,
     and the field accessors for each summand with fields.
     We omit fields that carry no semantic significance."))
  '(;; ident:
    (:e c::ident->name)
    ;; iconst-base:
    (:e c::iconst-base-kind)
    ;; iconst-length:
    (:e c::iconst-length-kind)
    ;; iconst:
    (:e c::iconst->value)
    (:e c::iconst->base)
    (:e c::iconst->unsignedp)
    (:e c::iconst->length)
    ;; const:
    (:e c::const-kind)
    (:e c::const-int->get)
    (:e const-enum->get)
    ;; tyspecseq:
    (:e c::tyspecseq-kind)
    (:e tyspecseq-float->complex)
    (:e tyspecseq-double->complex)
    (:e tyspecseq-ldouble->complex)
    (:e c::tyspecseq-struct->tag)
    (:e c::tyspecseq-union->tag)
    (:e c::tyspecseq-enum->tag)
    (:e tyspecseq-typedef->name)
    ;; scspecseq:
    (:e scspecseq-kind)
    ;; obj-declor:
    (:e obj-declor-kind)
    (:e obj-declor-ident->get)
    (:e obj-declor-pointer->decl)
    (:e obj-declor-array->decl)
    (:e obj-declor-array->size)
    ;; obj-adeclor:
    (:e obj-adeclor-kind)
    (:e obj-adeclor-pointer->decl)
    (:e obj-adeclor-array->decl)
    (:e obj-adeclor-array->size)
    ;; tyname:
    (:e tyname->tyspec)
    (:e tyname->declor)
    ;; unop:
    (:e unop-kind)
    ;; binop:
    (:e binop-kind)
    ;; expr:
    (:e expr-kind)
    (:e expr-ident->get)
    (:e expr-const->get)
    (:e expr-arrsub->arr)
    (:e expr-arrsub->sub)
    (:e expr-member->target)
    (:e expr-member->name)
    (:e expr-memberp->target)
    (:e expr-memberp->name)
    (:e expr-postinc->arg)
    (:e expr-postdec->arg)
    (:e expr-preinc->arg)
    (:e expr-predec->arg)
    (:e expr-unary->op)
    (:e expr-unary->arg)
    (:e expr-cast->type)
    (:e expr-cast->arg)
    (:e expr-binary->op)
    (:e expr-binary->arg1)
    (:e expr-binary->arg2)
    (:e expr-cond->test)
    (:e expr-cond->then)
    (:e expr-cond->else)
    ;; struct-declon:
    (:e struct-declon->tyspec)
    (:e struct-declon->declor)
    ;; tag-declon:
    (:e tag-declon-kind)
    (:e tag-declon-struct->tag)
    (:e tag-declon-struct->members)
    (:e tag-declon-union->tag)
    (:e tag-declon-union->members)
    (:e tag-declon-enum->tag)
    (:e tag-declon-enum->enumerators)
    ;; param-declon:
    (:e param-declon->tyspec)
    (:e param-declon->declor)
    ;; fun-declor:
    (:e fun-declor-kind)
    (:e fun-declor-base->name)
    (:e fun-declor-base->params)
    (:e fun-declor-pointer->decl)
    ;; fun-declor:
    (:e fun-declor-kind)
    (:e fun-declor-base->params)
    (:e fun-declor-pointer->decl)
    ;; fun-declon:
    (:e fun-declon->tyspec)
    (:e fun-declon->declor)
    ;; initer:
    (:e initer-kind)
    (:e initer-single->get)
    (:e initer-list->get)
    ;; obj-declon:
    (:e obj-declon->scspec)
    (:e obj-declon->tyspec)
    (:e obj-declon->declor)
    (:e obj-declon->init?)
    ;; label:
    (:e label-kind)
    (:e label-name->get)
    (:e label-cas->get)
    ;; stmt:
    (:e stmt-kind)
    (:e stmt-labeled->label)
    (:e stmt-labeled->body)
    (:e stmt-compound->items)
    (:e stmt-expr->get)
    (:e stmt-if->test)
    (:e stmt-if->then)
    (:e stmt-ifelse->test)
    (:e stmt-ifelse->then)
    (:e stmt-ifelse->else)
    (:e stmt-while->test)
    (:e stmt-while->body)
    (:e stmt-dowhile->body)
    (:e stmt-dowhile->test)
    (:e stmt-for->init)
    (:e stmt-for->test)
    (:e stmt-for->next)
    (:e stmt-for->body)
    (:e stmt-goto->target)
    (:e stmt-return->value)
    ;; block-item:
    (:e block-item-kind)
    (:e block-item-declon->get)
    (:e block-item-stmt->get)
    ;; fundef:
    (:e fundef->tyspec)
    (:e fundef->declor)
    (:e fundef->body)
    ;; ext-declon:
    (:e ext-declon-kind)
    (:e ext-declon-fundef->get)
    (:e ext-declon-fun-declon->get)
    (:e ext-declon-obj-declon->get)
    (:e ext-declon-tag-declon->get)
    ;; trans-unit:
    (:e trans-unit->declons)
    ;; trans-ensemble:
    (:e trans-ensemble->path-wo-ext)
    (:e trans-ensemble->dot-h)
    (:e trans-ensemble->dot-c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset const-ast-accessors
    ',*const-ast-accessors*))

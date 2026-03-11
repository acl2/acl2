; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/symbolic-execution-rules/top" :dir :system)
(include-book "kestrel/c/proof-support/const-ast-accessors" :dir :system)
(include-book "kestrel/c/proof-support/const-folding" :dir :system)
(include-book "kestrel/c/proof-support/exec-stmt-openers" :dir :system)
(include-book "kestrel/c/proof-support/exec-stmt-while-openers" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains supporting material for the strcpy-safe.lisp example.
; This supporting material is generic, not specific to that example;
; it could be moved to general libraries.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lists.

(defruled len-cdr-lemma
  (implies (< 1 (len x))
           (< 1 (+ 1 (len (cdr x))))))

(defruled len-cddr-lemma
  (implies (< 2 (len x))
           (< 2 (+ 2 (len (cddr x))))))

(defruled len-cdddr-lemma
  (implies (< 3 (len x))
           (< 3 (+ 3 (len (cdddr x))))))

(defruled cddr-when-len-gt-2
  (implies (> (len x) 2)
           (cddr x)))

;;;;;;;;;;;;;;;;;;;;

; Booleans.

(defruled if-of-boolean-t-nil
  (implies (booleanp x)
           (equal (if x t nil) x)))

;;;;;;;;;;;;;;;;;;;;

; Distributivity over IF.

(defruled c::expr-valuep-of-if
  (equal (c::expr-valuep (if a b c))
         (if a (c::expr-valuep b) (c::expr-valuep c))))

(defruled c::apconvert-expr-value-of-if
  (equal (c::apconvert-expr-value (if a b c))
         (if a (c::apconvert-expr-value b) (c::apconvert-expr-value c))))

(defruled c::expr-value->value-of-if
  (equal (c::expr-value->value (if a b c))
         (if a (c::expr-value->value b) (c::expr-value->value c))))

(defruled c::test-value-of-if
  (equal (c::test-value (if a b c))
         (if a (c::test-value b) (c::test-value c))))

(defruled booleanp-of-if
  (equal (booleanp (if a b c))
         (if a (booleanp b) (booleanp c))))

;;;;;;;;;;;;;;;;;;;;

; Array properties.

(defruled c::type-of-value-of-value-array
  (equal (c::type-of-value (c::value-array elemtype elements))
         (c::type-array elemtype (len elements)))
  :enable c::type-of-value)

(defruled c::len-of-value-array->elements-gt-0
  (> (len (c::value-array->elements x)) 0))

;;;;;;;;;;;;;;;;;;;;

; Relations between deep and shallow embedding.

(defruled c::value-array->elements-of-uchar-array-of
  (implies (consp elems)
           (equal (c::value-array->elements (c::uchar-array-of elems))
                  (c::uchar-list-fix elems)))
  :enable (c::uchar-array-of
           c::uchar-array
           c::value-array->elements
           c::value-kind
           c::value-listp-when-uchar-listp))

(defruled c::uchar-array->elements-to-value-array->elements
  (implies (c::uchar-arrayp a)
           (equal (c::uchar-array->elements a)
                  (c::value-array->elements a)))
  :enable (c::uchar-array->elements
           c::value-array->elements
           c::uchar-arrayp
           c::value-listp-when-uchar-listp
           c::value-kind))

(defruled c::uchar-array-of-to-value-array
  (implies (c::uchar-listp vals)
           (equal (c::uchar-array-of vals)
                  (c::value-array (c::type-uchar) vals)))
  :enable (c::uchar-array-of
           c::uchar-arrayp
           c::value-array
           c::value-listp-when-uchar-listp
           c::uchar-array->elements-to-value-array->elements
           c::value-array->elements
           c::value-kind
           c::uchar-array->elemtype))

(defruled c::value-array-to-uchar-array-of
  (implies (c::uchar-listp vals)
           (equal (c::value-array '(:uchar) vals)
                  (c::uchar-array-of vals)))
  :enable c::uchar-array-of-to-value-array)

(theory-invariant
 (incompatible (:rewrite c::uchar-array-of-to-value-array)
               (:rewrite c::value-array-to-uchar-array-of)))

(defruled c::uchar-listp-of-value-array->elements-when-uchar-arrayp
  (implies (c::uchar-arrayp a)
           (c::uchar-listp (c::value-array->elements a)))
  :use (:instance c::uchar-listp-of-uchar-array->elements (x a))
  :disable c::uchar-listp-of-uchar-array->elements
  :enable c::uchar-array->elements-to-value-array->elements)

;;;;;;;;;;;;;;;;;;;;

; Equality shifting.

(defruled c::equal-of-integer-from-uchar-to-uchar-from-integer
  (equal (equal (c::integer-from-uchar x) y)
         (and (c::uchar-integerp y)
              (equal (c::uchar-fix x) (c::uchar-from-integer y))))
  :enable (c::integer-from-uchar
           c::uchar-from-integer
           c::uchar-fix))

;;;;;;;;;;;;;;;;;;;;

; Turn array read & write into NTH & UPDATE-NTH.

(defruled c::uchar-array-read-of-sint-to-nth
  (implies (and (c::uchar-arrayp a)
                (c::sintp i)
                (<= 0 (c::integer-from-sint i))
                (< (c::integer-from-sint i)
                   (len (c::value-array->elements a))))
           (equal (c::uchar-array-read a i)
                  (nth (c::integer-from-sint i)
                       (c::value-array->elements a))))
  :enable (c::uchar-array-read
           c::integer-from-cinteger
           c::cinteger-kind
           c::cinteger-sint->get
           c::uchar-array->elements-to-value-array->elements
           c::uchar-listp-of-value-array->elements-when-uchar-arrayp))

(defruled c::uchar-array-write-of-sint-to-update-nth
  (implies (and (c::uchar-arrayp a)
                (c::sintp i)
                (<= 0 (c::integer-from-sint i))
                (< (c::integer-from-sint i)
                   (len (c::value-array->elements a)))
                (c::ucharp e))
           (equal (c::uchar-array-write a i e)
                  (c::uchar-array-of
                   (update-nth (c::integer-from-sint i)
                               e
                               (c::value-array->elements a)))))
  :enable (c::uchar-array-write
           c::uchar-array-index-okp
           c::uchar-array-length
           c::integer-from-cinteger
           c::cinteger-kind
           c::cinteger-sint->get
           c::uchar-array->elements-to-value-array->elements))

;;;;;;;;;;;;;;;;;;;;

; Rules for the symbolic execution.

(defconst *symb-exec-rules*
  '((:e booleanp)
    (:e c::binop-add)
    (:e c::binop-lt)
    (:e c::binop-sub)
    (:e c::expr-pure-limit)
    (:e c::expr-purep)
    (:e c::fun-info->body)
    (:e c::fun-info->params)
    (:e c::fun-info->result)
    (:e c::identp)
    (:e c::init-scope)
    (:e c::obj-declon-to-ident+scspec+tyname+init)
    (:e c::param-declon-to-ident+tyname)
    (:e c::param-declonp)
    (:e c::scopep)
    (:e c::sint-integerp)
    (:e c::uchar-integerp)
    (:e c::value-listp)
    (:e max)
    (:e member-equal)
    (:e omap::assoc)
    (:e str-fix)
    booleanp-of-if
    c::add-sint-and-value-when-sint
    c::add-sint-sint-const-fold
    c::add-sint-sint-okp-const-fold
    c::add-values-when-sint
    c::adjust-type-of-type-pointer
    c::apconvert-expr-value-of-if
    c::apconvert-expr-value-when-not-value-array
    c::booleanp-of-boolean-from-sint
    c::booleanp-of-boolean-from-uchar
    c::cintegerp-when-sintp
    c::compustate-frames-number-of-add-var-not-zero
    c::compustate-frames-number-of-enter-scope-not-zero
    c::compustatep-of-add-var
    c::compustatep-of-enter-scope
    c::compustatep-of-update-object
    c::compustatep-of-update-var
    c::create-var-of-const-identifier
    c::create-var-okp-of-add-frame
    c::create-var-okp-of-add-var
    c::create-var-okp-of-add-var
    c::create-var-to-add-var
    c::equal-of-ident-and-const
    c::equal-of-ident-and-ident
    c::exec-arrsub-when-uchar-arrayp
    c::exec-binary-strict-pure-when-add
    c::exec-binary-strict-pure-when-lt
    c::exec-binary-strict-pure-when-sub
    c::exec-block-item-list-of-nil
    c::exec-block-item-list-when-consp
    c::exec-block-item-when-declon
    c::exec-block-item-when-stmt
    c::exec-cast-of-uchar-when-sintp
    c::exec-const-to-sint
    c::exec-expr-pure-when-arrsub
    c::exec-expr-pure-when-binary-logand
    c::exec-expr-pure-when-cast
    c::exec-expr-pure-when-const
    c::exec-expr-pure-when-ident
    c::exec-expr-pure-when-strict-pure-binary
    c::exec-expr-when-asg-arrsub-when-uchar-arrayp
    c::exec-expr-when-asg-ident
    c::exec-expr-when-pure
    c::exec-fun-open-return
    c::exec-ident-open
    c::exec-initer-when-single
    c::exec-obj-declon-open
    c::exit-scope-of-enter-scope-when-compustatep
    c::expr-value->value-of-expr-value
    c::expr-value->value-of-if
    c::expr-value-optionp-when-expr-valuep
    c::expr-valuep-of-expr-value
    c::expr-valuep-of-if
    c::ident-fix-when-identp
    c::identp-of-ident
    c::init-scope-when-consp
    c::init-value-to-value-when-single
    c::len-of-value-array->elements-gt-0
    c::lt-sint-and-value-when-sint
    c::lt-values-when-sint
    c::not-errorp-when-expr-valuep
    c::not-flexible-array-member-p-when-sintp
    c::not-flexible-array-member-p-when-value-pointer
    c::not-zp-of-limit-minus-const
    c::not-zp-of-limit-variable
    c::pop-frame-of-add-frame
    c::pop-frame-of-add-var
    c::push-frame-of-one-empty-scope
    c::push-frame-of-one-nonempty-scope
    c::read-object-alloc-of-enter-scope
    c::read-object-of-add-frame
    c::read-object-of-add-var
    c::read-object-of-update-object-disjoint
    c::read-object-of-update-object-same
    c::read-var-of-add-var
    c::read-var-of-enter-scope
    c::remove-flexible-array-member-when-absent
    c::return-type-of-init-value-single
    c::return-type-of-stmt-value-none
    c::return-type-of-stmt-value-return
    c::scopep-of-update
    c::sint-from-boolean-with-error-when-booleanp
    c::sintp-of-lt-sint-sint
    c::sintp-of-sint-from-integer
    c::stmt-value-return->value?-of-stmt-value-return
    c::sub-sint-and-value-when-sint
    c::sub-values-when-sint
    c::test-value-of-if
    c::test-value-when-sintp
    c::test-value-when-ucharp
    c::tyname-to-type
    c::tyname-to-type-aux
    c::type-kind-of-type-sint
    c::type-of-value-of-value-array
    c::type-of-value-option-when-valuep
    c::type-of-value-when-sintp
    c::type-of-value-when-uchar-arrayp
    c::type-of-value-when-value-pointer
    c::tyspecseq-to-type
    c::uchar-array->elements-to-value-array->elements
    c::uchar-array-length
    c::uchar-array-length-of-uchar-array-write
    c::uchar-arrayp-of-uchar-array-write
    c::ucharp-of-uchar-array-read
    c::ucharp-of-uchar-from-integer
    c::update-object-of-add-frame
    c::update-object-of-add-var
    c::update-object-of-enter-scope
    c::update-object-of-update-object-same
    c::update-var-of-add-var
    c::update-var-of-enter-scope
    c::value-array->length-when-uchar-arrayp
    c::value-fix-when-valuep
    c::value-kind-when-sintp
    c::value-kind-when-ucharp
    c::value-listp-of-cons
    c::value-option-fix-when-value-optionp
    c::value-optionp-when-valuep
    c::valuep-when-sintp
    c::valuep-when-uchar-arrayp
    c::valuep-when-ucharp
    c::write-object-okp-of-add-frame
    c::write-object-okp-of-add-var
    c::write-object-okp-of-enter-scope
    c::write-object-okp-of-update-object-disjoint
    c::write-object-okp-of-update-object-same
    c::write-object-okp-when-valuep-of-read-object
    c::write-object-to-update-object
    c::write-var-okp-of-add-var
    c::write-var-okp-of-enter-scope
    c::write-var-to-update-var
    eq
    if-of-boolean-t-nil
    len-of-dst-postcond
    lookup-of-function
    omap::assoc-of-update))

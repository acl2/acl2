; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "types")

(include-book "../representation/integers")

(include-book "../language/static-semantics")

(include-book "fty-pseudo-terms")

(include-book "kestrel/std/util/error-value-tuples" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "std/strings/strtok-bang" :dir :system)

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defun list-lenp-fn (n l)
  (if (zp n)
      `(endp ,l)
    `(and (consp ,l)
          ,(list-lenp-fn (1- n) `(cdr ,l)))))

(defmacro list-lenp (n l)
  (declare (xargs :guard (natp n)))
  `(let ((l ,l)) ,(list-lenp-fn n 'l)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ term-checkers-common
  :parents (atc-event-and-code-generation defobject-implementation)
  :short "Checkers of ACL2 terms that represent C constructs,
          common to ATC and @(tsee defobject)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The shallow embedding of C in ACL2 defines
     representations of C constructs in ACL2.
     These are used by @(tsee atc) and @(tsee defobject),
     which check ACL2 terms to see if they represent C constructs,
     returning appropriate information if that is the case.")
   (xdoc::p
    "Here we collect some of this checking code on terms,
     which is common to @(tsee atc) and @(tsee defobject).
     We plan to organize all of this code more systematically at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-2part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp))
  :short "Check if a symbol consists of two parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>'),
     with @('<part1>') and @('<part2>') non-empty and without dashes,
     we return an indication of success and the two parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The two returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 2)) (mv nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym)))
    (mv t part1 part2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-3part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp)
               (part3 symbolp))
  :short "Check if a symbol consists of three parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>-<part3>'),
     with @('<part1>') and @('<part2>') and @('<part3>')
     non-empty and without dashes,
     we return an indication of success and the three parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The three returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 3)) (mv nil nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym))
       (part3 (intern-in-package-of-symbol (third parts) sym)))
    (mv t part1 part2 part3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-4part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp)
               (part3 symbolp)
               (part4 symbolp))
  :short "Check if a symbol consists of four parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>-<part3>-<part4>'),
     with @('<part1>') and @('<part2>') and @('<part3>') and @('<part4>')
     non-empty and without dashes,
     we return an indication of success and the four parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The four returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 4)) (mv nil nil nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym))
       (part3 (intern-in-package-of-symbol (third parts) sym))
       (part4 (intern-in-package-of-symbol (fourth parts) sym)))
    (mv t part1 part2 part3 part4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-5part ((sym symbolp))
  :returns (mv (yes/no booleanp)
               (part1 symbolp)
               (part2 symbolp)
               (part3 symbolp)
               (part4 symbolp)
               (part5 symbolp))
  :short "Check if a symbol consists of five parts separated by dash."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the symbol has the form @('<part1>-<part2>-<part3>-<part4>-<part5>'),
     with @('<part1>') and @('<part2>')
     and @('<part3>') and @('<part4>') and @('<part5>')
     non-empty and without dashes,
     we return an indication of success and the five parts.
     Otherwise, we return an indication of failure and @('nil') as the parts.
     The five returned symbols, when the function is successful,
     are interned in the same package as the input symbol."))
  (b* ((parts (str::strtok! (symbol-name sym) (list #\-)))
       ((unless (= (len parts) 5)) (mv nil nil nil nil nil nil))
       (part1 (intern-in-package-of-symbol (first parts) sym))
       (part2 (intern-in-package-of-symbol (second parts) sym))
       (part3 (intern-in-package-of-symbol (third parts) sym))
       (part4 (intern-in-package-of-symbol (fourth parts) sym))
       (part5 (intern-in-package-of-symbol (fifth parts) sym)))
    (mv t part1 part2 part3 part4 part5))
  :guard-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-iconst ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (type typep)
               (const iconstp))
  :short "Check if a term represents an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of a function @('<type>-<base>-const')
     on a quoted integer constant,
     we return the ACL2 function symbol,
     the C type of the term,
     and the C integer constant represented by the call.")
   (xdoc::p
    "In certain circumstances, we return an error in @('erp'),
     namely when the term cannot represent any other C construct."))
  (b* (((reterr) nil nil (irr-type) (irr-iconst))
       ((acl2::fun (no)) (retok nil nil (irr-type) (irr-iconst)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp type base const) (atc-check-symbol-3part fn))
       ((unless (and okp
                     (member-eq type '(sint uint slong ulong sllong ullong))
                     (member-eq base '(dec oct hex))
                     (eq const 'const)))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an integer constant function, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." term)))
       (arg (first args))
       ((unless (pseudo-term-case arg :quote))
        (reterr (msg "The function ~x0 must be applied to a quoted constant, ~
                      but it is applied to ~x1 instead."
                     fn arg)))
       (val (pseudo-term-quote->val arg))
       ((unless (natp val))
        (reterr (msg "The function ~x0 ~
                      must be applied to a quoted natural number, ~
                      but it is applied to ~x1 instead. ~
                      Since this is required by the guard of ~x0, ~
                      this call is unreachable under the guard."
                     fn val)))
       (inrangep (case type
                   (sint (sint-integerp val))
                   (uint (uint-integerp val))
                   (slong (slong-integerp val))
                   (ulong (ulong-integerp val))
                   (sllong (sllong-integerp val))
                   (ullong (ullong-integerp val))
                   (t (impossible))))
       ((unless inrangep)
        (reterr (msg "The function ~x0
                      must be applied to a quoted natural number ~
                      representable in the C type corresponding to ~x1, ~
                      but it is applied to ~x2 instead.
                      This is indicative of provably dead code, ~
                      given that the code is guard-verified."
                     fn type val)))
       (base (case base
               (dec (iconst-base-dec))
               (oct (iconst-base-oct))
               (hex (iconst-base-hex))
               (t (impossible))))
       ((mv const type)
        (case type
          (sint (mv (make-iconst :value val
                                 :base base
                                 :unsignedp nil
                                 :length (iconst-length-none))
                    (type-sint)))
          (uint (mv (make-iconst :value val
                                 :base base
                                 :unsignedp t
                                 :length (iconst-length-none))
                    (type-uint)))
          (slong (mv (make-iconst :value val
                                  :base base
                                  :unsignedp nil
                                  :length (iconst-length-long))
                     (type-slong)))
          (ulong (mv (make-iconst :value val
                                  :base base
                                  :unsignedp t
                                  :length (iconst-length-long))
                     (type-ulong)))
          (sllong (mv (make-iconst :value val
                                   :base base
                                   :unsignedp nil
                                   :length (iconst-length-llong))
                      (type-sllong)))
          (ullong (mv (make-iconst :value val
                                   :base base
                                   :unsignedp t
                                   :length (iconst-length-llong))
                      (type-ullong)))
          (t (mv (impossible) (impossible))))))
    (retok t fn type const))
  ///

  (defret type-integerp-of-atc-check-iconst-type
    (implies yes/no
             (type-integerp type)))

  (defret type-nonchar-integerp-of-atc-check-iconst-type
    (implies yes/no
             (type-nonchar-integerp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-unop ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (in-type typep)
               (out-type typep)
               (op unopp))
  :short "Check if a term may represent a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C unary operators,
     we return the function, the argument term
     the input and output types,
     and the C operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (b* (((reterr) nil nil nil (irr-type) (irr-type) (irr-unop))
       ((acl2::fun (no)) (retok nil nil nil (irr-type) (irr-type) (irr-unop)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp op fixtype) (atc-check-symbol-2part fn))
       (in-type (fixtype-to-integer-type fixtype))
       ((unless (and okp
                     (member-eq op '(plus minus bitnot lognot))
                     in-type))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an integer unary operation function, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." term)))
       (arg (first args))
       ((mv out-type unop)
        (case op
          (plus (mv (promote-type in-type) (unop-plus)))
          (minus (mv (promote-type in-type) (unop-minus)))
          (bitnot (mv (promote-type in-type) (unop-bitnot)))
          (lognot (mv (type-sint) (unop-lognot)))
          (t (prog2$ (impossible) (mv (irr-type) (irr-unop)))))))
    (retok t fn arg in-type out-type unop))
  ///

  (defret pseudo-term-count-of-atc-check-unop-arg
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-unop-in-type
    (implies yes/no
             (type-nonchar-integerp in-type)))

  (defret type-nonchar-integerp-of-atc-check-unop-out-type
    (implies yes/no
             (type-nonchar-integerp out-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-binop ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg1 pseudo-termp)
               (arg2 pseudo-termp)
               (in-type1 typep)
               (in-type2 typep)
               (out-type typep)
               (op binopp))
  :short "Check if a term may represent a strict pure binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C strict pure binary operators,
     we return the function, the argument terms,
     the inputs and output types,
     and the C operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (b* (((reterr) nil nil nil nil (irr-type) (irr-type) (irr-type) (irr-binop))
       ((acl2::fun (no))
        (retok nil nil nil nil (irr-type) (irr-type) (irr-type) (irr-binop)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp op fixtype1 fixtype2) (atc-check-symbol-3part fn))
       (in-type1 (fixtype-to-integer-type fixtype1))
       (in-type2 (fixtype-to-integer-type fixtype2))
       ((unless (and okp
                     (member-eq op '(add sub mul div rem shl shr
                                         lt le gt ge eq ne
                                         bitand bitxor bitior))
                     in-type1
                     in-type2))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an integer binary operation function, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 2 args))
        (reterr (raise "Internal error: ~x0 not applied to 2 arguments." term)))
       (arg1 (first args))
       (arg2 (second args))
       ((mv out-type binop)
        (case op
          (add (mv (uaconvert-types in-type1 in-type2) (binop-add)))
          (sub (mv (uaconvert-types in-type1 in-type2) (binop-sub)))
          (mul (mv (uaconvert-types in-type1 in-type2) (binop-mul)))
          (div (mv (uaconvert-types in-type1 in-type2) (binop-div)))
          (rem (mv (uaconvert-types in-type1 in-type2) (binop-rem)))
          (shl (mv (promote-type in-type1) (binop-shl)))
          (shr (mv (promote-type in-type1) (binop-shr)))
          (lt (mv (type-sint) (binop-lt)))
          (le (mv (type-sint) (binop-le)))
          (gt (mv (type-sint) (binop-gt)))
          (ge (mv (type-sint) (binop-ge)))
          (eq (mv (type-sint) (binop-eq)))
          (ne (mv (type-sint) (binop-ne)))
          (bitand (mv (uaconvert-types in-type1 in-type2) (binop-bitand)))
          (bitxor (mv (uaconvert-types in-type1 in-type2) (binop-bitxor)))
          (bitior (mv (uaconvert-types in-type1 in-type2) (binop-bitior)))
          (t (prog2$ (impossible) (mv (irr-type) (irr-binop)))))))
    (retok t fn arg1 arg2 in-type1 in-type2 out-type binop))
  ///

  (defret pseudo-term-count-of-atc-check-binop-arg1
    (implies yes/no
             (< (pseudo-term-count arg1)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-binop-arg2
    (implies yes/no
             (< (pseudo-term-count arg2)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-binop-in-type1
    (implies yes/no
             (type-nonchar-integerp in-type1)))

  (defret type-nonchar-integerp-of-atc-check-binop-in-type2
    (implies yes/no
             (type-nonchar-integerp in-type2)))

  (defret type-nonchar-integerp-of-atc-check-binop-out-type
    (implies yes/no
             (type-nonchar-integerp out-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-conv ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (in-type typep)
               (out-type typep)
               (out-tyname tynamep))
  :short "Check if a term may represent a conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represents C integer conversions,
     we return the function, the argument term,
     the input (i.e. argument) type, the output type,
     and the C output type name.
     The type name is redundant,
     because it can be determined from the output type,
     but we return it for the callers' convenience,
     since this kind of ACL2 term represents a C cast.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((reterr) nil nil nil (irr-type) (irr-type) (irr-tyname))
       ((acl2::fun (no)) (retok nil nil nil (irr-type) (irr-type) (irr-tyname)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp dtype from stype) (atc-check-symbol-3part fn))
       (in-type (fixtype-to-integer-type stype))
       (out-type (fixtype-to-integer-type dtype))
       ((unless (and okp
                     (eq from 'from)
                     in-type
                     out-type))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an integer conversion function, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." term)))
       (arg (first args))
       (out-tyname (type-to-tyname out-type)))
    (retok t fn arg in-type out-type out-tyname))
  ///

  (defret pseudo-term-count-of-atc-check-conv-arg
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

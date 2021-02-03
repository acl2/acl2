; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "kestrel/std/basic/good-valuep" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (acl2-programming-language)
  :short "A formalization of ACL2 values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 programming language has an "
    (xdoc::seetopic "acl2::evaluation" "evaluation semantics")
    ", which includes a notion of values.
     Here we formalize this notion."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod symbol-value
  :short "Fixtype of symbol values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Conceptually, a symbol consists of a package name and a (symbol) name.")
   (xdoc::p
    "We do not use the fixtype of the ACL2 symbols here
     (i.e. the fixtype for the built-in recognizer @(tsee symbolp)),
     because that type only contains symbols with known package names.
     Here instead we are formalizing
     the ACL2 programming language at the meta level,
     and therefore we must be able to talk about
     all possible symbols for different collections of known packages.")
   (xdoc::p
    "We use any strings as package names,
     even though there are restrictions on package names (see @(tsee defpkg)).
     These restrictions may be formalized elsewhere."))
  ((package string)
   (name string))
  :pred symbol-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist symbol-value-list
  :short "Fixtype of lists of symbol values."
  :elt-type symbol-value
  :true-listp t
  :elementp-of-nil nil
  :pred symbol-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-symbol-value
  symbol-value
  :short "Fixtype of symbol values and @('nil')."
  :pred maybe-symbol-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset symbol-value-set
  :short "Fixtype of finite sets of symbol values."
  :elt-type symbol-value
  :elementp-of-nil nil
  :pred symbol-value-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-symbol ((sym symbolp))
  :returns (symval symbol-valuep)
  :short "Lift an ACL2 symbol to a symbol value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function lifts an ACL2 symbol to the meta level,
     i.e. to our formalization of ACL2 symbols.")
   (xdoc::p
    "We extract package name and symbol name from the ACL2 symbol,
     and we build a symbol value that represents
     that symbol at the meta level."))
  (b* ((package (symbol-package-name sym))
       (name (symbol-name sym)))
    (make-symbol-value :package package :name name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection lift-symbol-list (x)
  :guard (symbol-listp x)
  :returns (symvals symbol-value-listp)
  :short "Lift @(tsee lift-symbol) to lists."
  (lift-symbol x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lower-symbol ((symval symbol-valuep))
  :returns (sym symbolp)
  :short "Lower a symbol value to an ACL2 symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the opposite of @(tsee lift-symbol).
     It lowers a symbol value from the meta level.")
   (xdoc::p
    "This must be used with care,
     because at the meta level
     a symbol is any pair of a package (name) and a (symbol) name,
     but (i) the package name may not exist in the current ACL2 environment
     and (ii) the package may exist but import a symbol with that name
     from another package.
     In the first case, the call of @(tsee pkg-witness) causes an error.
     In the second case, the resulting ACL2 symbol may have
     a different @(tsee symbol-package-name).")
   (xdoc::p
    "Nonetheless, if this function is judiciously called
     on a meta-level symbol that corresponds to
     an ACL2 symbol in the current ACL2 environment
     (e.g. on a result of @(tsee lift-symbol)),
     then the result will be the expected ACL2 symbol.")
   (xdoc::p
    "We construct the symbol via @(tsee intern-in-package-of-symbol),
     using the package witness of the package name.
     Since the guard of @(tsee pkg-witness) requires
     the package name to be non-empty,
     we need at least to check that here.
     If it is empty, we use the @('\"ACL2\"') package
     just to make this function total."))
  (b* ((package (symbol-value->package symval))
       (name (symbol-value->name symval))
       (package (if (equal package "") "ACL2" package)))
    (intern-in-package-of-symbol name (pkg-witness package)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum value
  :short "Fixtype of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 values of the evaluation semantics are
     numbers, characters, strings, symbols, and @(tsee cons) pairs.
     See the discussion in @(tsee symbol-value) for why
     we do not use the built-in ACL2 symbols here.")
   (xdoc::p
    "The ACL2 logical semantics also allows
     additional values called `bad atoms',
     and consequently @(tsee cons) pairs
     that may contain them directly or indirectly.
     However, such values cannot be constructed in evaluation,
     and therefore are not formalized here,
     where we are only concerned with the ACL2 programming language,
     not the ACL2 logic.")
   (xdoc::p
    "Note that the constructors
     @('value-number'),
     @('value-character'), and
     @('value-string')
     lift ACL2 numbers, characters, and symbols to the meta level,
     analogously to @(tsee lift-symbol) for symbols.
     Note also that the accessors
     @('value-number->get'),
     @('value-character->get'), and
     @('value-string->get')
     do the opposite, i.e. they lower numbers, characters, and strings
     from the meta level,
     analogously to @(tsee lower-symbol).")
   (xdoc::p
    "On the other hand, the constructor @('value-cons')
     does not lift a @(tsee cons) pair to the meta level,
     because it operates on two meta-level values.
     See @(tsee lift-value) instead."))
  (:number ((get acl2-number)))
  (:character ((get character)))
  (:string ((get string)))
  (:symbol ((get symbol-value)))
  (:cons ((car value) (cdr value)))
  :pred valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-list
  :short "Fixtype of lists of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that a list of values is not a meta-level value,
     i.e. it does not have type @(tsee value).
     It is an object-level value, of course;
     it represents a list of meta-level values."))
  :elt-type value
  :true-listp t
  :elementp-of-nil nil
  :pred value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-symbol-list ((symvals symbol-value-listp))
  :returns (values value-listp)
  :short "Lift @(tsee value-symbol) to lists."
  (cond ((endp symvals) nil)
        (t (cons (value-symbol (car symvals))
                 (value-symbol-list (cdr symvals)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-value
  value
  :short "Fixtype of values and @('nil')."
  :pred maybe-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-case-rational ((x valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a rational."
  :long
  (xdoc::topstring-p
   "The name of this function is analogous to
    the notation @('(value-case ... :number)') of the fixtype of values.")
  (and (value-case x :number)
       (rationalp (value-number->get x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-rational->get ((x (and (valuep x) (value-case-rational x))))
  :returns (x-rational rationalp
                       :hints (("Goal"
                                :in-theory (enable value-case-rational))))
  :short "Return the ACL2 rational from its meta representation."
  :long
  (xdoc::topstring-p
   "The name of this function is analogous to
    the accessor @(tsee value-number->get) of the fixtype of values.")
  (if (mbt (value-case-rational (value-fix x)))
      (value-number->get (value-fix x))
    0)
  :guard-hints (("Goal" :in-theory (enable value-case-rational)))
  ///
  (fty::deffixequiv value-rational->get
    :args ((x valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-case-integer ((x valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an integer."
  :long
  (xdoc::topstring-p
   "The name of this function is analogous to
    the notation @('(value-case ... :number)') of the fixtype of values.")
  (and (value-case x :number)
       (integerp (value-number->get x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integer->get ((x (and (valuep x) (value-case-integer x))))
  :returns (x-integer integerp
                      :hints (("Goal"
                               :in-theory (enable value-case-integer))))
  :short "Return the ACL2 integer from its meta representation."
  :long
  (xdoc::topstring-p
   "The name of this function is analogous to
    the accessor @(tsee value-number->get) of the fixtype of values.")
  (if (mbt (value-case-integer (value-fix x)))
      (value-number->get (value-fix x))
    0)
  :guard-hints (("Goal" :in-theory (enable value-case-integer)))
  ///
  (fty::deffixequiv value-integer->get
    :args ((x valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-nil ()
  :returns (value valuep)
  :short "The symbol value for @('nil')."
  (value-symbol (lift-symbol nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-t ()
  :returns (value valuep)
  :short "The symbol value for @('t')."
  (value-symbol (lift-symbol t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-list-of ((values value-listp))
  :returns (value valuep)
  :short "Make a meta-level list value from a list of meta-level values."
  (cond ((endp values) (value-nil))
        (t (value-cons (car values)
                       (value-list-of (cdr values)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-value ((x good-valuep))
  :returns (xval valuep)
  :short "Lift an ACL2 good value to a meta-level value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This extends @(tsee lift-symbol) to all values.
     More precisely, to all ``good'' values,
     as captured by @(tsee good-valuep).
     Even though good values are the only ones possible in execution,
     from a logical point of view there may be other values
     (i.e. bad atoms or @(tsee cons) pairs containing bad atoms at some level),
     and thus we need to restrict the domain of this lifting function."))
  (cond ((consp x) (value-cons (lift-value (car x))
                               (lift-value (cdr x))))
        ((acl2-numberp x) (value-number x))
        ((characterp x) (value-character x))
        ((stringp x) (value-string x))
        ((symbolp x) (value-symbol (lift-symbol x)))
        (t (prog2$ (impossible) (ec-call (value-fix :irrelevant)))))
  :verify-guards nil ; done below
  ///
  (verify-guards lift-value
    :hints (("Goal" :in-theory (enable good-valuep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lower-value ((xval valuep))
  :returns (x good-valuep
              :hints (("Goal" :in-theory (enable good-valuep))))
  :short "Lower a meta-level value to an ACL2 good value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee lift-value)."))
  (value-case xval
              :number (value-number->get xval)
              :character (value-character->get xval)
              :string (value-string->get xval)
              :symbol (lower-symbol (value-symbol->get xval))
              :cons (cons (lower-value (value-cons->car xval))
                          (lower-value (value-cons->cdr xval))))
  :measure (value-count xval)
  :hooks (:fix))

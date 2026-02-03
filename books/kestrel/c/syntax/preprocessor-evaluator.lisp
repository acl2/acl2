; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "implementation-environments")
(include-book "preprocessor-messages")
(include-book "abstract-syntax-irrelevants")

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-evaluator
  :parents (preprocessor)
  :short "Evaluator component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('#if') and @('#elif') directives contain
     integer constant expressions [C17:6.6/6]
     that must be evaluated [C17:6.10.1].
     In our preprocessor, this is done by the evaluator component,
     which is given the list of lexemes that follow a @('#if') and @('#elif'),
     after all macro replacement has taken place.
     Our evaluator parses those lexemes as an expression,
     which it then evaluates it.
     Any comment and white space, including the final new line,
     are ignored (i.e. skipped over) in this evaluation process:
     only tokens are relevant.")
   (xdoc::p
    "By the time we reach the evaluator.
     the occurrences of the @('defined') operator
     have already been evaluated, as part of macro replacement.
     They have been replaced by @('0') or @('1').")
   (xdoc::p
    "The details of character constants evaluation
     are implementation-defined [C17:6.4.4.4].
     Our preprocessor evaluates them to Unicode code points,
     in the natural way.
     We evaluate them to integers of type @('maxint_t'),
     which is enough to contains all Unicode code points,
     because @('maxint_t') is at least as large as @('long long').")
   (xdoc::p
    "Since operands always have type @('maxint_t') or @('umaxint_t'),
     no integer promotions [C17:6.3.1.1/2] are performed.
     The usual arithmetic conversions [C17:6.3.1.8]
     are performed in a limited way:
     see @(tsee uaconvert-pvalues)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pexpr
  :short "Fixtype of preprocessor expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ASTs for the constant expressions
     in @('#if') and @('#elif') directives [C17:6.10.1].
     These are similar to @(tsee expr) in our full abstract syntax:
     see that fixtype along with this one.
     We represent integer constant expressions [C17:6.6/6],
     with modifications motivated by the fact that we are preprocessing.
     [C17:6.6/6] does not give a completely precise definition;
     we discuss and motivate our choices below.")
   (xdoc::p
    "We represent integer constants as preprocessing numbers:
     we elaborate preprocessing numbers into integer constants
     (if they can be elaborated as such)
     during evaluation, after parsing.")
   (xdoc::p
    "Although [C17:6.6/6] allows floating constants
     as immediate operands of casts (to integer types, presumably),
     this does not seem to apply to the preprocessor.
     The preprocessor does not really know about types and casts.
     Indeed, both GCC and Clang fail when attempting to use
     a cast of a floating constant, or any cast in fact,
     as the expression of a conditional.
     Thus, we exclude floating constants.")
   (xdoc::p
    "We have a separate fixtype summand for character constants.
     These are explicitly called for in [C17:6.10.1/4], see footnote 171.")
   (xdoc::p
    "Unlike @(tsee expr), there are no enumeration constants here:
     they are just identifiers at this point,
     which are turned into @('0') [C17:6.10.1/4] during parsing.")
   (xdoc::p
    "We include no string literals, since they do not have integer types.")
   (xdoc::p
    "We include no parenthesized expressions,
     because for now we use these preprocessor expressions only transitorily,
     in order to evaluate them after parsing them,
     and parentheses are not relevant to that in ASTs.")
   (xdoc::p
    "Since the only allowed operands are numbers and characters [C17:6.6/6],
     it seems reasonable to exclude operations that require
     lvalues or pointer values or aggregate values.
     This excludes compound literals,
     array subscript operations,
     and structure/union member access;
     among the unary operators, it excludes @('&') and @('*');
     among the binary operators, it excludes all forms of assignment.
     Instead of using subtypes of @(tsee unop) and @(tsee binop),
     we spell out the allowed unary and binary operators
     as separate fixtype summands.")
   (xdoc::p
    "Perhaps somewhat inconsistently with [C17:6.6/6],
     [C17:6.6/3] allows for certain kinds of expressions
     to occur only in sub-expressions that are not evaluated.
     We omit them completely for now, to keep things simpler;
     we will add support for them later if needed.
     These are the unary operators that take lvalues (increment and decrement),
     the assignment operators (simple and compound),
     function calls,
     and comma expressions.")
   (xdoc::p
    "Note also that the comma operator is excluded at the top level
     by the fact the grammar rule for constant expressions says that
     they are conditional expressions [C17:6.6/1].")
   (xdoc::p
    "Although [C17:6.6/6] explictly calls out @('sizeof') and @('_Alignof'),
     both GCC and Clang reject them,
     which makes sense because the preprocessor
     does not really know about types.")
   (xdoc::p
    "Although [C17:6.6/6] explicitly calls out casts,
     both GCC and Clang reject them, as mentioned earlier.")
   (xdoc::p
    "Neither [C17:6.10.1] nor [C17:6.6/6] mention generic selections.
     Both GCC and Clang reject them.
     This makes sense because the preprocessor
     does not really know about types.")
   (xdoc::p
    "We avoid any GCC or Clang extensions for now.")
   (xdoc::p
    "Unlike @(tsee expr), there is no need to include ambiguous expressions.
     Those only arise when certain identifiers
     may ambiguously denote variables or types,
     but there are no identifiers here."))
  (:number ((number pnumber)))
  (:char ((char cconst)))
  (:plus ((arg pexpr)))
  (:minus ((arg pexpr)))
  (:bitnot ((arg pexpr)))
  (:lognot ((arg pexpr)))
  (:mul ((arg1 pexpr) (arg2 pexpr)))
  (:div ((arg1 pexpr) (arg2 pexpr)))
  (:rem ((arg1 pexpr) (arg2 pexpr)))
  (:add ((arg1 pexpr) (arg2 pexpr)))
  (:sub ((arg1 pexpr) (arg2 pexpr)))
  (:shl ((arg1 pexpr) (arg2 pexpr)))
  (:shr ((arg1 pexpr) (arg2 pexpr)))
  (:lt ((arg1 pexpr) (arg2 pexpr)))
  (:gt ((arg1 pexpr) (arg2 pexpr)))
  (:le ((arg1 pexpr) (arg2 pexpr)))
  (:ge ((arg1 pexpr) (arg2 pexpr)))
  (:eq ((arg1 pexpr) (arg2 pexpr)))
  (:ne ((arg1 pexpr) (arg2 pexpr)))
  (:bitand ((arg1 pexpr) (arg2 pexpr)))
  (:bitxor ((arg1 pexpr) (arg2 pexpr)))
  (:bitior ((arg1 pexpr) (arg2 pexpr)))
  (:logand ((arg1 pexpr) (arg2 pexpr)))
  (:logor ((arg1 pexpr) (arg2 pexpr)))
  (:cond ((test pexpr) (then pexpr) (else pexpr)))
  :pred pexprp
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pexpr
  :short "An irrelevant preprocessor expression."
  :type pexprp
  :body (pexpr-number (irr-pnumber)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pnumber-to-iconst ((number pnumberp))
  :returns (mv erp (const iconstp))
  :short "Turn a preprocessing number into an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the preprocessing number does not form a valid integer constant,
     we return an error.")
   (xdoc::p
    "We work by induction on the preprocessing number.
     Since we only convert to integer constants,
     any fixtype summand case involving dots and exponents
     results in an error, because it is for floating constants.
     This leaves three cases to consider:
     a single digit,
     a number followed by a digit,
     and a number followed by a nondigit.")
   (xdoc::p
    "If the preprocessing number is a single digit,
     we return the octal constant @('0') if the digit is 0,
     otherwise we return a decimal constant consisting of the digit.")
   (xdoc::p
    "If the preprocessing number consists of
     a digit after an inner preprocessing number,
     first we check whether the inner number is @('0x') or @('0X'),
     i.e. a hexadecimal prefix,
     in which case we return a hexadecimal constant
     with the digit as the only digit.
     Otherwise, we convert the inner number to an integer constant.
     The constant must have no suffixes, because those come after the digits.
     If the constant is decimal,
     we multiply its value by 10 and add the digit to it,
     obtaining a new decimal constant.
     If the constant is octal, we ensure that the additional digit is octal,
     and then there are a few cases:
     if the constans has value 0 and the digit is 0,
     we create a new octal constant with an extra leading 0 and still value 0;
     if the constant has value 0 but the digit is not 0,
     the digit becomes the value, and the leading zeros are unchanged;
     if the constant does not have value 0,
     we multiply the value by 8 and we add the digit to it.
     If the constant is hexadecimal,
     we add the digit to the end of the list of digits.")
   (xdoc::p
    "If the preprocessing number consists of
     a non-digit after an inner preprocessing number,
     first we check whether the inner number is @('0x') or @('0X'),
     i.e. a hexadecimal prefix,
     in which case we return a hexadecimal constant
     with the non-digit as the only hexadecimal digit,
     provided that it is a valid hexadecimal digit.
     Otherwise, we convert the inner number to an integer constant.
     If the non-digit is @('u') or @('U'),
     the integer constant must have no suffix
     or a suffix extensible with @('u') or @('U'):
     we incorporate the @('u') or @('U') into the suffix.
     If the non-digit is @('l') or @('U'),
     the integer constant must have no suffix
     or a suffix extensible with @('l') or @('L'):
     we incorporate the @('l') or @('L') into the suffix.
     If the non-digit is a valid hexadecimal digit,
     the constant generated from the inner number must be hexadecimal
     and have no suffixes:
     we add the digit to it.
     If the non-digit is anything else than the above, it is an error.")
   (xdoc::p
    "Note that, in both the number-and-digit and number-and-non-digit cases,
     the check that the inner number is a hexadecimal prefix
     must be done before trying to convert the inner number,
     because a hexadecimal prefix alone would not convert to
     a valid integer constant."))
  (b* (((reterr) (irr-iconst)))
    (pnumber-case
     number
     :digit
     (if (eql number.digit #\0)
         (retok
          (make-iconst :core (make-dec/oct/hex-const-oct :leading-zeros 1
                                                         :value 0)
                       :suffix? nil
                       :info nil))
       (retok
        (make-iconst :core (dec/oct/hex-const-dec
                            (str::dec-digit-char-value number.digit))
                     :suffix? nil
                     :info nil)))
     :dot-digit
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))
     :number-digit
     (b* (((when (equal number.number
                        (make-pnumber-number-nondigit
                         :number (pnumber-digit #\0)
                         :nondigit #\x)))
           (retok
            (make-iconst
             :core (make-dec/oct/hex-const-hex
                    :prefix (hprefix-locase-0x)
                    :digits (list number.digit))
             :suffix? nil
             :info nil)))
          ((when (equal number.number
                        (make-pnumber-number-nondigit
                         :number (pnumber-digit #\0)
                         :nondigit #\X)))
           (retok
            (make-iconst
             :core (make-dec/oct/hex-const-hex
                    :prefix (hprefix-upcase-0x)
                    :digits (list number.digit))
             :suffix? nil
             :info nil)))
          ((erp (iconst iconst)) (pnumber-to-iconst number.number))
          ((when iconst.suffix?)
           (reterr (msg "Incorrect preprocessing number ~x0."
                        (pnumber-fix number))))
          (digit-value (str::dec-digit-char-value number.digit)))
       (dec/oct/hex-const-case
        iconst.core
        :dec (b* ((value (+ (* 10 iconst.core.value) digit-value)))
               (retok (make-iconst :core (dec/oct/hex-const-dec value)
                                   :suffix? nil
                                   :info nil)))
        :oct (b* (((unless (< digit-value 8))
                   (reterr (msg "Incorrect preprocessing number ~x0."
                                (pnumber-fix number)))))
               (if (= iconst.core.value 0)
                   (if (eql number.digit #\0)
                       (retok
                        (make-iconst
                         :core (make-dec/oct/hex-const-oct
                                :leading-zeros (1+ iconst.core.leading-zeros)
                                :value 0)
                         :suffix? nil
                         :info nil))
                     (retok
                      (make-iconst
                       :core (make-dec/oct/hex-const-oct
                              :leading-zeros iconst.core.leading-zeros
                              :value digit-value)
                       :suffix? nil
                       :info nil)))
                 (retok
                  (make-iconst
                   :core (make-dec/oct/hex-const-oct
                          :leading-zeros iconst.core.leading-zeros
                          :value (+ (* 8 iconst.core.value) digit-value))
                   :suffix? nil
                   :info nil))))
        :hex (retok
              (make-iconst
               :core (make-dec/oct/hex-const-hex
                      :prefix iconst.core.prefix
                      :digits (append iconst.core.digits (list number.digit)))
               :suffix? nil
               :info nil))))
     :number-nondigit
     (b* (((when (equal number.number
                        (make-pnumber-number-nondigit
                         :number (pnumber-digit #\0)
                         :nondigit #\x)))
           (if (str::hex-digit-char-p number.nondigit)
               (retok
                (make-iconst
                 :core (make-dec/oct/hex-const-hex
                        :prefix (hprefix-locase-0x)
                        :digits (list number.nondigit))
                 :suffix? nil
                 :info nil))
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number)))))
          ((when (equal number.number
                        (make-pnumber-number-nondigit
                         :number (pnumber-digit #\0)
                         :nondigit #\X)))
           (if (str::hex-digit-char-p number.nondigit)
               (retok
                (make-iconst
                 :core (make-dec/oct/hex-const-hex
                        :prefix (hprefix-upcase-0x)
                        :digits (list number.nondigit))
                 :suffix? nil
                 :info nil))
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number)))))
          ((erp (iconst iconst)) (pnumber-to-iconst number.number))
          ((when (eql number.nondigit #\u))
           (cond
            ((not iconst.suffix?)
             (retok (change-iconst iconst
                                   :suffix? (isuffix-u (usuffix-locase-u)))))
            ((isuffix-case iconst.suffix? :l)
             (retok (change-iconst
                     iconst
                     :suffix? (make-isuffix-lu
                               :length (isuffix-l->length iconst.suffix?)
                               :unsigned (usuffix-locase-u)))))
            (t
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number))))))
          ((when (eql number.nondigit #\U))
           (cond
            ((not iconst.suffix?)
             (retok (change-iconst iconst
                                   :suffix? (isuffix-u (usuffix-upcase-u)))))
            ((isuffix-case iconst.suffix? :l)
             (retok (change-iconst
                     iconst
                     :suffix? (make-isuffix-lu
                               :length (isuffix-l->length iconst.suffix?)
                               :unsigned (usuffix-upcase-u)))))
            (t ; (member-eq (isuffix-kind iconst.suffix?) '(:u :ul :lu))
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number))))))
          ((when (eql number.nondigit #\l))
           (cond
            ((not iconst.suffix?)
             (retok (change-iconst iconst
                                   :suffix? (isuffix-l (lsuffix-locase-l)))))
            ((isuffix-case iconst.suffix? :u)
             (retok (change-iconst
                     iconst
                     :suffix? (make-isuffix-ul
                               :unsigned (isuffix-u->unsigned iconst.suffix?)
                               :length (lsuffix-locase-l)))))
            ((isuffix-case iconst.suffix? :l)
             (if (lsuffix-case (isuffix-l->length iconst.suffix?) :locase-l)
                 (retok (change-iconst
                         iconst
                         :suffix? (isuffix-l (lsuffix-locase-ll))))
               (reterr (msg "Incorrect preprocessing number ~x0."
                            (pnumber-fix number)))))
            ((isuffix-case iconst.suffix? :ul)
             (if (lsuffix-case (isuffix-ul->length iconst.suffix?) :locase-l)
                 (retok (change-iconst
                         iconst
                         :suffix? (make-isuffix-ul
                                   :unsigned (isuffix-ul->unsigned
                                              iconst.suffix?)
                                   :length (lsuffix-locase-ll))))
               (reterr (msg "Incorrect preprocessing number ~x0."
                            (pnumber-fix number)))))
            (t ; (isuffix-case iconst.sufix? :lu)
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number))))))
          ((when (eql number.nondigit #\L))
           (cond
            ((not iconst.suffix?)
             (retok (change-iconst iconst
                                   :suffix? (isuffix-l (lsuffix-upcase-l)))))
            ((isuffix-case iconst.suffix? :u)
             (retok (change-iconst
                     iconst
                     :suffix? (make-isuffix-ul
                               :unsigned (isuffix-u->unsigned iconst.suffix?)
                               :length (lsuffix-upcase-l)))))
            ((isuffix-case iconst.suffix? :l)
             (if (lsuffix-case (isuffix-l->length iconst.suffix?) :upcase-l)
                 (retok (change-iconst
                         iconst
                         :suffix? (isuffix-l (lsuffix-upcase-ll))))
               (reterr (msg "Incorrect preprocessing number ~x0."
                            (pnumber-fix number)))))
            ((isuffix-case iconst.suffix? :ul)
             (if (lsuffix-case (isuffix-ul->length iconst.suffix?) :upcase-l)
                 (retok (change-iconst
                         iconst
                         :suffix? (make-isuffix-ul
                                   :unsigned (isuffix-ul->unsigned
                                              iconst.suffix?)
                                   :length (lsuffix-upcase-ll))))
               (reterr (msg "Incorrect preprocessing number ~x0."
                            (pnumber-fix number)))))
            (t ; (isuffix-case iconst.sufix? :lu)
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number))))))
          ((when (str::hex-digit-char-p number.nondigit))
           (if (and (not iconst.suffix?)
                    (dec/oct/hex-const-case iconst.core :hex))
               (retok
                (make-iconst
                 :core (change-dec/oct/hex-const-hex
                        iconst.core
                        :digits (append
                                 (dec/oct/hex-const-hex->digits iconst.core)
                                 (list number.nondigit)))
                 :suffix? nil
                 :info nil))
             (reterr (msg "Incorrect preprocessing number ~x0."
                          (pnumber-fix number))))))
       (reterr (msg "Incorrect preprocessing number ~x0."
                    (pnumber-fix number))))
     :number-locase-e-sign
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))
     :number-upcase-e-sign
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))
     :number-locase-p-sign
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))
     :number-upcase-p-sign
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))
     :number-dot
     (reterr
      (msg "Unsupported preprocessing number ~x0." (pnumber-fix number)))))
  :measure (pnumber-count number)
  :verify-guards :after-returns
  :guard-hints (("Goal"
                 :in-theory (e/d (natp
                                  posp
                                  str::dec-digit-char-value
                                  str::letter/uscore-char-p
                                  dec-digit-char-p
                                  hex-digit-char-p)
                                 (pnumber-digit-requirements
                                  pnumber-number-digit-requirements))
                 :use ((:instance pnumber-digit-requirements
                                  (x number))
                       (:instance pnumber-number-digit-requirements
                                  (x number))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pvalue
  :short "Fixtype of values used by the preprocessor evaluator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only values meeded are integers
     of types @('intmax_t') and @('uintmax_t') [C17:6.19.1/4],
     i.e. signed and unsigned integers with a certain number of bits.
     We model them as any integer and natural number,
     checking that they are in range outside of this fixtype."))
  (:signed ((integer int)))
  (:unsigned ((integer nat)))
  :pred pvaluep
  :prepwork ((local (in-theory (enable ifix)))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pvalue
  :short "An irrelevant prepocessor value."
  :type pvaluep
  :body (pvalue-unsigned 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pvalue->integer ((pval pvaluep))
  :returns (ival integerp :rule-classes (:rewrite :type-prescription))
  :short "Mathematical integer of a @(tsee pvalue)."
  (pvalue-case pval
               :signed pval.integer
               :unsigned pval.integer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-iconst ((iconst iconstp) (ienv ienvp))
  :returns (mv erp (val pvaluep))
  :short "Evaluate an integer constant during preproecessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "Normally the type (and thus the kind of value) of an integer constant
     is determined via the table in [C17:6.4.4/5].
     In the preprocessor, there are only two types,
     namely @('maxint_t') and @('umaxint_t'),
     whose range of possible integer values
     we capture in the implementation environments.")
   (xdoc::p
    "Any length suffix is ignored,
     because @('maxint_t') and @('umaxint_t')
     are at least as large as @('long long') and @('unsigned long long').")
   (xdoc::p
    "If the integer constant has an unsigned suffix,
     the resulting value is unsigned, provided it fits in the range.
     If the integer constant has no unsigned suffix
     and has decimal base,
     the resulting value is signed, provided it fits the range.
     If the integer constant has no unsigned suffix
     and has octal or hexadecimal base,
     the resulting value is signed if it fits,
     otherwise unsigned if it fits."))
  (b* (((reterr) (irr-pvalue))
       ((iconst iconst) iconst)
       ((mv ival unsigned-okp)
        (dec/oct/hex-const-case
         iconst.core
         :dec (mv iconst.core.value nil)
         :oct (mv iconst.core.value t)
         :hex (mv (str::hex-digit-chars-value iconst.core.digits) t)))
       ((when (and iconst.suffix?
                   (member-eq (isuffix-kind iconst.suffix?) '(:u :ul :lu))))
        (if (ienv-uinteger-max-rangep ival ienv)
            (retok (pvalue-unsigned ival))
          (reterr (msg "Integer constant ~x0 has value ~x1 out of range."
                       (iconst-fix iconst) ival))))
       ((when (ienv-sinteger-max-rangep ival ienv))
        (retok (pvalue-signed ival)))
       ((when (and unsigned-okp
                   (ienv-uinteger-max-rangep ival ienv)))
        (retok (pvalue-unsigned ival))))
    (reterr (msg "Integer constant ~x0 has value ~x1 out of range."
                 (iconst-fix iconst) ival))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-pnumber ((number pnumberp) (ienv ienvp))
  :returns (mv erp (val pvaluep))
  :short "Evaluate a preprocessing number during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert the preprocessing number to an integer constant
     and then we evaluate the latter."))
  (b* (((reterr) (irr-pvalue))
       ((erp iconst) (pnumber-to-iconst number)))
    (peval-iconst iconst ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-simple-escape ((esc simple-escapep))
  :returns (val pvaluep)
  :short "Evaluate a simple escape during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each simple escape naturally corresponds to an ASCII code,
     which is also a Unicode code point."))
  (pvalue-signed
   (simple-escape-case esc
                       :squote (char-code #\')
                       :dquote (char-code #\")
                       :qmark (char-code #\?)
                       :bslash (char-code #\\)
                       :a 7
                       :b 8
                       :f 12
                       :n 10
                       :r 13
                       :t 9
                       :v 11
                       :percent (char-code #\%))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-oct-escape ((esc oct-escapep))
  :returns (val pvaluep)
  :short "Evaluate an octal escape during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the value of the octal representation."))
  (pvalue-signed
   (oct-escape-case esc
                    :one (str::oct-digit-char-value esc.digit)
                    :two (str::oct-digit-chars-value (list esc.digit1
                                                           esc.digit2))
                    :three (str::oct-digit-chars-value (list esc.digit1
                                                             esc.digit2
                                                             esc.digit3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-univ-char-name ((ucn univ-char-name-p))
  :returns (mv erp (val pvaluep))
  :short "Evaluate a universal character name during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the numeric value of the hexadecimal digits,
     provided that it does not exceed 10FFFFh."))
  (b* (((reterr) (irr-pvalue))
       (code (univ-char-name-case
              ucn
              :locase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad)
                               (hex-quad->2nd ucn.quad)
                               (hex-quad->3rd ucn.quad)
                               (hex-quad->4th ucn.quad)))
              :upcase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad1)
                               (hex-quad->2nd ucn.quad1)
                               (hex-quad->3rd ucn.quad1)
                               (hex-quad->4th ucn.quad1)
                               (hex-quad->1st ucn.quad2)
                               (hex-quad->2nd ucn.quad2)
                               (hex-quad->3rd ucn.quad2)
                               (hex-quad->4th ucn.quad2))))))
    (if (<= code #x10ffff)
        (retok (pvalue-signed code))
      (reterr (msg "Universal character name ~x0 exceeds 10FFFFh."
                   (univ-char-name-fix ucn))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-escape ((esc escapep))
  :returns (mv erp (val pvaluep))
  :short "Evaluate an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Simple escapes, octal escapes, and universal character names
     are handled by separate functions.
     Hexadecimal escapes evaluate to their numeric values,
     if they do not exceed 10FFFFh."))
  (b* (((reterr) (irr-pvalue)))
    (escape-case
     esc
     :simple (retok (peval-simple-escape esc.escape))
     :oct (retok (peval-oct-escape esc.escape))
     :hex (b* ((code (str::hex-digit-chars-value esc.escape)))
            (if (<= code #x10ffff)
                (retok (pvalue-signed code))
              (reterr (msg "Hexadecimal escape ~x0 exceeds 10FFFFh."
                           esc.escape))))
     :univ (peval-univ-char-name esc.escape))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-c-char ((cchar c-char-p))
  :returns (mv erp (val pvaluep))
  :short "Evaluate a character of a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a character with an explicit code,
     the result of the evaluation is the code,
     provided it does not exceed 10FFFFh.
     For an escape, we use a separate function."))
  (b* (((reterr) (irr-pvalue)))
    (c-char-case
     cchar
     :char (if (<= cchar.code #x10ffff)
               (retok (pvalue-signed cchar.code))
             (reterr (msg "Character ~x0 exceeds 10FFFFh." (c-char-fix cchar))))
     :escape (peval-escape cchar.escape))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-c-char-list ((cchars c-char-listp))
  :returns (mv erp (val pvaluep))
  :short "Evaluate a list of characters in a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list must be a singleton,
     and it evaluates to the same as its one character."))
  (b* (((reterr) (irr-pvalue)))
    (if (and (consp cchars)
             (endp (cdr cchars)))
        (peval-c-char (car cchars))
      (reterr (msg "Evaluation of ~x0 characters is not defined."
                   (len cchars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-cconst ((cconst cconstp))
  :returns (mv erp (val pvaluep))
  :short "Evaluate a character constant during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since during preprocessing character constants
     are interpreted, like integers,
     as having the types @('maxint_t') and @('umaxint_t'),
     we ignore the prefix, if any.
     We evaluate the underlying character sequence (which must be a singleton)
     to a signed integer of type @('maxint_t')."))
  (peval-c-char-list (cconst->cchars cconst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define result-pvalue ((ival integerp) signed/unsigned (ienv ienvp))
  :guard (member-eq signed/unsigned '(:signed :unsigned))
  :returns (mv erp (pval pvaluep))
  :short "Calculate a result @(tsee pvalue) from an integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn a mathematical integer,
     resulting from an arithmetic operation,
     into a value of type @('maxint_t') or @('umaxint_t'),
     as indicated by the @('signedp') flag.
     Signed arithmetic is defined only if it fits within the type,
     while unsigned arithmetic is always defined via modular reduction
     [C17:6.3.1.3]."))
  (b* (((reterr) (irr-pvalue)))
    (case signed/unsigned
      (:signed
       (if (ienv-sinteger-max-rangep (ifix ival) ienv)
           (retok (pvalue-signed ival))
         (reterr
          (msg "The integer ~x0 does not fit in maxint_t." (ifix ival)))))
      (:unsigned
       (retok (pvalue-unsigned (mod (ifix ival)
                                    (1+ (ienv->uinteger-max ienv))))))
      (t (prog2$ (impossible) (reterr :impossible))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uaconvert-pvalues ((pval1 pvaluep) (pval2 pvaluep) (ienv ienvp))
  :returns (mv (new-pval1 pvaluep) (new-pval2 pvaluep))
  :short "Apply the usual arithmetic conversions [C17:6.3.1.8]
          to two @(tsee pvalue)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a limited form of the usual arithmetic conversions,
     because the only types are @('maxint_t') and @('umaxint_t').
     If one operand is @('maxint_t') and the other is @('uintmax_t'),
     the signed one is converted to unsigned."))
  (pvalue-case
   pval1
   :signed (pvalue-case
            pval2
            :signed (mv (pvalue-fix pval1) (pvalue-fix pval2))
            :unsigned (mv (pvalue-unsigned
                           (mod pval1.integer
                                (1+ (ienv->uinteger-max ienv))))
                          (pvalue-fix pval2)))
   :unsigned (pvalue-case
              pval2
              :signed (mv (pvalue-fix pval1)
                          (pvalue-unsigned
                           (mod pval2.integer
                                (1+ (ienv->uinteger-max ienv)))))
              :unsigned (mv (pvalue-fix pval1) (pvalue-fix pval2))))

  ///

  (defret same-types-of-uaconvert-pvalues
    (equal (pvalue-kind new-pval1)
           (pvalue-kind new-pval2)))

  (in-theory (disable same-types-of-uaconvert-pvalues)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-plus ((arg pvaluep))
  :returns (result pvaluep)
  :short "Evaluate the unary plus operator [C17:6.5.3.3/2]
          during preprocessing."
  (pvalue-fix arg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-minus ((arg pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the unary minus operator [C17:6.5.3.3/3]
          during preprocessing."
  (result-pvalue (- (pvalue->integer arg))
                 (pvalue-kind arg)
                 ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-bitnot ((arg pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the bitwise complement operator [C17:6.5.3.3/4]
          during preprocessing."
  (result-pvalue (lognot (pvalue->integer arg))
                 (pvalue-kind arg)
                 ienv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-lognot ((arg pvaluep))
  :returns (result pvaluep)
  :short "Evaluate the logical complement operator [C17:6.5.3.3/5]
          during preprocessing."
  (if (= (pvalue->integer arg) 0)
      (pvalue-signed 1)
    (pvalue-signed 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-mul ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the multiplication operator [C17:6.5.5/4]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (* (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-div ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the division operator [C17:6.5.5/5] [C17:6.5.5/6]
          during preprocessing."
  (b* (((reterr) (irr-pvalue))
       ((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (= (pvalue->integer arg2) 0)
        (reterr (msg "Divisor is zero."))
      (result-pvalue (truncate (pvalue->integer arg1) (pvalue->integer arg2))
                     (pvalue-kind arg1)
                     ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-rem ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the remainder operator [C17:6.5.5/5] [C17:6.5.5/6]
          during preprocessing."
  (b* (((reterr) (irr-pvalue))
       ((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (= (pvalue->integer arg2) 0)
        (reterr (msg "Divisor is zero."))
      (result-pvalue (rem (pvalue->integer arg1) (pvalue->integer arg2))
                     (pvalue-kind arg1)
                     ienv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-add ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the addition operator [C17:6.5.6/5]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (+ (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-sub ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the subtraction operator [C17:6.5.6/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (- (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-shl ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the left shift operator [C17:6.5.7/3] [C17:6.5.7/4]
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the result is that of the left operand.
     The left operand must be non-negative.
     The right operand must be non-negative
     and below the number of bits of the left operand.
     No usual arithmetic conversions are performed."))
  (b* (((reterr) (irr-pvalue))
       (ival1 (pvalue->integer arg1))
       (ival2 (pvalue->integer arg2))
       ((unless (>= ival1 0))
        (reterr (msg "Shift operand is negative.")))
       ((unless (and (<= 0 ival2)
                     (< ival2 (* 8 (ienv->integer-max-bytes ienv)))))
        (reterr (msg "Shift distance out of range."))))
    (result-pvalue (* ival1 (expt 2 ival2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-shr ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the right shift operator [C17:6.5.7/3] [C17:6.5.7/5]
          during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the result is that of the left operand.
     The left operand must be non-negative.
     The right operand must be non-negative
     and below the number of bits of the left operand.
     No usual arithmetic conversions are performed."))
  (b* (((reterr) (irr-pvalue))
       (ival1 (pvalue->integer arg1))
       (ival2 (pvalue->integer arg2))
       ((unless (>= ival1 0))
        (reterr (msg "Shift operand is negative.")))
       ((unless (and (<= 0 ival2)
                     (< ival2 (* 8 (ienv->integer-max-bytes ienv)))))
        (reterr (msg "Shift distance out of range."))))
    (result-pvalue (truncate ival1 (expt 2 ival2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-lt ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the less-than operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (< (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-gt ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the greater-than operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (> (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-le ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the less-than-or-equal-to operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (<= (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-ge ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the greater-than-or-equal-to operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (>= (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-eq ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the equality operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (= (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-ne ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (result pvaluep)
  :short "Evaluate the non-equality operator [C17:6.5.8/6]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (if (/= (pvalue->integer arg1) (pvalue->integer arg2))
        (pvalue-signed 1)
      (pvalue-signed 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-bitand ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the bitwise conjunction operator [C17:6.5.10/4]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (logand (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-bitxor ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the bitwise exclusive disjunction operator [C17:6.5.11/4]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (logxor (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-bitior ((arg1 pvaluep) (arg2 pvaluep) (ienv ienvp))
  :returns (mv erp (result pvaluep))
  :short "Evaluate the bitwise inclusive disjunction operator [C17:6.5.12/4]
          during preprocessing."
  (b* (((mv arg1 arg2) (uaconvert-pvalues arg1 arg2 ienv)))
    (result-pvalue (logior (pvalue->integer arg1) (pvalue->integer arg2))
                   (pvalue-kind arg1)
                   ienv)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peval-expr ((expr pexprp) (ienv ienvp))
  :returns (mv erp (pval pvaluep))
  :short "Evaluate an expression during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since all these expressions are pure,
     the order of evaluation does not matter.
     It only matters for the non-strict expressions."))
  (b* (((reterr) (irr-pvalue)))
    (pexpr-case
     expr
     :number (peval-pnumber expr.number ienv)
     :char (peval-cconst expr.char)
     :plus (b* (((erp arg) (peval-expr expr.arg ienv)))
             (retok (peval-plus arg)))
     :minus (b* (((erp arg) (peval-expr expr.arg ienv)))
              (peval-minus arg ienv))
     :bitnot (b* (((erp arg) (peval-expr expr.arg ienv)))
               (peval-bitnot arg ienv))
     :lognot (b* (((erp arg) (peval-expr expr.arg ienv)))
               (retok (peval-lognot arg)))
     :mul (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-mul arg1 arg2 ienv))
     :div (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-div arg1 arg2 ienv))
     :rem (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-rem arg1 arg2 ienv))
     :add (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-add arg1 arg2 ienv))
     :sub (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-sub arg1 arg2 ienv))
     :shl (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-shl arg1 arg2 ienv))
     :shr (b* (((erp arg1) (peval-expr expr.arg1 ienv))
               ((erp arg2) (peval-expr expr.arg2 ienv)))
            (peval-shr arg1 arg2 ienv))
     :lt (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-lt arg1 arg2 ienv)))
     :gt (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-gt arg1 arg2 ienv)))
     :le (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-le arg1 arg2 ienv)))
     :ge (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-ge arg1 arg2 ienv)))
     :eq (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-eq arg1 arg2 ienv)))
     :ne (b* (((erp arg1) (peval-expr expr.arg1 ienv))
              ((erp arg2) (peval-expr expr.arg2 ienv)))
           (retok (peval-ne arg1 arg2 ienv)))
     :bitand (b* (((erp arg1) (peval-expr expr.arg1 ienv))
                  ((erp arg2) (peval-expr expr.arg2 ienv)))
               (peval-bitand arg1 arg2 ienv))
     :bitxor (b* (((erp arg1) (peval-expr expr.arg1 ienv))
                  ((erp arg2) (peval-expr expr.arg2 ienv)))
               (peval-bitxor arg1 arg2 ienv))
     :bitior (b* (((erp arg1) (peval-expr expr.arg1 ienv))
                  ((erp arg2) (peval-expr expr.arg2 ienv)))
               (peval-bitior arg1 arg2 ienv))
     :logand (b* (((erp arg1) (peval-expr expr.arg1 ienv))
                  ((when (= (pvalue->integer arg1) 0))
                   (retok (pvalue-signed 0)))
                  ((erp arg2) (peval-expr expr.arg2 ienv)))
               (if (= (pvalue->integer arg2) 0)
                   (retok (pvalue-signed 0))
                 (retok (pvalue-signed 1))))
     :logor (b* (((erp arg1) (peval-expr expr.arg1 ienv))
                 ((when (/= (pvalue->integer arg1) 0))
                  (retok (pvalue-signed 1)))
                 ((erp arg2) (peval-expr expr.arg2 ienv)))
              (if (= (pvalue->integer arg2) 0)
                  (retok (pvalue-signed 0))
                (retok (pvalue-signed 1))))
     :cond (b* (((erp test) (peval-expr expr.test ienv)))
             (if (= (pvalue->integer test) 0)
                 (peval-expr expr.else ienv)
               (peval-expr expr.then ienv)))))
  :measure (pexpr-count expr)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-first-token ((lexemes plexeme-listp))
  :returns (mv (token? plexeme-optionp)
               (lexemes-rest plexeme-listp))
  :short "Find the first token in a list of lexemes, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "We skip over comments and white space until we find a token.
     If we find no token, we return @('nil')."))
  (b* (((when (endp lexemes)) (mv nil nil))
       (lexeme (car lexemes))
       ((when (plexeme-tokenp lexeme))
        (mv (plexeme-fix lexeme) (plexeme-list-fix (cdr lexemes)))))
    (find-first-token (cdr lexemes)))

  ///

  (defret plexeme-tokenp-of-find-first-token
    (implies token?
             (plexeme-tokenp token?))
    :hints (("Goal" :induct t)))

  (defret len-of-find-first-token-uncond
    (<= (len lexemes-rest)
        (len lexemes))
    :rule-classes :linear
    :hints (("Goal" :induct t)))

  (defret len-of-fid-first-token-cond
    (implies token?
             (<= (len lexemes-rest)
                 (1- (len lexemes))))
    :rule-classes :linear
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pparse-expressions
  :short "Parse expressions during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The structure of these functions is similar to
     the ones in our @(see parser),
     but here they are simpler because the expressions are more limited.
     Refer to the grammar and to the documentation of those parser functions.")
   (xdoc::p
    "These functions parse a list of lexemes,
     returning the parsed expression and the rest of the lexemes,
     unless there is some error.")
   (xdoc::p
    "Since a constant expression is a conditional expression
     in the grammar [C17:6.6/1],
     and since we exclude assignment and comma expressions for now
     (see @(see preprocessor-evaluator)),
     the top-level function of this parser clique
     is the one for conditional expressions.")
   (xdoc::p
    "Since there are no cast and postfix expressions here,
     in the grammatical hierarchy of expressions,
     we skip them when they appear as sub-expressions in grammar rules,
     going directly to the ones below them in the hierarchy.")
   (xdoc::p
    "The only primary expressions that we parse are
     preprocessing numbers, character constants, identifiers,
     and parenthesized expressions.
     Identifiers are not in @(tsee pexpr),
     because as soon as we parse them,
     we turn them into the preprocessing number @('0') [C17:6.10.1/4]."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse an expression during preprocessing."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since a constant expression is a conditional expression
       in the grammar [C17:6.6/1],
       and since we exclude assignment and comma expressions for now
       (see @(see preprocessor-evaluator)),
       this function amounts to parsing a conditional expression.
       We introduce it for clarity and future extensibility."))
    (pparse-conditional-expression lexemes)
    :measure (two-nats-measure (len lexemes) 13))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-conditional-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a conditional expression during preproecessing."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we do not support GCC/Clang conditional expressions
       without a `then' sub-expression."))
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-logical-or-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok expr lexemes))
         ((when (not (plexeme-punctuatorp token "?"))) ; expr ?
          (retok expr (cons token lexemes))) ; expr
         (llen (len lexemes))
         ((erp expr2 lexemes) (pparse-expression lexemes)) ; expr ? expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         ((mv token lexemes) (find-first-token lexemes))
         ((unless (and token
                       (plexeme-punctuatorp token ":"))) ; expr ? expr :
          (reterr (msg "Expected colon, found ~@0."
                       (if token
                           (plexeme-to-msg token)
                         "no token"))))
         ((erp expr3 lexemes) ; expr ? expr : expr
          (pparse-conditional-expression lexemes)))
      (retok (make-pexpr-cond :test expr :then expr2 :else expr3) lexemes))
    :measure (two-nats-measure (len lexemes) 12))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-logical-or-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a logical disjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-logical-and-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-logical-or-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 11))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-logical-or-expression-rest ((prev-expr pexprp)
                                             (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a logical disjunction expression
            during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (plexeme-punctuatorp token "||")) ; prev-expr ||
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr || expr
          (pparse-logical-and-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (make-pexpr-logor :arg1 prev-expr :arg2 expr)))
      (pparse-logical-or-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-logical-and-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a logical conjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-inclusive-or-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-logical-and-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 10))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-logical-and-expression-rest ((prev-expr pexprp)
                                              (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a logical conjunction expression
            during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (plexeme-punctuatorp token "&&")) ; prev-expr &&
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr || expr
          (pparse-inclusive-or-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (make-pexpr-logand :arg1 prev-expr :arg2 expr)))
      (pparse-logical-and-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-inclusive-or-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse an inclusive disjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-exclusive-or-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-inclusive-or-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 9))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-inclusive-or-expression-rest ((prev-expr pexprp)
                                               (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of an inclusive disjunction expression
            during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (plexeme-punctuatorp token "|")) ; prev-expr |
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr | expr
          (pparse-exclusive-or-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (make-pexpr-bitior :arg1 prev-expr :arg2 expr)))
      (pparse-inclusive-or-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-exclusive-or-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse an exclusive disjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-and-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-exclusive-or-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 8))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-exclusive-or-expression-rest ((prev-expr pexprp)
                                               (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of an exclusive disjunction expression
            during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (plexeme-punctuatorp token "^")) ; prev-expr ^
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr | expr
          (pparse-and-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (make-pexpr-bitxor :arg1 prev-expr :arg2 expr)))
      (pparse-exclusive-or-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-and-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a conjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-equality-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-and-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 7))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-and-expression-rest ((prev-expr pexprp)
                                      (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a conjunction expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (plexeme-punctuatorp token "&")) ; prev-expr &
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr | expr
          (pparse-equality-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (make-pexpr-bitand :arg1 prev-expr :arg2 expr)))
      (pparse-and-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-equality-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse an equality expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-relational-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-equality-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 6))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-equality-expression-rest ((prev-expr pexprp)
                                           (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of an equality expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (or (plexeme-punctuatorp token "==") ; prev-expr ==
                      (plexeme-punctuatorp token "!="))) ; prev-expr !=
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr OP expr
          (pparse-relational-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (cond ((plexeme-punctuatorp token "==")
                           (make-pexpr-eq :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token "!=")
                           (make-pexpr-ne :arg1 prev-expr :arg2 expr))
                          (t (prog2$ (impossible) (irr-pexpr))))))
      (pparse-equality-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-relational-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a relational expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-shift-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-relational-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 5))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-relational-expression-rest ((prev-expr pexprp)
                                             (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a relational expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (or (plexeme-punctuatorp token "<") ; prev-expr <
                      (plexeme-punctuatorp token ">") ; prev-expr >
                      (plexeme-punctuatorp token "<=") ; prev-expr <=
                      (plexeme-punctuatorp token ">="))) ; prev-expr >=
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr OP expr
          (pparse-shift-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (cond ((plexeme-punctuatorp token "<")
                           (make-pexpr-lt :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token ">")
                           (make-pexpr-gt :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token "<=")
                           (make-pexpr-le :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token ">=")
                           (make-pexpr-ge :arg1 prev-expr :arg2 expr))
                          (t (prog2$ (impossible) (irr-pexpr))))))
      (pparse-relational-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-shift-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a shift expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-additive-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-shift-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 4))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-shift-expression-rest ((prev-expr pexprp)
                                        (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a shift expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (or (plexeme-punctuatorp token "<<") ; prev-expr <<
                      (plexeme-punctuatorp token ">>"))) ; prev-expr >>
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr OP expr
          (pparse-additive-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (cond ((plexeme-punctuatorp token "<<")
                           (make-pexpr-shl :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token ">>")
                           (make-pexpr-shr :arg1 prev-expr :arg2 expr))
                          (t (prog2$ (impossible) (irr-pexpr))))))
      (pparse-shift-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-additive-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse an additive expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-multiplicative-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-additive-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 3))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-additive-expression-rest ((prev-expr pexprp)
                                           (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of an additive expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (or (plexeme-punctuatorp token "+") ; prev-expr +
                      (plexeme-punctuatorp token "-"))) ; prev-expr -
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr OP expr
          (pparse-multiplicative-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (cond ((plexeme-punctuatorp token "+")
                           (make-pexpr-add :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token "-")
                           (make-pexpr-sub :arg1 prev-expr :arg2 expr))
                          (t (prog2$ (impossible) (irr-pexpr))))))
      (pparse-additive-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-multiplicative-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a multiplicative expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         (llen (len lexemes))
         ((erp expr lexemes) (pparse-unary-expression lexemes)) ; expr
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible)))
      (pparse-multiplicative-expression-rest expr lexemes))
    :measure (two-nats-measure (len lexemes) 2))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-multiplicative-expression-rest ((prev-expr pexprp)
                                                 (lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse the rest of a multiplicative expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil) ; prev-expr
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (retok (pexpr-fix prev-expr) lexemes))
         ((unless (or (plexeme-punctuatorp token "*") ; prev-expr *
                      (plexeme-punctuatorp token "/") ; prev-expr /
                      (plexeme-punctuatorp token "%"))) ; prev-expr %
          (retok (pexpr-fix prev-expr) (cons token lexemes))) ; prev-expr
         (llen (len lexemes))
         ((erp expr lexemes) ; prev-expr OP expr
          (pparse-unary-expression lexemes))
         ((unless (mbt (<= (len lexemes) (1- llen))))
          (reterr :impossible))
         (curr-expr (cond ((plexeme-punctuatorp token "*")
                           (make-pexpr-add :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token "/")
                           (make-pexpr-sub :arg1 prev-expr :arg2 expr))
                          ((plexeme-punctuatorp token "%")
                           (make-pexpr-sub :arg1 prev-expr :arg2 expr))
                          (t (prog2$ (impossible) (irr-pexpr))))))
      (pparse-multiplicative-expression-rest curr-expr lexemes))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-unary-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a unary expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (reterr (msg "Expected a unary operator ~
                        or a number ~
                        or a character constant ~
                        or an identifier ~
                        or an open parenthesis; ~
                        found nothing instead.")))
         ((when (or (plexeme-punctuatorp token "+") ; +
                    (plexeme-punctuatorp token "-") ; -
                    (plexeme-punctuatorp token "~") ; ~
                    (plexeme-punctuatorp token "!"))) ; !
          (b* (((erp expr lexemes) (pparse-unary-expression lexemes)) ; OP expr
               (expr (cond ((plexeme-punctuatorp token "+") (pexpr-plus expr))
                           ((plexeme-punctuatorp token "-") (pexpr-minus expr))
                           ((plexeme-punctuatorp token "~") (pexpr-bitnot expr))
                           ((plexeme-punctuatorp token "!") (pexpr-lognot expr))
                           (t (prog2$ (impossible) (irr-pexpr))))))
            (retok expr lexemes))))
      (pparse-primary-expression (cons token lexemes))) ; put back token
    :measure (two-nats-measure (len lexemes) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define pparse-primary-expression ((lexemes plexeme-listp))
    :returns (mv erp (expr pexprp) (lexemes-rest plexeme-listp))
    :parents (preprocessor-evaluator pparse-expressions)
    :short "Parse a primary expression during preprocessing."
    (b* (((reterr) (irr-pexpr) nil)
         ((mv token lexemes) (find-first-token lexemes))
         ((when (not token))
          (reterr (msg "Expected a number ~
                        or a character constant ~
                        or an identifier ~
                        or an open parenthesis; ~
                        found nothing instead."))))
      (cond
       ((plexeme-case token :number) ; number
        (retok (pexpr-number (plexeme-number->number token)) lexemes))
       ((plexeme-case token :char) ; char
        (retok (pexpr-char (plexeme-char->const token)) lexemes))
       ((plexeme-case token :ident) ; ident
        (retok (pexpr-number (pnumber-digit #\0)) lexemes))
       ((plexeme-punctuatorp token "(") ; (
        (b* (((erp expr lexemes) (pparse-expression lexemes)) ; ( expr
             ((mv token lexemes) (find-first-token lexemes))
             ((when (not token))
              (reterr (msg "Expected a closed parenthesis; ~
                            found nothing instead.")))
             ((unless (plexeme-punctuatorp token ")")) ; ( expr )
              (reterr (msg "Expected a closed parenthesis; ~
                            found ~@0 instead."
                           (plexeme-to-msg token)))))
          (retok expr lexemes)))
       (t ; OTHER
        (reterr (msg "Expected a number ~
                      or a character constant ~
                      or an identifier ~
                      or an open parenthesis; ~
                      found ~@0 instead."
                     (plexeme-to-msg token))))))
    :measure (two-nats-measure (len lexemes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual len-of-pparse-expressions-uncond
    (defret len-of-pparse-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-expression
      :rule-classes :linear)
    (defret len-of-pparse-conditional-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-conditional-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-conditional-expression lexemes))))
    (defret len-of-pparse-logical-or-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-logical-or-expression
      :rule-classes :linear)
    (defret len-of-pparse-logical-or-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-logical-or-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-logical-and-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-logical-and-expression
      :rule-classes :linear)
    (defret len-of-pparse-logical-and-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-logical-and-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-inclusive-or-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-inclusive-or-expression
      :rule-classes :linear)
    (defret len-of-pparse-inclusive-or-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-inclusive-or-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-exclusive-or-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-exclusive-or-expression
      :rule-classes :linear)
    (defret len-of-pparse-exclusive-or-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-exclusive-or-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-and-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-and-expression
      :rule-classes :linear)
    (defret len-of-pparse-and-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-and-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-equality-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-equality-expression
      :rule-classes :linear)
    (defret len-of-pparse-equality-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-equality-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-relational-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-relational-expression
      :rule-classes :linear)
    (defret len-of-pparse-relational-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-relational-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-shift-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-shift-expression
      :rule-classes :linear)
    (defret len-of-pparse-shift-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-shift-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-additive-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-additive-expression
      :rule-classes :linear)
    (defret len-of-pparse-additive-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-additive-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-multiplicative-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-multiplicative-expression
      :rule-classes :linear)
    (defret len-of-pparse-multiplicative-expression-rest-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-multiplicative-expression-rest
      :rule-classes :linear)
    (defret len-of-pparse-unary-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-unary-expression
      :rule-classes :linear)
    (defret len-of-pparse-primary-expression-uncond
      (<= (len lexemes-rest)
          (len lexemes))
      :fn pparse-primary-expression
      :rule-classes :linear))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual len-of-pparse-expressions-cond
    (defret len-of-pparse-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-expression
      :rule-classes :linear)
    (defret len-of-pparse-conditional-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-conditional-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-conditional-expression lexemes))))
    (defret len-of-pparse-logical-or-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-logical-or-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-logical-or-expression lexemes))))
    (defret len-of-pparse-logical-and-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-logical-and-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-logical-and-expression lexemes))))
    (defret len-of-pparse-inclusive-or-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-inclusive-or-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-inclusive-or-expression lexemes))))
    (defret len-of-pparse-exclusive-or-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-exclusive-or-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-exclusive-or-expression lexemes))))
    (defret len-of-pparse-and-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-and-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-and-expression lexemes))))
    (defret len-of-pparse-equality-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-equality-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-equality-expression lexemes))))
    (defret len-of-pparse-relational-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-relational-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-relational-expression lexemes))))
    (defret len-of-pparse-shift-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-shift-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-shift-expression lexemes))))
    (defret len-of-pparse-additive-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-additive-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-additive-expression lexemes))))
    (defret len-of-pparse-multiplicative-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-multiplicative-expression
      :rule-classes :linear
      :hints ('(:expand (pparse-multiplicative-expression lexemes))))
    (defret len-of-pparse-unary-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-unary-expression
      :rule-classes :linear)
    (defret len-of-pparse-primary-expression-cond
      (implies (not erp)
               (<= (len lexemes-rest)
                   (1- (len lexemes))))
      :fn pparse-primary-expression
      :rule-classes :linear)
    :skip-others t)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards pparse-conditional-expression)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual pparse-expressions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pparseval-const-expr ((lexemes plexeme-listp) (ienv ienvp))
  :returns (mv erp (pval pvaluep))
  :short "Parse and evaluate a constant expression during preprocessing."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for the expressions in @('#if') and @('#elif') directives.
     We parse the expression, obtaining an AST,
     and ensuring that there are no tokens left after the expression.
     Then we evaluate the AST, obtaining a preprocessor value."))
  (b* (((reterr) (irr-pvalue))
       ((erp expr lexemes) (pparse-expression lexemes))
       ((mv token lexemes) (find-first-token lexemes))
       ((when token)
        (reterr (msg "Found extra lexemes with tokens ~x0."
                     (cons token lexemes)))))
    (peval-expr expr ienv)))

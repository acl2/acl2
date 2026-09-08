; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-evaluator")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hash-conditional-evaluation
  :parents (abstract-syntax)
  :short "Evaluation of expressions used in conditional directives."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the expressions of fixtype @(tsee hash-if/elif-expr),
     i.e. the expressions used in the @('#if') and @('#elif') directives
     that our preprocessor and parser preserve into the ASTs.
     As noted in @(tsee hash-if/elif-expr),
     these are almost identical to @(tsee pexpr),
     except for the use of @(tsee iconst) instead of @(tsee pnumber).
     Expressions of type @(tsee pexpr) are evaluated
     via the code in @(see preprocessor-evaluator).
     We also need to evaluate expressions of type @(tsee hash-if/elif-expr),
     e.g. in the disambiguator and validator.
     To reuse the evaluation code in @(tsee preprocessor-evaluator),
     we convers from @(tsee hash-if/elif-expr) to @(tsee pexpr)
     and then we use that evaluation code.
     This is a bit ``backwards'',
     because we convert @(tsee iconst) to @(tsee pnumber),
     which the evaluator converts back to @(tsee iconst).
     So we should restructure the code to avoid this awkwardness,
     but for now what we are doing is functionally correct."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dec-const-to-pnumber ((value posp))
  :returns (number pnumberp)
  :short "Convert a decimal constant,
          represented as its positive integer value,
          to a preprocessing number."
  :long
  (xdoc::topstring
   (xdoc::p
    "We build the preprocessing number from the digits."))
  (b* ((value (lposfix value))
       ((when (< value 10)) (pnumber-digit (digit-to-char value))))
    (make-pnumber-number-digit
     :number (dec-const-to-pnumber (floor value 10))
     :squotep nil
     :digit (digit-to-char (mod value 10))))
  :measure (pos-fix value)
  :hints (("Goal" :in-theory (enable pos-fix)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable dec-digit-char-p digit-to-char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define oct-const-to-pnumber ((leading-zeros posp) (value natp))
  :returns (number pnumberp)
  :short "Convert an octal constant,
          represented as its positive number of leading zeros
          and as its non-negative integer value,
          to a preprocessing number."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first build the leading zeros,
     and then the additional digits if any."))
  (b* ((zeros (oct-const-to-pnumber-loop-leading-zeros leading-zeros)))
    (oct-const-to-pnumber-loop-value value zeros))

  :prepwork

  ((define oct-const-to-pnumber-loop-leading-zeros ((leading-zeros posp))
     :returns (number pnumberp)
     :parents nil
     (b* ((leading-zeros (lposfix leading-zeros))
          ((when (= leading-zeros 1)) (pnumber-digit #\0)))
       (make-pnumber-number-digit
        :number (oct-const-to-pnumber-loop-leading-zeros (1- leading-zeros))
        :squotep nil
        :digit #\0))
     :measure (pos-fix leading-zeros)
     :hints (("Goal" :in-theory (enable pos-fix)))
     :verify-guards :after-returns
     :guard-hints (("Goal" :in-theory (enable posp))))

   (define oct-const-to-pnumber-loop-value ((value natp) (number pnumberp))
     :returns (number1 pnumberp)
     :parents nil
     (b* (((when (zp value)) (pnumber-fix number)))
       (make-pnumber-number-digit
        :number (oct-const-to-pnumber-loop-value (floor value 8) number)
        :squotep nil
        :digit (digit-to-char (mod value 8))))
     :measure (nfix value)
     :verify-guards :after-returns
     :guard-hints (("Goal" :in-theory (enable dec-digit-char-p digit-to-char)))
     ;; The following is to prove the fixing theorems.
     :prepwork ((local (in-theory (enable nfix)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hex-const-to-pnumber ((prefix hprefixp) (digits hex-digit-char-listp))
  :returns (pnumber pnumberp)
  :short "Convert a hexadecimal constant,
          represented as its prefix and its digits,
          to a preprocessing number."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first build the prefix,
     and then we add the digits."))
  (b* ((zero (pnumber-digit #\0))
       (zero+x
        (hprefix-case
         prefix
         :locase-0x (make-pnumber-number-nondigit
                     :number zero
                     :squotep nil
                     :nondigit #\x)
         :upcase-0x (make-pnumber-number-nondigit
                     :number zero
                     :squotep nil
                     :nondigit #\X))))
    (hex-const-to-pnumber-loop digits zero+x))
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p)))

  :prepwork
  ((define hex-const-to-pnumber-loop ((digits hex-digit-char-listp)
                                      (number pnumberp))
     :returns (number1 pnumberp)
     :parents nil
     (b* (((when (endp digits)) (pnumber-fix number))
          (digit (str::hex-digit-char-fix (car digits)))
          (number (if (dec-digit-char-p digit)
                      (make-pnumber-number-digit
                       :number number
                       :squotep nil
                       :digit digit)
                    (make-pnumber-number-nondigit
                     :number number
                     :squotep nil
                     :nondigit digit))))
       (hex-const-to-pnumber-loop (cdr digits) number))
     :guard-hints (("Goal" :in-theory (enable hex-digit-char-p
                                              dec-digit-char-p
                                              str::letter/uscore-char-p))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dec/oct/hex-const-to-pnumber ((const dec/oct/hex-constp))
  :returns (number pnumberp)
  :short "Convert a decimal, octal, or hexadecimal constant
          to a preprocessing number."
  (dec/oct/hex-const-case
   const
   :dec (dec-const-to-pnumber const.value)
   :oct (oct-const-to-pnumber const.leading-zeros const.value)
   :hex (hex-const-to-pnumber const.prefix const.digits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define usuffix-to-pnumber ((suffix usuffixp) (number pnumberp))
  :returns (number1 pnumberp)
  :short "Add an unsigned suffix to a preprocessing number."
  (usuffix-case
   suffix
   :locase-u (make-pnumber-number-nondigit
              :number number
              :squotep nil
              :nondigit #\u)
   :upcase-u (make-pnumber-number-nondigit
              :number number
              :squotep nil
              :nondigit #\U))
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lsuffix-to-pnumber ((suffix lsuffixp) (number pnumberp))
  :returns (number1 pnumberp)
  :short "Add a length suffix to a preprocessing number."
  (lsuffix-case
   suffix
   :locase-l (make-pnumber-number-nondigit
              :number number
              :squotep nil
              :nondigit #\l)
   :upcase-l (make-pnumber-number-nondigit
              :number number
              :squotep nil
              :nondigit #\L)
   :locase-ll (make-pnumber-number-nondigit
               :number (make-pnumber-number-nondigit
                        :number number
                        :squotep nil
                        :nondigit #\l)
               :squotep nil
               :nondigit #\l)
   :upcase-ll (make-pnumber-number-nondigit
               :number (make-pnumber-number-nondigit
                        :number number
                        :squotep nil
                        :nondigit #\L)
               :squotep nil
               :nondigit #\L))
  :guard-hints (("Goal" :in-theory (enable str::letter/uscore-char-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iconst-to-pnumber ((iconst iconstp))
  :returns (number pnumberp)
  :short "Convert an integer constant to a preprocessing number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the awkward part discussed in @(see hash-conditional-evaluation),
     but there is nothing functionally incorrect about this conversion.")
   (xdoc::p
    "First we convert the code, then we add the suffix if needed."))
  (b* (((iconst iconst) iconst)
       (number (dec/oct/hex-const-to-pnumber iconst.core))
       ((unless iconst.suffix?) number))
    (isuffix-case
     iconst.suffix?
     :u (usuffix-to-pnumber iconst.suffix?.unsigned number)
     :l (lsuffix-to-pnumber iconst.suffix?.length number)
     :ul (lsuffix-to-pnumber iconst.suffix?.length
                             (usuffix-to-pnumber iconst.suffix?.unsigned
                                                 number))
     :lu (usuffix-to-pnumber iconst.suffix?.unsigned
                             (lsuffix-to-pnumber iconst.suffix?.length
                                                 number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash-if/elif-expr-to-pexpr ((expr hash-if/elif-exprp))
  :returns (pexpr pexprp)
  :short "Convert from @(tsee hash-if/elif-expr) to @(tsee pexpr)."
  (hash-if/elif-expr-case
   expr
   :number (pexpr-number (iconst-to-pnumber expr.number))
   :char (pexpr-char expr.char)
   :paren (pexpr-paren (hash-if/elif-expr-to-pexpr expr.inner))
   :plus (pexpr-plus (hash-if/elif-expr-to-pexpr expr.arg))
   :minus (pexpr-minus (hash-if/elif-expr-to-pexpr expr.arg))
   :bitnot (pexpr-bitnot (hash-if/elif-expr-to-pexpr expr.arg))
   :lognot (pexpr-lognot (hash-if/elif-expr-to-pexpr expr.arg))
   :mul (pexpr-mul (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :div (pexpr-div (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :rem (pexpr-rem (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :add (pexpr-add (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :sub (pexpr-sub (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :shl (pexpr-shl (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :shr (pexpr-shr (hash-if/elif-expr-to-pexpr expr.arg1)
                   (hash-if/elif-expr-to-pexpr expr.arg2))
   :lt (pexpr-lt (hash-if/elif-expr-to-pexpr expr.arg1)
                 (hash-if/elif-expr-to-pexpr expr.arg2))
   :gt (pexpr-gt (hash-if/elif-expr-to-pexpr expr.arg1)
                 (hash-if/elif-expr-to-pexpr expr.arg2))
   :le (pexpr-le (hash-if/elif-expr-to-pexpr expr.arg1)
                 (hash-if/elif-expr-to-pexpr expr.arg2))
   :ge (pexpr-ge (hash-if/elif-expr-to-pexpr expr.arg1)
                 (hash-if/elif-expr-to-pexpr expr.arg2))
   :eq (pexpr-eq (hash-if/elif-expr-to-pexpr expr.arg1)
                 (hash-if/elif-expr-to-pexpr expr.arg2))
   :ne (pexpr-mul (hash-if/elif-expr-to-pexpr expr.arg1)
                  (hash-if/elif-expr-to-pexpr expr.arg2))
   :bitand (pexpr-bitand (hash-if/elif-expr-to-pexpr expr.arg1)
                         (hash-if/elif-expr-to-pexpr expr.arg2))
   :bitxor (pexpr-bitxor (hash-if/elif-expr-to-pexpr expr.arg1)
                         (hash-if/elif-expr-to-pexpr expr.arg2))
   :bitior (pexpr-bitior (hash-if/elif-expr-to-pexpr expr.arg1)
                         (hash-if/elif-expr-to-pexpr expr.arg2))
   :logand (pexpr-logand (hash-if/elif-expr-to-pexpr expr.arg1)
                         (hash-if/elif-expr-to-pexpr expr.arg2))
   :logor (pexpr-logor (hash-if/elif-expr-to-pexpr expr.arg1)
                       (hash-if/elif-expr-to-pexpr expr.arg2))
   :cond (pexpr-cond (hash-if/elif-expr-to-pexpr expr.test)
                     (hash-if/elif-expr-to-pexpr expr.then)
                     (hash-if/elif-expr-to-pexpr expr.else))
   :defined (b* ((string (ident->unwrap expr.name))
                 ((unless (stringp string))
                  (raise "Internal error: identifier ~x0." expr.name)
                  (irr-pexpr)))
              (pexpr-defined string)))
  :no-function nil
  :measure (hash-if/elif-expr-count expr)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hash-if/elif-expr ((expr hash-if/elif-exprp)
                                (macros macro-tablep)
                                (ienv ienvp))
  :returns (mv erp
               (result integerp :rule-classes (:rewrite :type-prescription)))
  :short "Evaluate an expression in @('#if') or @('#elif')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert to @(tsee pexpr) and reuse its evaluator.
     This function also depends on
     the macro table and the implementation environment.
     We extract the integer from the @(tsee pvalue)."))
  (b* (((reterr) 0)
       ((erp pval) (peval-expr (hash-if/elif-expr-to-pexpr expr) macros ienv)))
    (retok (pvalue-case
            pval
            :signed pval.integer
            :unsigned pval.integer))))

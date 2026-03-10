; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-lexemes")
(include-book "abstract-syntax-irrelevants")

(include-book "../language/punctuators")

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ token-concatenation
  :parents (preprocessor)
  :short "Concatenation of tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('##') operator concatenates preprocessing tokens [C17:6.10.3.3].
     This is well-defined only for some combinations of tokens;
     for the other combinations, the behavior is undefined [C17:6.10.3.3/3].
     We use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to return an error if the concatenation is not well-defined."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-idents ((ident1 identp) (ident2 identp))
  :returns (ident identp)
  :short "Concatenate two identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always well-defined,
     because the characters that can start an identifer
     are a subset of the characters that can continue it:
     thus, the second identifier forms
     an acceptable extension of the first one.")
   (xdoc::p
    "Currently our preprocessor produces identifiers
     that consist of (wrapped) ACL2 strings.
     So we unwrap, concatenate, and re-wrap.")
   (xdoc::p
    "The type @(tsee ident) does not enforce ACL2 strings,
     so we need to double-check this here,
     and we throw a hard error if the check fails (which should not happen).
     We should strengthen the guard at some point."))
  (b* ((string1 (ident->unwrap ident1))
       (string2 (ident->unwrap ident2))
       ((unless (stringp string1))
        (raise "Internal error: non-string identifier ~x0." string1)
        (irr-ident))
       ((unless (stringp string2))
        (raise "Internal error: non-string identifier ~x0." string2)
        (irr-ident))
       (string (str::cat string1 string2)))
    (ident string))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-pnumbers ((number1 pnumberp) (number2 pnumberp))
  :returns (number pnumberp)
  :short "Concatenate two preprocessing numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always well-defined:
     the second number may start with a digit,
     which is a valid extension of the first number,
     or it may start with a dot,
     which is also a valid extension of the first number,
     and then all the additional extensions of the second number
     are valid extensions of the combined number:
     see the grammar rule for preprocessing numbers.")
   (xdoc::p
    "Indeed, the fact that this function
     operates on ASTs of preprocessing numbers,
     and always returns an AST of that type,
     shows that the concatenation is always well-defined.")
   (xdoc::p
    "Given the recursive structure of the @(tsee pnumber) ASTs,
     this function recurses on the second number,
     decomposing it and re-adding its components to the first number."))
  (pnumber-case
   number2
   :digit (make-pnumber-number-digit :number number1 :digit number2.digit)
   :dot-digit (make-pnumber-number-digit :number (pnumber-number-dot number1)
                                         :digit number2.digit)
   :number-digit (make-pnumber-number-digit
                  :number (concatenate-pnumbers number1 number2.number)
                  :digit number2.digit)
   :number-nondigit (make-pnumber-number-nondigit
                     :number (concatenate-pnumbers number1 number2.number)
                     :nondigit number2.nondigit)
   :number-locase-e-sign (make-pnumber-number-locase-e-sign
                          :number (concatenate-pnumbers number1 number2.number)
                          :sign number2.sign)
   :number-upcase-e-sign (make-pnumber-number-upcase-e-sign
                          :number (concatenate-pnumbers number1 number2.number)
                          :sign number2.sign)
   :number-locase-p-sign (make-pnumber-number-locase-p-sign
                          :number (concatenate-pnumbers number1 number2.number)
                          :sign number2.sign)
   :number-upcase-p-sign (make-pnumber-number-upcase-p-sign
                          :number (concatenate-pnumbers number1 number2.number)
                          :sign number2.sign)
   :number-dot (pnumber-number-dot
                (concatenate-pnumbers number1 number2.number)))
  :measure (pnumber-count number2)
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-punctuators ((punct1 stringp)
                                 (punct2 stringp)
                                 (version c::versionp))
  :returns (mv erp (punct stringp))
  :short "Concatenate two punctuators."
  :long
  (xdoc::topstring
   (xdoc::p
    "In @(tsee plexeme), punctuators are represented as ACL2 strings;
     we have no fixtype for punctuators.
     So this function takes and returns strings.
     Without examining the two punctuators case by case,
     we concanate the strings and see whether the result is a punctuator,
     returning an error if it is not.")
   (xdoc::p
    "This function is parameterized over the C version,
     which affects the valid punctuators."))
  (b* (((reterr) "")
       (punct (str::cat punct1 punct2)))
    (if (member-equal punct (c::punctuators-for version))
        (retok punct)
      (reterr (msg "The concatenation of the punctuators ~s0 and ~s1 ~
                    yields the non-punctuator ~s2."
                   (str-fix punct1) (str-fix punct2) punct)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-ident-pnumber ((ident identp) (number pnumberp))
  :returns (mv erp (ident1 identp))
  :short "Concatenate an identifier and a preprocessing number,
          in that order."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is well-defined, and yields an identifier,
     exactly when the preprocessing number has no dots or signs,
     which are not valid characters in identifiers.
     The other characters that can appear in a preprocessing number,
     namely digits and nondigits, are valid in identifiers
     (after the first one, which comes from the original identifier).")
   (xdoc::p
    "The auxiliary function turns a preprocessing number
     into a list of ACL2 characters,
     returning an error if any of those characters
     would be dots or signs.
     The characters are accumulated in reverse,
     which fits with the recursion on the preprocessing number."))
  (b* (((reterr) (irr-ident))
       (ident-string (ident->unwrap ident))
       ((unless (stringp ident-string))
        (raise "Internal error: non-string identifier ~x0." ident-string)
        (reterr t))
       ((erp rev-number-chars) (concatenate-ident-pnumber-aux ident number))
       (number-string (str::implode (rev rev-number-chars))))
    (retok (ident (str::cat ident-string number-string))))
  :no-function nil

  :prepwork
  ((define concatenate-ident-pnumber-aux ((ident identp) (number pnumberp))
     :returns (mv erp (rev-chars character-listp))
     :parents nil
     (b* (((reterr) nil))
       (pnumber-case
        number
        :digit (retok (list number.digit))
        :dot-digit (reterr (msg "Cannot concatenate an identiifer ~x0 ~
                                 and a preprocessing number with dots ~x1."
                                (ident-fix ident) (pnumber-fix number)))
        :number-digit (b* (((erp rev-chars)
                            (concatenate-ident-pnumber-aux ident
                                                           number.number)))
                        (retok (cons number.digit rev-chars)))
        :number-nondigit (b* (((erp rev-chars)
                               (concatenate-ident-pnumber-aux ident
                                                              number.number)))
                           (retok (cons number.nondigit rev-chars)))
        :number-locase-e-sign (reterr
                               (msg "Cannot concatenate an identifier ~x0 ~
                                     and a prrprocessing number with signs ~x1."
                                    (ident-fix ident) (pnumber-fix number)))
        :number-upcase-e-sign (reterr
                               (msg "Cannot concatenate an identifier ~x0 ~
                                     and a prrprocessing number with signs ~x1."
                                    (ident-fix ident) (pnumber-fix number)))
        :number-locase-p-sign (reterr
                               (msg "Cannot concatenate an identifier ~x0 ~
                                     and a prrprocessing number with signs ~x1."
                                    (ident-fix ident) (pnumber-fix number)))
        :number-upcase-p-sign (reterr
                               (msg "Cannot concatenate an identifier ~x0 ~
                                     and a prrprocessing number with signs ~x1."
                                    (ident-fix ident) (pnumber-fix number)))
        :number-dot (reterr (msg "Cannot concatenate an identiifer ~x0 ~
                                  and a preprocessing number with dots ~x1."
                                 (ident-fix ident) (pnumber-fix number)))))
     :measure (pnumber-count number))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-pnumber-ident ((number pnumberp) (ident identp))
  :returns (number1 pnumberp)
  :short "Concatenate a preprocessing number and an identifier,
          in that order."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is always well-defined,
     because all the characters that can appear in identifers
     can also appear, in a non-starting position, in preprocessing numbers.
     The result is a preprocessing number.")
   (xdoc::p
    "The auxiliary recursive function adds the identifier's characters
     to the preprocessing number in reverse,
     which fits better with the recursive structure of
     the ASTs for preprocessing numbers."))
  (b* ((string (ident->unwrap ident))
       ((unless (stringp string))
        (raise "Internal error: non-string identifier ~x0." string)
        (irr-pnumber))
       (chars (str::explode string))
       (rev-chars (rev chars)))
    (concatenate-pnumber-ident-aux number rev-chars))
  :no-function nil

  :prepwork
  ((define concatenate-pnumber-ident-aux ((number pnumberp)
                                          (rev-chars character-listp))
     :returns (number1 pnumberp)
     :parents nil
     (b* (((when (endp rev-chars)) (pnumber-fix number))
          (char (char-fix (car rev-chars)))
          (number (concatenate-pnumber-ident-aux number (cdr rev-chars))))
       (cond ((str::letter/uscore-char-p char)
              (make-pnumber-number-nondigit :number number :nondigit char))
             ((str::dec-digit-char-p char)
              (make-pnumber-number-digit :number number :digit char))
             (t (prog2$
                 (raise "Internal error: character ~x0 in identifier." char)
                 (irr-pnumber)))))
     :no-function nil
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-tokens ((token1 plexemep)
                            (token2 plexemep)
                            (version c::versionp))
  :guard (and (plexeme-tokenp token1)
              (plexeme-tokenp token2))
  :returns (mv erp (token plexemep))
  :short "Concatenate two preprocessing tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "We can only concatenate
     two identifiers,
     two preprocessing numbers,
     two punctuators (under conditions),
     an identifier with a preprocessing number (under conditions),
     and a preprocessing number with an identifier.
     All other combinations do not yield tokens."))
  (b* (((reterr) (irr-plexeme)))
    (plexeme-case
     token1
     :ident (plexeme-case
             token2
             :ident (retok (plexeme-ident
                            (concatenate-idents token1.ident
                                                token2.ident)))
             :number (b* (((erp ident)
                           (concatenate-ident-pnumber token1.ident
                                                      token2.number)))
                       (retok (plexeme-ident ident)))
             :otherwise (reterr (msg "Cannot concatenate ~x0 and ~x1."
                                     (plexeme-fix token1)
                                     (plexeme-fix token2))))
     :number (plexeme-case
              token2
              :ident (retok (plexeme-number
                             (concatenate-pnumber-ident token1.number
                                                        token2.ident)))
              :number (retok (plexeme-number
                              (concatenate-pnumbers token1.number
                                                    token2.number)))
              :otherwise (reterr (msg "Cannot concatenate ~x0 and ~x1."
                                      (plexeme-fix token1)
                                      (plexeme-fix token2))))
     :punctuator (plexeme-case
                  token2
                  :punctuator (b* (((erp punctuator)
                                    (concatenate-punctuators
                                     token1.punctuator
                                     token2.punctuator
                                     version)))
                                (retok (plexeme-punctuator punctuator)))
                  :otherwise (reterr (msg "Cannot concatenate ~x0 and ~x1."
                                          (plexeme-fix token1)
                                          (plexeme-fix token2))))
     :otherwise (reterr (msg "Cannot concatenate ~x0 and ~x1."
                             (plexeme-fix token1)
                             (plexeme-fix token2)))))

  ///

  (more-returns
   (token plexeme-tokenp
          :hints (("Goal" :in-theory (enable plexeme-tokenp
                                             irr-plexeme))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-tokens/placemarkers ((token1? plexeme-optionp)
                                         (token2? plexeme-optionp)
                                         (version c::versionp))
  :guard (and (or (not token1?) (plexeme-tokenp token1?))
              (or (not token2?) (plexeme-tokenp token2?)))
  :returns (mv erp (token? plexeme-optionp))
  :short "Concatenate two tokens or placemarkers."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee replace-macro-args),
     we represent placemarkers [C17:6.10.3.3] as @('nil').")
   (xdoc::p
    "The concatenation of two placemarkers is a placemarker, i.e. @('nil').")
   (xdoc::p
    "The concatenation of a placemarker and a token (in any order)
     is the token, i.e. the placemarker disappears.")
   (xdoc::p
    "The concatenation of two tokens is
     as defined by @(tsee concatenate-tokens)."))
  (b* (((reterr) nil))
    (plexeme-option-case
     token1?
     :some (plexeme-option-case
            token2?
            :some (concatenate-tokens token1?.val token2?.val version)
            :none (retok (plexeme-option-fix token1?)))
     :none (retok (plexeme-option-fix token2?))))
  :guard-hints (("Goal" :in-theory (enable plexeme-option-some->val)))

  ///

  (defret plexeme-tokenp-of-concatenate-tokens/placemarkers
    (implies token?
             (plexeme-tokenp token?))
    :hyp (and (or (not token1?) (plexeme-tokenp token1?))
              (or (not token2?) (plexeme-tokenp token2?)))
    :hints (("Goal" :in-theory (enable plexeme-option-some->val))))

  (defret plexemep-of-concatenate-tokens/placemarkers-when-not-nil-arg
    (plexemep token?)
    :hyp (or token1? token2?)
    :hints (("Goal" :in-theory (enable concatenate-tokens/placemarkers))))

  (defret plexeme-tokenp-of-concatenate-tokens/placemarkers-when-not-nil-arg
    (plexeme-tokenp token?)
    :hyp (and (or token1? token2?)
              (or (not token1?) (plexeme-tokenp token1?))
              (or (not token2?) (plexeme-tokenp token2?)))
    :hints (("Goal" :in-theory (enable concatenate-tokens/placemarkers)))))

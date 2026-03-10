; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-states")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ stringization
  :parents (preprocessor)
  :short "Stringization of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('#') operator turns lexemes into string literals [C17:6.10.3.2].
     Here we define a family of functions to perform this conversion.")
   (xdoc::p
    "The term `stringize' is used in [C17],
     although not in [C17:6.10.3.2].")
   (xdoc::p
    "In general, stringization may be applied to lexmarks,
     as they result from macro replacements.
     The markers themselves are not stringized,
     but we still need to handle them with respect to the disabled multiset."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-achar ((achar characterp))
  :returns (schars s-char-listp)
  :short "Stringize an ACL2 character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only for the ACL2 characters
     that form identifiers, preprocessing numbers, and punctuators,
     so they are all ASCII,
     and they do not include (single or double) quotes or backslashes.
     Thus, the mapping is one to one,
     but we return a list for flexibility,
     so that future extensions may return more @(tsee s-char) values."))
  (list (s-char-char (char-code achar))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-achars ((achars character-listp))
  :returns (schars s-char-listp)
  :short "Stringize a list of ACL2 characters."
  (cond ((endp achars) nil)
        (t (append (stringize-achar (car achars))
                   (stringize-achars (cdr achars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-astring ((astring stringp))
  :returns (schars s-char-listp)
  :short "Stringize an ACL2 string."
  (stringize-achars (str::explode astring)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-pnumber ((number pnumberp))
  :returns (schars s-char-listp)
  :short "Stringize a preprocessing number."
  (pnumber-case
   number
   :digit (stringize-achar number.digit)
   :dot-digit (stringize-achars (list #\. number.digit))
   :number-digit (append (stringize-pnumber number.number)
                         (stringize-achar number.digit))
   :number-nondigit (append (stringize-pnumber number.number)
                            (stringize-achar number.nondigit))
   :number-locase-e-sign (append (stringize-pnumber number.number)
                                 (stringize-achar #\e)
                                 (stringize-achar (sign-case number.sign
                                                             :plus #\+
                                                             :minus #\-)))
   :number-upcase-e-sign (append (stringize-pnumber number.number)
                                 (stringize-achar #\E)
                                 (stringize-achar (sign-case number.sign
                                                             :plus #\+
                                                             :minus #\-)))
   :number-locase-p-sign (append (stringize-pnumber number.number)
                                 (stringize-achar #\p)
                                 (stringize-achar (sign-case number.sign
                                                             :plus #\+
                                                             :minus #\-)))
   :number-upcase-p-sign (append (stringize-pnumber number.number)
                                 (stringize-achar #\P)
                                 (stringize-achar (sign-case number.sign
                                                             :plus #\+
                                                             :minus #\-)))
   :number-dot (append (stringize-pnumber number.number)
                       (stringize-achar #\.)))
  :measure (pnumber-count number))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-simple-escape ((escape simple-escapep))
  :returns (schars s-char-listp)
  :short "Stringize a simple escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "A backslash is inserted before each backslash and double quote
     [C17:6.10.3.2]."))
  (append (stringize-achars (list #\\ #\\)) ; inserted backslash
          (simple-escape-case
           escape
           :squote (stringize-achar #\')
           :dquote (stringize-achars (list #\\ #\")) ; inserted backslash
           :qmark (stringize-achar #\?)
           :bslash (stringize-achars (list #\\ #\\)) ; inserted backslash
           :a (stringize-achar #\a)
           :b (stringize-achar #\b)
           :f (stringize-achar #\f)
           :n (stringize-achar #\n)
           :r (stringize-achar #\r)
           :t (stringize-achar #\t)
           :v (stringize-achar #\v)
           :percent (stringize-achar #\%))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-oct-escape ((escape oct-escapep))
  :returns (schars s-char-listp)
  :short "Stringize an octal escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "A backslash is inserted before the initial backslash [C17:6.10.3.2]."))
  (append (stringize-achars (list #\\ #\\)) ; inserted backslash
          (oct-escape-case
           escape
           :one (stringize-achar escape.digit)
           :two (stringize-achars (list escape.digit1
                                        escape.digit2))
           :three (stringize-achars (list escape.digit1
                                          escape.digit2
                                          escape.digit3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-hex-quad ((quad hex-quad-p))
  :returns (schars s-char-listp)
  :short "Stringize a quadruple of hexadecimal digits."
  (b* (((hex-quad quad) quad))
    (stringize-achars (list quad.1st quad.2nd quad.3rd quad.4th))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-univ-char-name ((uchar univ-char-name-p))
  :returns (schars s-char-listp)
  :short "Stringize a universal character name."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.10.3.2/2] says that it is implementation-defined whether
     a backslash is inserted before a universal character name.
     For now we always add it."))
  (append (stringize-achars (list #\\ #\\)) ; inserted backslash
          (univ-char-name-case
           uchar
           :locase-u (append (stringize-achar #\u)
                             (stringize-hex-quad uchar.quad))
           :upcase-u (append (stringize-achar #\U)
                             (stringize-hex-quad uchar.quad1)
                             (stringize-hex-quad uchar.quad2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-escape ((escape escapep))
  :returns (schars s-char-listp)
  :short "Stringize an escape."
  (escape-case escape
               :simple (stringize-simple-escape escape.escape)
               :oct (stringize-oct-escape escape.escape)
               :hex (stringize-achars escape.escape)
               :univ (stringize-univ-char-name escape.escape))
  :guard-hints
  (("Goal" :in-theory (enable str::character-listp-when-hex-digit-char-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-c-char ((cchar c-char-p))
  :returns (schars s-char-listp)
  :short "Stringize a character or escape sequence in character constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "A backslash is inserted before backslash and double quote
     [C17:6.10.3.2]."))
  (c-char-case
   cchar
   :char (cond ((= cchar.code (char-code #\\))
                (append (stringize-achars (list #\\ #\\))))
               ((= cchar.code (char-code #\"))
                (append (stringize-achars (list #\\ #\"))))
               (t (list (s-char-char cchar.code))))
   :escape (stringize-escape cchar.escape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-c-char-list ((cchars c-char-listp))
  :returns (schars s-char-listp)
  :short "Stringize a list of character and escape sequences
          in character constants."
  (cond ((endp cchars) nil)
        (t (append (stringize-c-char (car cchars))
                   (stringize-c-char-list (cdr cchars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-cprefix ((prefix cprefixp))
  :returns (schars s-char-listp)
  :short "Stringize a prefix of character constants."
  (stringize-achar (cprefix-case prefix
                                 :upcase-l #\L
                                 :locase-u #\u
                                 :upcase-u #\U)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-cprefix-option ((prefix? cprefix-optionp))
  :returns (schars s-char-listp)
  :short "Stringize an optional prefix of character constants."
  (cprefix-option-case prefix?
                       :some (stringize-cprefix prefix?.val)
                       :none nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-cconst ((cconst cconstp))
  :returns (schars s-char-listp)
  :short "Stringize a character constant."
  (b* (((cconst cconst) cconst))
    (append (stringize-cprefix-option cconst.prefix?)
            (stringize-achar #\')
            (stringize-c-char-list cconst.cchars)
            (stringize-achar #\'))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-s-char ((schar s-char-p))
  :returns (schars s-char-listp)
  :short "Stringize a character or escape sequence in string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "A backslash is inserted before backslash and double quote
     [C17:6.10.3.2]."))
  (s-char-case
   schar
   :char (cond ((= schar.code (char-code #\\))
                (append (stringize-achars (list #\\ #\\))))
               ((= schar.code (char-code #\"))
                (append (stringize-achars (list #\\ #\"))))
               (t (list (s-char-char schar.code))))
   :escape (stringize-escape schar.escape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-s-char-list ((schars s-char-listp))
  :returns (schars1 s-char-listp)
  :short "Stringize a list of character and escape sequences
          in string literals."
  (cond ((endp schars) nil)
        (t (append (stringize-s-char (car schars))
                   (stringize-s-char-list (cdr schars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-eprefix ((prefix eprefixp))
  :returns (schars s-char-listp)
  :short "Stringize an encoding prefix."
  (eprefix-case prefix
                :locase-u8 (stringize-achars (list #\u #\8))
                :locase-u (stringize-achar #\u)
                :upcase-u (stringize-achar #\U)
                :upcase-l (stringize-achar #\L)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-eprefix-option ((prefix? eprefix-optionp))
  :returns (schars s-char-listp)
  :short "Stringize an optional encoding prefix."
  (eprefix-option-case prefix?
                       :some (stringize-eprefix prefix?.val)
                       :none nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-stringlit ((stringlit stringlitp))
  :returns (schars s-char-listp)
  :short "Stringize a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add a backslash before the opening and closing double quotes
     [C17:6.10.3.2/3]."))
  (b* (((stringlit stringlit) stringlit))
    (append (stringize-eprefix-option stringlit.prefix?)
            (stringize-achars (list #\\ #\")) ; inserted backslash
            (stringize-s-char-list stringlit.schars)
            (stringize-achars (list #\\ #\"))))) ; inserted backslash

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-lexeme ((lexeme plexemep))
  :returns (schars s-char-listp)
  :short "Stringize a lexeme."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only called on
     identifiers,
     preprocessing numbers,
     character constants,
     string literals,
     punctuators,
     other (non-header-name) tokens,
     and (single) spaces.
     We throw an error if called on
     a header name
     or a comment
     or a white space that is not a single space;
     but this should never happen."))
  (plexeme-case
   lexeme
   :header (raise "Internal error: header name ~x0." (plexeme-fix lexeme))
   :ident (b* ((astring (ident->unwrap lexeme.ident))
               ((unless (stringp astring))
                (raise "Internal error: non-string ~x0 in identifier."
                       astring)))
            (stringize-astring astring))
   :number (stringize-pnumber lexeme.number)
   :char (stringize-cconst lexeme.const)
   :string (stringize-stringlit lexeme.literal)
   :punctuator (stringize-astring lexeme.punctuator)
   :other (list (s-char-char lexeme.char))
   :block-comment (raise "Internal error: block comment ~x0."
                         (plexeme-fix lexeme))
   :line-comment (raise "Internal error: line comment ~x0."
                        (plexeme-fix lexeme))
   :newline (raise "Internal error: new line ~x0." (plexeme-fix lexeme))
   :spaces (if (= lexeme.count 1)
               (list (s-char-char 32))
             (raise "Internal error: multiple ~x0 spaces." lexeme.count))
   :horizontal-tab (raise "Internal error: horizontal tab.")
   :vertical-tab (raise "Internal error: vertical tab.")
   :form-feed (raise "Internal error: form feed."))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize-lexeme-list ((lexemes plexeme-listp))
  :returns (schars s-char-listp)
  :short "Stringize a list of lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We concatenate all the stringizations.")
   (xdoc::p
    "This is not actually used in @(tsee stringize),
     which operates on lexmarks,
     but it is useful to have for other purposes."))
  (cond ((endp lexemes) nil)
        (t (append (stringize-lexeme (car lexemes))
                   (stringize-lexeme-list (cdr lexemes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stringize ((lexmarks lexmark-listp))
  :returns (mv (stringlit stringlitp) (markers lexmark-listp))
  :short "Stringize the lexemes in a list of lexmarks,
          collecting the markers in a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our preprocessor, the @('#') operator may be applied
     to a macro argument that contains markers,
     resulting from the expansion of other macros.
     Although direct arguments of the macro that contains @('#')
     do not get expanded [C17:6.10.3.1],
     indirect arguments may be expanded, e.g. given")
   (xdoc::codeblock
    "#define F(x) # x"
    "#define G(x) F(x)"
    "#define M a b c")
   (xdoc::p
    "the macro call @('G(M)')
     expands to @('F(start(M) a b c end(M))'),
     where we are showing the markers @('start(M)') and @('end(M)'),
     which then expands to @('\"a b c\"'),
     but note that that the markers are passed,
     along with the lexemes between them, to the @('#') operator.")
   (xdoc::p
    "The markers are not stringized, but must not lose them.
     So we collect them as we go through the lexemes we stringize,
     and return all the markers in a separate list.")
   (xdoc::p
    "The characters obtained by stringizing the lexemes
     are concatenated all together,
     and then wrapper into a string literal.
     The string literal has no encoding prefix,
     because the term `character string literal' in [C17:6.10.3.2/2]
     denotes a string literal without prefix,
     as opposed to `UTF-8 string literals' and `wide string literals'
     [C17:6.4.5/3]."))
  (b* (((mv schars markers) (stringize-loop lexmarks)))
    (mv (make-stringlit :prefix? nil :schars schars)
        markers))

  :prepwork
  ((define stringize-loop ((lexmarks lexmark-listp))
     :returns (mv (schars s-char-listp) (markers lexmark-listp))
     :parents nil
     (b* (((when (endp lexmarks)) (mv nil nil))
          (lexmark (car lexmarks))
          ((mv schars markers) (stringize-loop (cdr lexmarks))))
       (if (lexmark-case lexmark :lexeme)
           (mv (append (stringize-lexeme (lexmark-lexeme->lexeme lexmark))
                       schars)
               markers)
         (mv schars (cons (lexmark-fix lexmark) markers)))))))

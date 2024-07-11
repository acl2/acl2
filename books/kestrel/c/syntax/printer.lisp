; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")
(include-book "concrete-syntax")

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ printer
  :parents (syntax-for-tools)
  :short "A printer of C from the abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a (pretty-)printer that turns our "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " into C code, according to "
    (xdoc::seetopic "concrete-syntax" "our concrete syntax formulation")
    ". This printer is relatively simple initially,
     but we will make it more feature-rich in the future.")
   (xdoc::p
    "Our abstract syntax is broader than the concrete syntax,
     in the sense that it represents more constructs
     than allowed by the concrete syntax.
     For instance, identifiers in the abstract syntax can be anything
     (for the reasons explained in @(tsee ident)),
     but they follow certain restrictions in the concrete syntax.
     We plan to define, and use in the printer as guards,
     predicates over the abstract syntax that check whether
     the abstract syntax conforms to the concrete syntax.
     For now, we use run-time checks, where needed,
     to ensure that the abstract syntax matches the concrete syntax;
     in some cases we actually use weaker checks.
     If these run-time checks fail, we throw hard errors,
     which is not ideal in general,
     but we want to keep the printing functions's inputs and outputs
     simpler, without using "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " or other forms (like "
    (xdoc::seetopic "acl2::error-triple" "error triples")
    ") needed for non-hard errors.
     After all, a printer is not supposed to fail,
     and once we have the aforementioned guards, it will never fail.
     For now, we can regard calls to the printer
     with non-compliant abstract syntax a form of internal error,
     for which hard errors are generally appropriate.
     But we use the term `misusage error' in the hard error messages,
     to reflect the fact that the printer is being misused in some sense,
     as opposed to an `internal error' which is generally used for
     situations are due to some proper implementation error."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pristate
  :short "Fixtype of printer states."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our printing functions take and return printer states.")
   (xdoc::p
    "The main content of a printer state is
     the bytes that form (the data of) the file being printed,
     in reverse order, which makes extending the data more efficent
     (by @(tsee cons)ing).")
   (xdoc::p
    "We also keep track of the current indentation level,
     as a natural number starting from 0 (where 0 means left margin).
     This is used to print indented code, as typical.")
   (xdoc::p
    "We also keep track of the size of each identation level,
     as a positive integer that indicates the number of spaces
     for a single indentation level.
     This does not change in the course of the printing,
     but it is convenient to keep it in the printing state,
     to avoid passing it around as an extra parameter.
     It is set when the printing state is initially created and never changes.")
   (xdoc::p
    "In the future, we may make printer states richer,
     in order to support more elaborate printing strategies,
     e.g. involving a specified maximum number of columns,
     for which the printing state would need to keep track of
     the current number of columns and other information.")
   (xdoc::p
    "We could look into turning the printer state into a stobj in the future,
     if efficiency is an issue."))
  ((bytes-rev byte-list)
   (indent-level nat)
   (indent-size pos))
  :pred pristatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-pristate ((indent-size posp))
  :returns (pstate pristatep)
  :short "Initial printer state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the size of the indentation,
     because that is an option that must be provided externally.")
   (xdoc::p
    "Initially, no data has been printed, and the indentation level is 0."))
  (make-pristate :bytes-rev nil
                 :indent-level 0
                 :indent-size indent-size))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define inc-pristate-indent ((pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Increase the printer state's indentation level by one."
  (change-pristate pstate :indent-level (1+ (pristate->indent-level pstate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dec-pristate-indent ((pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Decrease the printer state's indentation level by one."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that the current indentation level is not 0,
     throwing a hard error if that happens
     (which would make the level negative when decremented).
     This is an internal error: it should never happen,
     but if it may happen if there is a bug in our printer."))
  (b* ((indent-level (pristate->indent-level pstate))
       ((when (= indent-level 0))
        (raise "Internal error: ~
                attempting to decrease a zero indentation level.")
        (pristate-fix pstate)))
    (change-pristate pstate :indent-level (1- indent-level)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-char ((char natp) (pstate pristatep))
  :guard (grammar-character-p char)
  :returns (new-pstate pristatep)
  :short "Print a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We UTF-8-encode the character code into one, two, three, or four bytes.")
   (xdoc::p
    "This is the most basic printing function in our printer.
     All other printing functions call this one, directly or indirectly."))
  (b* ((bytes-rev (pristate->bytes-rev pstate))
       (encoding (cond
                  ((< char #x80) (list char))
                  ((< char #x800) (list (logior (ash char -6)
                                                #b11000000)
                                        (logior (logand char
                                                        #b00111111)
                                                #b10000000)))
                  ((< char #x10000) (list (logior (ash char -12)
                                                  #b11100000)
                                          (logior (logand (ash char -6)
                                                          #b00111111)
                                                  #b10000000)
                                          (logior (logand char
                                                          #b00111111)
                                                  #b10000000)))
                  (t (list (logior (ash char -18)
                                   #b11110000)
                           (logior (logand (ash char -12)
                                           #b00111111)
                                   #b10000000)
                           (logior (logand (ash char -6)
                                           #b00111111)
                                   #b10000000)
                           (logior (logand char
                                           #b00111111)
                                   #b10000000)))))
       (new-bytes-rev (append (rev encoding) bytes-rev))
       (new-pstate (change-pristate pstate :bytes-rev new-bytes-rev)))
    new-pstate)
  :guard-hints (("Goal" :in-theory (enable bytep grammar-character-p
                                           unsigned-byte-p
                                           integer-range-p)))
  ///
  (fty::deffixequiv print-char
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-chars ((chars nat-listp) (pstate pristatep))
  :guard (grammar-character-listp chars)
  :returns (new-pstate pristatep)
  :short "Print zero or more characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The characters are supplied in a list (of their codes).
     They are printed from left to right."))
  (b* (((when (endp chars)) (pristate-fix pstate))
       (pstate (print-char (car chars) pstate)))
    (print-chars (cdr chars) pstate))
  ///
  (fty::deffixequiv print-chars
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-new-line ((pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a new-line character."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we print a single line feed character, which has code 10.
     In the future, we could support a printer option
     for the kind of new line character to use.
     Our parser supports
     (i) line feeds,
     (ii) carriage returns, and
     (iii) line feeds immediately followed by carriage returns."))
  (print-char 10 pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-indent ((pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an indentation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be called at the beginning of a line,
     i.e. at the very beginning of printing
     (which will be a no-op, since the indentation level is initially 0),
     or after printing a new-line character.")
   (xdoc::p
    "We multiply the indentation level by the number of spaces for each level,
     and we print those many spaces (the code of the space character is 32).
     This is zero spaces, at indent level 0."))
  (b* (((pristate pstate) pstate)
       (spaces-to-print (* pstate.indent-level
                           pstate.indent-size)))
    (print-chars (repeat spaces-to-print 32) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-astring ((string stringp) (pstate pristatep))
  :guard (grammar-character-listp (acl2::string=>nats string))
  :returns (new-pstate pristatep)
  :short "Print the characters from an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "This provides the convenience to use use ACL2 strings,
     instead of using character codes.")
   (xdoc::p
    "Since most of the C syntax is ASCII,
     this printing function is used to print most of the code.")
   (xdoc::p
    "Note that an ACL2 string can contain characters that,
     when converted to natural numbers, are larger than 127,
     and therefore are not ASCII.
     But we always call this printing function with ASCII strings."))
  (print-chars (acl2::string=>nats string) pstate)
  ///
  (fty::deffixequiv print-astring
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-digit-achar ((achar dec-digit-char-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an ACL2 decimal digit character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself.")
   (xdoc::p
    "This is essentially the same code as
     @(tsee print-oct-digit-achar) and @(tsee print-hex-digit-achar),
     but it has a stronger guard than if we used
     a more general function to print an ACL2 character."))
  (print-char (char-code achar) pstate)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           dec-digit-char-p)))
  ///
  (fty::deffixequiv print-dec-digit-achar
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-digit-achars ((achars dec-digit-char-listp)
                                (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print zero or more ACL2 decimal digit characters."
  (b* (((when (endp achars)) (pristate-fix pstate))
       (pstate (print-dec-digit-achar (car achars) pstate)))
    (print-dec-digit-achars (cdr achars) pstate))
  ///
  (fty::deffixequiv print-dec-digit-achars
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-oct-digit-achar ((achar oct-digit-char-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an ACL2 octal digit character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself.")
   (xdoc::p
    "This is essentially the same code as
     @(tsee print-dec-digit-achar) and @(tsee print-hex-digit-achar),
     but it has a stronger guard than if we used
     a more general function to print an ACL2 character."))
  (print-char (char-code achar) pstate)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           oct-digit-char-p)))
  ///
  (fty::deffixequiv print-oct-digit-achar
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-oct-digit-achars ((achars oct-digit-char-listp)
                                (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print zero or more ACL2 octal digit characters."
  (b* (((when (endp achars)) (pristate-fix pstate))
       (pstate (print-oct-digit-achar (car achars) pstate)))
    (print-oct-digit-achars (cdr achars) pstate))
  ///
  (fty::deffixequiv print-oct-digit-achars
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hex-digit-achar ((achar hex-digit-char-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an ACL2 hexadecimal digit character."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the character into its code and print it.
     Note that we do not need the numeric value of the character;
     we just need to print the character itself.")
   (xdoc::p
    "This is essentially the same code as
     @(tsee print-dec-digit-achar) and @(tsee print-oct-digit-achar),
     but it has a stronger guard than if we used
     a more general function to print an ACL2 character."))
  (print-char (char-code achar) pstate)
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           hex-digit-char-p)))
  ///
  (fty::deffixequiv print-hex-digit-achar
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hex-digit-achars ((achars hex-digit-char-listp)
                                (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print zero or more ACL2 hexadecimal digit characters."
  (b* (((when (endp achars)) (pristate-fix pstate))
       (pstate (print-hex-digit-achar (car achars) pstate)))
    (print-hex-digit-achars (cdr achars) pstate))
  ///
  (fty::deffixequiv print-hex-digit-achars
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-ident ((ident identp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the identifier is a non-empty ACL2 string
     whose character codes are all valid in our C grammar.
     This way we can call @(tsee print-chars).")
   (xdoc::p
    "This is a weaker check than ensuring that the string
     is in fact a valid C identifier in our concrete syntax.
     We plan to strengthen this in the future."))
  (b* ((string? (ident->unwrap ident))
       ((unless (stringp string?))
        (raise "Misusage error: ~
                the identifier contains ~x0 instead of an ACL2 string."
               string?)
        (pristate-fix pstate))
       (chars (acl2::string=>nats string?))
       ((unless chars)
        (raise "Misusage error; ~
                the identifier is empty.")
        (pristate-fix pstate))
       ((unless (grammar-character-listp chars))
        (raise "Misusage error: ~
                the identifier consists of the character codes ~x0, ~
                not all of which are allowed by the ABNF grammar."
               chars)
        (pristate-fix pstate)))
    (print-chars chars pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-ident-list ((idents ident-listp) (pstate pristatep))
  :guard (consp idents)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more identifiers, separated by commas."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our abstract syntax, @(tsee ident-list) is used only
     in the @(':function-names') case of @(tsee dirdeclor),
     where the identifiers represent function parameter names,
     and so it is appropriate to print them separated by commas."))
  (b* (((unless (mbt (consp idents))) (pristate-fix pstate))
       (pstate (print-ident (car idents) pstate))
       ((when (endp (cdr idents))) pstate)
       (pstate (print-astring ", " pstate)))
    (print-ident-list (cdr idents) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-lsuffix ((lsuffix lsuffixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a length suffix."
  (lsuffix-case
   lsuffix
   :locase-l (print-astring "l" pstate)
   :upcase-l (print-astring "L" pstate)
   :locase-ll (print-astring "ll" pstate)
   :upcase-ll (print-astring "LL" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-usuffix ((usuffix usuffixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an unsigned suffix."
  (usuffix-case
   usuffix
   :locase-u (print-astring "u" pstate)
   :upcase-u (print-astring "U" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-isuffix ((isuffix isuffixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an integer suffix."
  (isuffix-case
   isuffix
   :u (print-usuffix isuffix.unsigned pstate)
   :l (print-lsuffix isuffix.length pstate)
   :ul (b* ((pstate (print-usuffix isuffix.unsigned pstate))
            (pstate (print-lsuffix isuffix.length pstate)))
         pstate)
   :lu (b* ((pstate (print-lsuffix isuffix.length pstate))
            (pstate (print-usuffix isuffix.unsigned pstate)))
         pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-isuffix-option ((isuffix? isuffix-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional integer suffix."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no suffix, we print nothing."))
  (isuffix-option-case
   isuffix?
   :some (print-isuffix isuffix?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hprefix ((hprefix hprefixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a hexadecimal prefix."
  (hprefix-case
   hprefix
   :locase-0x (print-astring "0x" pstate)
   :upcase-0x (print-astring "0X" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec/oct/hex-const ((dohconst dec/oct/hex-constp)
                                 (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a decimal, octal, or hexadecimal constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a decimal constant,
     the abstract syntax gives us the value (a positive integer),
     which we convert to ACL2 decimal digit characters,
     which we print.")
   (xdoc::p
    "For an octal constant,
     first we print the leading zeros.
     We convert the value, which is a non-negative integer,
     into octal digits, using an auxiliary function from the library
     that turns 0 into @('nil'), which is what we want,
     because the octal constant @('0') is represented as
     one leading zero and value zero.")
   (xdoc::p
    "For a hexadecimal constant,
     first we print the prefix.
     We ensure that there is at least one digit
     (otherwise it is not a syntactically valid hexadecimal constant),
     and we print them."))
  (dec/oct/hex-const-case
   dohconst
   :dec (print-dec-digit-achars (str::nat-to-dec-chars dohconst.value) pstate)
   :oct (b* ((pstate (print-oct-digit-achars
                      (repeat dohconst.leading-zeros #\0)
                      pstate))
             (pstate (print-oct-digit-achars
                      (str::nat-to-oct-chars-aux dohconst.value nil)
                      pstate)))
          pstate)
   :hex (b* (((unless dohconst.digits)
              (raise "Misusage error: ~
                      the hexadecimal constant has no digits.")
              (pristate-fix pstate))
             (pstate (print-hprefix dohconst.prefix pstate))
             (pstate (print-hex-digit-achars dohconst.digits pstate)))
          pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-iconst ((iconst iconstp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an integer constant."
  (b* (((iconst iconst) iconst)
       (pstate (print-dec/oct/hex-const iconst.dec/oct/hex pstate))
       (pstate (print-isuffix-option iconst.suffix? pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fsuffix ((fsuffix fsuffixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a floating suffix."
  (fsuffix-case
   fsuffix
   :locase-f (print-astring "f" pstate)
   :upcase-f (print-astring "F" pstate)
   :locase-l (print-astring "l" pstate)
   :upcase-l (print-astring "L" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fsuffix-option ((fsuffix? fsuffix-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional floating suffix."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no suffix, we print nothing."))
  (fsuffix-option-case
   fsuffix?
   :some (print-fsuffix fsuffix?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-sign ((sign signp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a sign."
  (sign-case
   sign
   :plus (print-astring "+" pstate)
   :minus (print-astring "-" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-sign-option ((sign? sign-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional sign."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no sign, we print nothing."))
  (sign-option-case
   sign?
   :some (print-sign sign?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-expo-prefix ((prefix dec-expo-prefixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a decimal exponent prefix."
  (dec-expo-prefix-case
   prefix
   :locase-e (print-astring "e" pstate)
   :upcase-e (print-astring "E" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-bin-expo-prefix ((prefix bin-expo-prefixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a binary exponent prefix."
  (bin-expo-prefix-case
   prefix
   :locase-p (print-astring "p" pstate)
   :upcase-p (print-astring "P" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-expo ((expo dec-expop) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a decimal exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one digit."))
  (b* (((dec-expo expo) expo)
       (pstate (print-dec-expo-prefix expo.prefix pstate))
       (pstate (print-sign-option expo.sign? pstate))
       ((unless expo.digits)
        (raise "Misusage error: ~
                the decimal exponent has no digits.")
        pstate)
       (pstate (print-dec-digit-achars expo.digits pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-expo-option ((expo? dec-expo-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional decimal exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no decimal exponent, we print nothing."))
  (dec-expo-option-case
   expo?
   :some (print-dec-expo expo?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-bin-expo ((expo bin-expop) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a binary exponent."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one digit."))
  (b* (((bin-expo expo) expo)
       (pstate (print-bin-expo-prefix expo.prefix pstate))
       (pstate (print-sign-option expo.sign? pstate))
       ((unless expo.digits)
        (raise "Misusage error: ~
                the binary exponent has no digits.")
        pstate)
       (pstate (print-dec-digit-achars expo.digits pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-frac-const ((dfconst dec-frac-constp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a decimal fractional constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one digit,
     before or after the fractional point."))
  (b* (((dec-frac-const dfconst) dfconst)
       ((unless (or dfconst.before
                    dfconst.after))
        (raise "Misusage error: ~
                the decimal fractional constant has no digits.")
        (pristate-fix pstate))
       (pstate (print-dec-digit-achars dfconst.before pstate))
       (pstate (print-astring "." pstate))
       (pstate (print-dec-digit-achars dfconst.after pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hex-frac-const ((hfconst hex-frac-constp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a hexadecimal fractional constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one digit,
     before or after the fractional point."))
  (b* (((hex-frac-const hfconst) hfconst)
       ((unless (or hfconst.before
                    hfconst.after))
        (raise "Misusage error: ~
                the hexadecimal fractional constant has no digits.")
        (pristate-fix pstate))
       (pstate (print-hex-digit-achars hfconst.before pstate))
       (pstate (print-astring "." pstate))
       (pstate (print-hex-digit-achars hfconst.after pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-dec-core-fconst ((fconst dec-core-fconstp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a decimal core floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For an integer one, we ensure that there is at least one digit.
     For a fractional one, the check is performed
     in @(tsee print-dec-frac-const)."))
  (dec-core-fconst-case
   fconst
   :frac (b* ((pstate (print-dec-frac-const fconst.significand pstate))
              (pstate (print-dec-expo-option fconst.expo? pstate)))
           pstate)
   :int (b* (((unless fconst.significand)
              (raise "Misusage error: ~
                      the integer decimal core floating constant ~
                      has no digits in the significand.")
              (pristate-fix pstate))
             (pstate (print-dec-digit-achars fconst.significand pstate))
             (pstate (print-dec-expo fconst.expo pstate)))
          pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hex-core-fconst ((fconst hex-core-fconstp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a hexadecimal core floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "For an integer one, we ensure that there is at least one digit.
     For a fractional one, the check is performed
     in @(tsee print-hex-frac-const)."))
  (hex-core-fconst-case
   fconst
   :frac (b* ((pstate (print-hex-frac-const fconst.significand pstate))
              (pstate (print-bin-expo fconst.expo pstate)))
           pstate)
   :int (b* (((unless fconst.significand)
              (raise "Misusage error: ~
                      the integer hexadecimal core floating constant ~
                      has no digits in the significand.")
              (pristate-fix pstate))
             (pstate (print-hex-digit-achars fconst.significand pstate))
             (pstate (print-bin-expo fconst.expo pstate)))
          pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fconst ((fconst fconstp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a floating constant."
  (fconst-case
   fconst
   :dec (b* ((pstate (print-dec-core-fconst fconst.core pstate))
             (pstate (print-fsuffix-option fconst.suffix? pstate)))
          pstate)
   :hex (b* ((pstate (print-hprefix fconst.prefix pstate))
             (pstate (print-hex-core-fconst fconst.core pstate))
             (pstate (print-fsuffix-option fconst.suffix? pstate)))
          pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-simple-escape ((esc simple-escapep) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a simple escape."
  (simple-escape-case
   esc
   :squote (print-astring "\\'" pstate)  ; \'
   :dquote (print-astring "\\\"" pstate) ; \"
   :qmark (print-astring "\\?" pstate)   ; \?
   :bslash (print-astring "\\\\" pstate) ; \\
   :a (print-astring "\\a" pstate)       ; \a
   :b (print-astring "\\b" pstate)       ; \b
   :f (print-astring "\\f" pstate)       ; \f
   :n (print-astring "\\n" pstate)       ; \n
   :r (print-astring "\\r" pstate)       ; \r
   :t (print-astring "\\t" pstate)       ; \t
   :v (print-astring "\\v" pstate))      ; \v
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-oct-escape ((esc oct-escapep) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an octal escape."
  (b* ((pstate (print-astring "\\" pstate))
       (pstate
        (oct-escape-case
         esc
         :one (print-oct-digit-achar esc.digit pstate)
         :two (b* ((pstate (print-oct-digit-achar esc.digit1 pstate))
                   (pstate (print-oct-digit-achar esc.digit2 pstate)))
                pstate)
         :three (b* ((pstate (print-oct-digit-achar esc.digit1 pstate))
                     (pstate (print-oct-digit-achar esc.digit2 pstate))
                     (pstate (print-oct-digit-achar esc.digit3 pstate)))
                  pstate))))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-hex-quad ((quad hex-quad-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a quadruple of hexadecimal digits."
  (b* (((hex-quad quad) quad)
       (pstate (print-hex-digit-achar quad.1st pstate))
       (pstate (print-hex-digit-achar quad.2nd pstate))
       (pstate (print-hex-digit-achar quad.3rd pstate))
       (pstate (print-hex-digit-achar quad.4th pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-univ-char-name ((ucname univ-char-name-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a universal character name."
  (univ-char-name-case
   ucname
   :locase-u (b* ((pstate (print-astring "\\u" pstate)) ; \u
                  (pstate (print-hex-quad ucname.quad pstate)))
               pstate)
   :upcase-u (b* ((pstate (print-astring "\\U" pstate)) ; \U
                  (pstate (print-hex-quad ucname.quad1 pstate))
                  (pstate (print-hex-quad ucname.quad2 pstate)))
               pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-escape ((esc escapep) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one digit
     in a hexadecimal escape sequence."))
  (escape-case
   esc
   :simple (print-simple-escape esc.unwrap pstate)
   :oct (print-oct-escape esc.unwrap pstate)
   :hex (b* ((pstate (print-astring "\\x" pstate)) ; \x
             ((unless esc.unwrap)
              (raise "Misusage error: ~
                      hexadecimal escape sequence has no digits.")
              pstate)
             (pstate (print-hex-digit-achars esc.unwrap pstate)))
          pstate)
   :univ (print-univ-char-name esc.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-c-char ((cchar c-char-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a character or escape sequence usable in character constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax puts no limitation on the character (code),
     but here we check that it satisfies
     the requirements in the concrete syntax.
     It must be a character in the grammar,
     and in addition it must not be
     a single quote, a backslash, or a new-line character.
     The latter check encompasses not only line feed, but also carriage return:
     recall that both are allowed in our grammar,
     and that we allow three kinds of new-line characters
     (line feed alone,
     carriage return alone,
     or line feed followed by carriage return)."))
  (c-char-case
   cchar
   :char (b* (((unless (and (grammar-character-p cchar.unwrap)
                            (not (= cchar.unwrap (char-code #\'))) ; '
                            (not (= cchar.unwrap (char-code #\\))) ; \
                            (not (= cchar.unwrap 10))              ; LF
                            (not (= cchar.unwrap 13))))            ; CR
               (raise "Misusage error: ~
                       the character code ~x0 is disallowed ~
                       in a character constant."
                      cchar.unwrap)
               (pristate-fix pstate)))
           (print-char cchar.unwrap pstate))
   :escape (print-escape cchar.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-c-char-list ((cchars c-char-listp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a list of zero or more characters or escape sequences
          usable in character constants."
  (b* (((when (endp cchars)) (pristate-fix pstate))
       (pstate (print-c-char (car cchars) pstate)))
    (print-c-char-list (cdr cchars) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-cprefix ((cprefix cprefixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a character constant prefix."
  (cprefix-case
   cprefix
   :upcase-l (print-astring "L" pstate)
   :locase-u (print-astring "u" pstate)
   :upcase-u (print-astring "U" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-cprefix-option ((cprefix? cprefix-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional character constant prefix."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no prefix, we print nothing."))
  (cprefix-option-case
   cprefix?
   :some (print-cprefix cprefix?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-cconst ((cconst cconstp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one character or escape sequence."))
  (b* (((cconst cconst) cconst)
       (pstate (print-cprefix-option cconst.prefix? pstate))
       (pstate (print-astring "'" pstate))
       ((unless cconst.cchars)
        (raise "Misusage error: ~
                the character constant has no characters or escape sequences.")
        pstate)
       (pstate (print-c-char-list cconst.cchars pstate))
       (pstate (print-astring "'" pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-const ((const constp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a constant."
  (const-case
   const
   :int (print-iconst const.unwrap pstate)
   :float (print-fconst const.unwrap pstate)
   :enum (print-ident const.unwrap pstate)
   :char (print-cconst const.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-s-char ((schar s-char-p) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a character or escape sequence usable in string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax puts no limitation on the character (code),
     but here we check that it satisfies
     the requirements in the concrete syntax.
     It must be a character in the grammar,
     and in addition it must not be
     a double quote, a backslash, or a new-line character.
     The latter check encompasses not only line feed, but also carriage return:
     recall that both are allowed in our grammar,
     and that we allow three kinds of new-line characters
     (line feed alone,
     carriage return alone,
     or line feed followed by carriage return)."))
  (s-char-case
   schar
   :char (b* (((unless (and (grammar-character-p schar.unwrap)
                            (not (= schar.unwrap (char-code #\"))) ; "
                            (not (= schar.unwrap (char-code #\\))) ; \
                            (not (= schar.unwrap 10))              ; LF
                            (not (= schar.unwrap 13))))            ; CR
               (raise "Misusage error: ~
                       the character code ~x0 is disallowed ~
                       in a string literal."
                      schar.unwrap)
               (pristate-fix pstate)))
           (print-char schar.unwrap pstate))
   :escape (print-escape schar.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-s-char-list ((schars s-char-listp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a list of zero or more characters or escape sequences
          usable in string-literals."
  (b* (((when (endp schars)) (pristate-fix pstate))
       (pstate (print-s-char (car schars) pstate)))
    (print-s-char-list (cdr schars) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-eprefix ((eprefix eprefixp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an encoding prefix."
  (eprefix-case
   eprefix
   :locase-u8 (print-astring "u8" pstate)
   :locase-u (print-astring "u" pstate)
   :upcase-u (print-astring "U" pstate)
   :upcase-l (print-astring "L" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-eprefix-option ((eprefix? eprefix-optionp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an optional encoding prefix."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no prefix, we print nothing."))
  (eprefix-option-case
   eprefix?
   :some (print-eprefix eprefix?.val pstate)
   :none (pristate-fix pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-stringlit ((stringlit stringlitp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one character or escape sequence."))
  (b* (((stringlit stringlit) stringlit)
       (pstate (print-eprefix-option stringlit.prefix? pstate))
       (pstate (print-astring "\"" pstate))
       ((unless stringlit.schars)
        (raise "Misusage error: ~
                the character constant has no characters or escape sequences.")
        pstate)
       (pstate (print-s-char-list stringlit.schars pstate))
       (pstate (print-astring "\"" pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-stringlit-list ((strings stringlit-listp) (pstate pristatep))
  :guard (consp strings)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more string literals, separated by spaces."
  (b* (((unless (mbt (consp strings))) (pristate-fix pstate))
       (pstate (print-stringlit (car strings) pstate))
       ((when (endp (cdr strings))) pstate)
       (pstate (print-astring " " pstate)))
    (print-stringlit-list (cdr strings) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-unop ((op unopp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a unary operator."
  (unop-case
   op
   :address (print-astring "&" pstate)
   :indir (print-astring "*" pstate)
   :plus (print-astring "+" pstate)
   :minus (print-astring "-" pstate)
   :bitnot (print-astring "~" pstate)
   :lognot (print-astring "!" pstate)
   :preinc (print-astring "++" pstate)
   :predec (print-astring "--" pstate)
   :postinc (print-astring "++" pstate)
   :postdec (print-astring "--" pstate)
   :sizeof (print-astring "sizeof" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-binop ((op binopp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a binary operator."
  (binop-case
   op
   :mul (print-astring "*" pstate)
   :div (print-astring "/" pstate)
   :rem (print-astring "%" pstate)
   :add (print-astring "+" pstate)
   :sub (print-astring "-" pstate)
   :shl (print-astring "<<" pstate)
   :shr (print-astring ">>" pstate)
   :lt (print-astring "<" pstate)
   :gt (print-astring ">" pstate)
   :le (print-astring "<=" pstate)
   :ge (print-astring ">=" pstate)
   :eq (print-astring "==" pstate)
   :ne (print-astring "!=" pstate)
   :bitand (print-astring "&" pstate)
   :bitxor (print-astring "^" pstate)
   :bitior (print-astring "|" pstate)
   :logand (print-astring "&&" pstate)
   :logor (print-astring "||" pstate)
   :asg (print-astring "=" pstate)
   :asg-mul (print-astring "*=" pstate)
   :asg-div (print-astring "/=" pstate)
   :asg-rem (print-astring "%=" pstate)
   :asg-add (print-astring "+=" pstate)
   :asg-sub (print-astring "-=" pstate)
   :asg-shl (print-astring "<<=" pstate)
   :asg-shr (print-astring ">>=" pstate)
   :asg-and (print-astring "&=" pstate)
   :asg-xor (print-astring "^=" pstate)
   :asg-ior (print-astring "|=" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-stoclaspec ((stoclaspec stoclaspecp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a storage class specifier."
  (stoclaspec-case
   stoclaspec
   :tydef (print-astring "typedef" pstate)
   :extern (print-astring "extern" pstate)
   :static (print-astring "static" pstate)
   :threadloc (print-astring "_Thread_local" pstate)
   :auto (print-astring "auto" pstate)
   :register (print-astring "register" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-tyqual ((tyqual tyqualp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a type qualifier."
  (tyqual-case
   tyqual
   :const (print-astring "const" pstate)
   :restrict (print-astring "restrict" pstate)
   :volatile (print-astring "volatile" pstate)
   :atomic (print-astring "_Atomic" pstate)
   ;; GCC extensions:
   :__restrict (print-astring "__restrict" pstate)
   :__restrict__ (print-astring "__restrict__" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-tyqual-list ((tyquals tyqual-listp) (pstate pristatep))
  :guard (consp tyquals)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more type qualifiers, separated by spaces."
  (b* (((unless (mbt (consp tyquals))) (pristate-fix pstate))
       (pstate (print-tyqual (car tyquals) pstate))
       ((when (endp (cdr tyquals))) pstate)
       (pstate (print-astring " " pstate)))
    (print-tyqual-list (cdr tyquals) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-tyqual-list-list ((tyqualss tyqual-list-listp) (pstate pristatep))
  :guard (consp tyqualss)
  :returns (new-pstate pristatep)
  :short "Print a list or one or more lists of type qualifiers,
          corresponding to a `pointer' in the grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax uses lists of lists of type qualifiers
     to model what the grammar calls `pointer',
     which is a sequence of one or more stars,
     each star followed by zero or more type qualifiers;
     see @(tsee declor) and @(tsee absdeclor).
     Here we print such a `pointer',
     from its representation as a list of lists of type qualifiers.")
   (xdoc::p
    "The outer list must not be empty, as required in the guard.
     We go through each inner list, printing a star for each;
     if the inner list under consideration is empty,
     the star is all we print;
     if the inner list is not empty,
     we also print a space,
     the type qualifiers (separated by spaces),
     and a space.
     That is, we provide separation when there are type qualifiers.
     But there are no extra separations for stars,
     e.g. we print @('**') for the list of lists @('(list nil nil)').
     Note that the last inner list is printed as just star."))
  (b* (((unless (mbt (consp tyqualss))) (pristate-fix pstate))
       (pstate (print-astring "*" pstate))
       (tyquals (car tyqualss))
       (pstate (if (consp tyquals)
                   (b* ((pstate (print-astring " " pstate))
                        (pstate (print-tyqual-list tyquals pstate))
                        (pstate (print-astring " " pstate)))
                     pstate)
                 pstate))
       ((when (endp (cdr tyqualss))) pstate))
    (print-tyqual-list-list (cdr tyqualss) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-funspec ((funspec funspecp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a function specifier."
  (funspec-case
   funspec
   :inline (print-astring "inline" pstate)
   :noreturn (print-astring "_Noreturn" pstate)
   ;; GCC extensions:
   :__inline (print-astring "__inline" pstate)
   :__inline__ (print-astring "__inline__" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-inc/dec-op ((op inc/dec-opp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an increment or decrement operator."
  (inc/dec-op-case
   op
   :inc (print-astring "++" pstate)
   :dec (print-astring "--" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-inc/dec-op-list ((ops inc/dec-op-listp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a list of zero or more increment or decrement operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We separate any two consecutive ones with a space."))
  (b* (((when (endp ops)) (pristate-fix pstate))
       (pstate (print-inc/dec-op (car ops) pstate))
       ((when (endp (cdr ops))) pstate)
       (pstate (print-astring " " pstate)))
    (print-inc/dec-op-list (cdr ops) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines print-exprs/decls
  :short "Print expressions, declarations, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since expressions and declarations are mutually recursive
     in our abstract syntax (as in the grammar),
     their printing functions are mutually recursive.
     Termination is easily proved,
     based on the sizes of the fixtypes."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-expr ((expr exprp)
                      (expected-prio expr-priorityp)
                      (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "The tree structure of the abstract syntax of C expressions
       describes the grouping of nested subexpressions.
       For instance, the tree")
     (xdoc::codeblock
      "(expr-binary (binop-mul)"
      "             (expr-binary (binop-add)"
      "                          (expr-ident (ident \"x\"))"
      "                          (expr-ident (ident \"y\")))"
      "             (expr-ident (ident \"z\")))")
     (xdoc::p
      "represents the expression @('(x + y) * z').
       When this expression is written in concrete syntax as just done,
       parentheses must be added,
       because @('*') binds tighter (i.e. has a higher priority) than @('+').")
     (xdoc::p
      "The relative priorities of C operators are implicitly defined
       by the grammar rules for expressions,
       which also define the left vs. right associativity
       of binary operators.
       For instance, the rules in [C:6.5.5] and [C:6.5.6] tell us that
       (i) @('+') binds tighter than @('*') and
       (ii) @('+') is left-associative:")
     (xdoc::ul
      (xdoc::li
       "Consider an expression @('x + y * z').
        In order to parse this as a <i>multiplicative-expression</i>,
        @('x + y') would have to be a <i>multiplicative-expression</i>),
        which is not.
        Thus, the expression can only be parsed
        as an <i>additive-expression</i>.")
      (xdoc::li
       "Consider an expression @('x * y + z').
        In order to parse this as a <i>multiplicative-expression</i>,
        @('y + z') would have to be a <i>cast-expression</i>,
        which is not.
        Thus, the expression can only be parsed
        as an <i>additive-expression</i>.")
      (xdoc::li
       "Consider an expression @('x + y + z').
        In order to right-associate it (i.e. @('x + (y + z)')),
        @('y + z') would have to be a <i>multiplicative-expression</i>,
        which is not.
        Thus, the expression can only be left-associated
        (i.e. @('(x + y) + z'))."))
     (xdoc::p
      "Our printer adds parentheses
       based on the relative priorities of the C operators
       and the left or right associativity of the C binary operators,
       following the grammar.")
     (xdoc::p
      "The function @(tsee expr-priority) classifies expressions
       according to certain nonterminals of the C grammar.
       For instance, the priority of additive expressions
       corresponds to the nonterminal <i>additive-expression</i>.
       The function @(tsee expr->priority) defines a mapping
       from the expressions of our abstract syntax to their priorities,
       e.g. @('(expr-binary (binop-add) ... ...)')
       and @('(expr-binary (binop-sub) ... ...)')
       are mapped to @('expr-priority-add'),
       the priority of additive expressions.
       The function @(tsee expr-priority-<=) defines
       a total order on expression priorities:
       see that function's documentation for details of
       how that total order is defined in relation to the grammar.")
     (xdoc::p
      "Besides the abstract syntactic expression to print,
       this printer function for expression has an argument
       that is the priority of the expression that must be printed
       at that point.
       At the top level, this second argument is
       the priority of top-level expressions,
       i.e. the priority that corresponds to
       the nonterminal <i>expression</i> [C:6.5.17].
       As we descend into subexpressions,
       the second argument of this function is changed according to
       the grammar rule corresponding to the super-expression.
       For instance, when printing the left and right subexpressions
       of a super-expression @('(expr-binary (binop-add) left right)'),
       we recursively call the printer twice,
       once on @('left') and once on @('right').
       Because of the grammar rule
       <i>additive-expression:
          additive-expression <tt>+</tt> multiplicative-expression</i>
       that corresponds to the super-expression,
       the recursive call on @('left') will have as second argument
       the priority of <i>additive-expression</i>,
       while the recursive call on @('right') will have as second argument
       the priority of <i>multiplicative-expression</i>.
       The second argument of the printer is used as follows:
       the printer compares the second argument
       (i.e. the expected priority of the expression)
       with the priority of the expression passed as first argument
       (i.e. the actual priority of the expression),
       according to the total order on expression priorities;
       if the actual priority is greater than or equal to the expected priority,
       the expression is printed without parentheses,
       otherwise parentheses are added.
       The reason why no parentheses are needed in the first case is that
       the nonterminal for the expected priority can be expanded,
       possibly in multiple steps,
       into the nonterminal for the actual priority:
       or conversely, the actual expression can be parsed
       into an expression of the expected priority.
       The expansion is based on the grammar (sub)rules
       discussed in @(tsee expr-priority-<=).
       On the other hand,
       if the actual priority is less than the expected priority,
       there is no such possibility;
       by adding parentheses, we change the priority of the actual expression
       into the one at the top of the total order,
       i.e. the priority corresponding to <i>primary-expression</i>,
       which again lets the parenthesized expression be parsed
       into an expression of the expected priority.")
     (xdoc::p
      "For instance, consider the abstract syntax tree for @('(x + y) * z'),
       shown earlier as motivating example.
       Assume that it is printed as a top-level expression,
       i.e. that the second argument is the priority of <i>expression</i>
       (the expected priority).
       Since the actual priority of the expression is
       the one for <i>multiplicative-expression</i>,
       which is greater than or equal to the one for <i>expression</i>
       (via
       <i>assignment-expression</i>,
       <i>conditional-expression</i>,
       <i>logical-OR-expression</i>,
       <i>logical-AND-expression</i>,
       <i>inclusive-OR-expression</i>,
       <i>exclusive-OR-expression</i>,
       <i>AND-expression</i>,
       <i>equality-expression</i>,
       <i>relational-expression</i>,
       <i>shift-expression</i>, and
       <i>additive-expression</i>),
       no parentheses are printed at the top level.
       When printing the left subexpression @('x + y'),
       the expected priority is <i>multiplicative-expression</i>:
       since the actual priority of @('x + y') is <i>additive-expression</i>,
       which is less than the expected priority,
       parentheses must be added,
       as mentioned when the example was first presented.
       On the other hand, when printing the right subexpression @('z'),
       the expected priority is <i>cast-expression</i>:
       since the actual priority of @('z') is <i>primary-expression</i>,
       which is less than the expected priority,
       no parentheses are printed.")
     (xdoc::p
      "The total order on expression priority only considers,
       as explained in @(tsee expr-priority-<=),
       (sub)rules of the form <i>nonterm1: nonterm2</i>
       where <i>nonterm2</i> is a single nonterminal.
       Rule definientia that are not single terminals
       are captured as tree structures in our abstract syntax,
       and thus have their own explicit priority.
       On the other hand, single-nonterminal definientia
       do not correspond to any tree structure,
       but rather allow the same expression to have, in effect,
       different priorities (a form of subtyping)."))
    (b* ((actual-prio (expr->priority expr))
         (parenp (not (expr-priority-<= expected-prio actual-prio)))
         (pstate (if parenp
                     (print-astring "(" pstate)
                   pstate))
         (pstate
          (expr-case
           expr
           :ident (print-ident expr.unwrap pstate)
           :const (print-const expr.unwrap pstate)
           :string (print-stringlit expr.unwrap pstate)
           :paren
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-expr expr.unwrap (expr-priority-expr) pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :gensel
           (b* ((pstate (print-astring "_Generic(" pstate))
                (pstate (print-expr expr.control (expr-priority-asg) pstate))
                (pstate (print-astring ", " pstate))
                ((unless expr.assoc)
                 (raise "Misusage error: ~
                         empty generic association list.")
                 pstate)
                (pstate (print-genassoc-list expr.assoc pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :arrsub
           (b* ((pstate (print-expr expr.arg1 (expr-priority-postfix) pstate))
                (pstate (print-astring "[" pstate))
                (pstate (print-expr expr.arg2 (expr-priority-expr) pstate))
                (pstate (print-astring "]" pstate)))
             pstate)
           :funcall
           (b* ((pstate (print-expr expr.fun (expr-priority-postfix) pstate))
                (pstate (print-astring "(" pstate))
                (pstate (if expr.args
                            (print-expr-list expr.args pstate)
                          pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :member
           (b* ((pstate (print-expr expr.arg (expr-priority-postfix) pstate))
                (pstate (print-astring "." pstate))
                (pstate (print-ident expr.name pstate)))
             pstate)
           :memberp
           (b* ((pstate (print-expr expr.arg (expr-priority-postfix) pstate))
                (pstate (print-astring "->" pstate))
                (pstate (print-ident expr.name pstate)))
             pstate)
           :complit
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ") {" pstate))
                ((unless expr.elems)
                 (raise "Misusage error: ~
                         empty initializer list.")
                 (pristate-fix pstate))
                (pstate (print-desiniter-list expr.elems pstate))
                (pstate (if expr.final-comma
                            (print-astring ", }" pstate)
                          (print-astring "}" pstate))))
             pstate)
           :unary
           (if (or (unop-case expr.op :postinc)
                   (unop-case expr.op :postdec))
               (b* ((pstate
                     (print-expr expr.arg (expr-priority-postfix) pstate))
                    (pstate (print-unop expr.op pstate)))
                 pstate)
             (b* ((pstate (print-unop expr.op pstate))
                  ;; We add a space:
                  ;; - After sizeof unless the argument is
                  ;;   a parenthesized expression,
                  ;;   in which case we print sizeof(expr).
                  ;;   This is a bit more than needed
                  ;;   just to avoid ambiguity in the printed code:
                  ;;   we could avoid the space in other cases,
                  ;;   besides parenthesized expressions as arguments;
                  ;;   but the resulting code may look confusing
                  ;;   in those other cases without the space.
                  ;; - After + if the argument is ++...,
                  ;;   otherwise +++ would be lexed as ++ +.
                  ;; - After - if the argument is --...,
                  ;;   otherwise --- would be lexed as -- -.
                  (spacep (or (and (unop-case expr.op :sizeof)
                                   (not (expr-case expr.arg :paren)))
                              (and (unop-case expr.op :plus)
                                   (expr-case expr.arg :unary)
                                   (unop-case (expr-unary->op expr.arg)
                                              :preinc))
                              (and (unop-case expr.op :minus)
                                   (expr-case expr.arg :unary)
                                   (unop-case (expr-unary->op expr.arg)
                                              :predec))))
                  (pstate (if spacep
                              (print-astring " " pstate)
                            pstate))
                  (arg-priority (if (or (unop-case expr.op :preinc)
                                        (unop-case expr.op :predec)
                                        (unop-case expr.op :sizeof))
                                    (expr-priority-unary)
                                  (expr-priority-cast)))
                  (pstate (print-expr expr.arg arg-priority pstate)))
               pstate))
           :sizeof
           (b* ((pstate (print-astring "sizeof(" pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           ;; We temporarily allow an ambiguous sizeof expression
           ;; as if its argument is an expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :sizeof-ambig
           (b* ((pstate (print-astring "sizeof(" pstate))
                (pstate (print-expr (amb-expr/tyname->expr expr.expr/tyname)
                                    (expr-priority-expr)
                                    pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :alignof
           (b* ((pstate (print-astring "_Alignof(" pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :cast
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-expr expr.arg (expr-priority-cast) pstate)))
             pstate)
           :binary
           (b* (((mv expected-arg1-prio expected-arg2-prio)
                 (binop-expected-priorities expr.op))
                (pstate (print-expr expr.arg1 expected-arg1-prio pstate))
                (pstate (print-astring " " pstate))
                (pstate (print-binop expr.op pstate))
                (pstate (print-astring " " pstate))
                (pstate (print-expr expr.arg2 expected-arg2-prio pstate)))
             pstate)
           :cond
           (b* ((pstate (print-expr expr.test (expr-priority-logor) pstate))
                (pstate (print-astring " ? " pstate))
                (pstate (print-expr expr.then (expr-priority-expr) pstate))
                (pstate (print-astring " : " pstate))
                (pstate (print-expr expr.else (expr-priority-cond) pstate)))
             pstate)
           :comma
           (b* ((pstate (print-expr expr.first (expr-priority-expr) pstate))
                (pstate (print-astring ", " pstate))
                (pstate (print-expr expr.next (expr-priority-asg) pstate)))
             pstate)
           ;; We temporarily allow an ambiguous cast/mul expression
           ;; as if it were a cast expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :cast/call-ambig
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname (amb-expr/tyname->tyname expr.type/fun)
                                      pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-inc/dec-op-list expr.inc/dec pstate))
                (pstate (if expr.inc/dec
                            (print-astring " " pstate)
                          pstate))
                (pstate (print-astring "(" pstate))
                (pstate (print-expr expr.arg/rest (expr-priority-expr) pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           ;; We temporarily allow an ambiguous cast/mul expression
           ;; as if it were a cast expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :cast/mul-ambig
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname (amb-expr/tyname->tyname expr.type/arg1)
                                      pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-inc/dec-op-list expr.inc/dec pstate))
                (pstate (if expr.inc/dec
                            (print-astring " " pstate)
                          pstate))
                (pstate (print-astring "* " pstate))
                (pstate (print-expr expr.arg/arg2
                                    (expr-priority-cast)
                                    pstate)))
             pstate)
           ;; We temporarily allow an ambiguous cast/add expression
           ;; as if it were a cast expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :cast/add-ambig
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname (amb-expr/tyname->tyname expr.type/arg1)
                                      pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-inc/dec-op-list expr.inc/dec pstate))
                (pstate (if expr.inc/dec
                            (print-astring " " pstate)
                          pstate))
                (pstate (print-astring "+ " pstate))
                ;; We keep the expected priority to cast
                ;; so that it is valid if it is a cast;
                ;; if it is an addition,
                ;; it may have harmless extra parentheses.
                (pstate (print-expr expr.arg/arg2
                                    (expr-priority-cast)
                                    pstate)))
             pstate)
           ;; We temporarily allow an ambiguous cast/sub expression
           ;; as if it were a cast expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :cast/sub-ambig
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname (amb-expr/tyname->tyname expr.type/arg1)
                                      pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-inc/dec-op-list expr.inc/dec pstate))
                (pstate (if expr.inc/dec
                            (print-astring " " pstate)
                          pstate))
                (pstate (print-astring "- " pstate))
                ;; We keep the expected priority to cast
                ;; so that it is valid if it is a cast;
                ;; if it is a subtraction,
                ;; it may have harmless extra parentheses.
                (pstate (print-expr expr.arg/arg2
                                    (expr-priority-cast)
                                    pstate)))
             pstate)
           ;; We temporarily allow an ambiguous cast/and expression
           ;; as if it were a cast expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :cast/and-ambig
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-tyname (amb-expr/tyname->tyname expr.type/arg1)
                                      pstate))
                (pstate (print-astring ") " pstate))
                (pstate (print-inc/dec-op-list expr.inc/dec pstate))
                (pstate (if expr.inc/dec
                            (print-astring " " pstate)
                          pstate))
                (pstate (print-astring "& " pstate))
                ;; We keep the expected priority to cast
                ;; so that it is valid if it is a cast;
                ;; if it is a conjunction,
                ;; it may have harmless extra parentheses.
                (pstate (print-expr expr.arg/arg2
                                    (expr-priority-cast)
                                    pstate)))
             pstate)))
         (pstate (if parenp
                     (print-astring ")" pstate)
                   pstate)))
      pstate)
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-expr-list ((exprs expr-listp) (pstate pristatep))
    :guard (consp exprs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more expressions, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used to print argument expressions of function calls,
       as well as paramaters of GCC attributes
       if GCC extensions are supported.")
     (xdoc::p
      "The case of an empty expression list
       is handled in @(tsee print-expr).
       This function is called when there is at least one.")
     (xdoc::p
      "This is why we separate the expressions with commas.
       Since the grammar rule for @('argument-expression-list')
       uses assignment expressions,
       we pass that priority to @(tsee print-expr)."))
    (b* (((unless (mbt (consp exprs))) (pristate-fix pstate))
         (pstate (print-expr (car exprs) (expr-priority-asg) pstate))
         ((when (endp (cdr exprs))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-expr-list (cdr exprs) pstate))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-const-expr ((cexpr const-exprp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "A constant expression is
       a synonym of a conditional expression in the grammar,
       so we use that as priority."))
    (print-expr (const-expr->unwrap cexpr) (expr-priority-cond) pstate)
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-genassoc ((genassoc genassocp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a generic association."
    (genassoc-case
     genassoc
     :type
     (b* ((pstate (print-tyname genassoc.type pstate))
          (pstate (print-astring ": " pstate))
          (pstate (print-expr genassoc.expr (expr-priority-asg) pstate)))
       pstate)
     :default
     (b* ((pstate (print-astring "default: " pstate))
          (pstate (print-expr genassoc.expr (expr-priority-asg) pstate)))
       pstate))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-genassoc-list ((genassocs genassoc-listp) (pstate pristatep))
    :guard (consp genassocs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more generic associations,
            separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called by @(tsee print-expr),
       which ensures that the list is not empty."))
    (b* (((unless (mbt (consp genassocs))) (pristate-fix pstate))
         (pstate (print-genassoc (car genassocs) pstate))
         ((when (endp (cdr genassocs))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-genassoc-list (cdr genassocs) pstate))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-tyspec ((tyspec tyspecp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a type specifier."
    (tyspec-case
     tyspec
     :void (print-astring "void" pstate)
     :char (print-astring "char" pstate)
     :short (print-astring "short" pstate)
     :int (print-astring "int" pstate)
     :long (print-astring "long" pstate)
     :float (print-astring "float" pstate)
     :double (print-astring "double" pstate)
     :signed (print-astring "signed" pstate)
     :unsigned (print-astring "unsigned" pstate)
     :bool (print-astring "_Bool" pstate)
     :complex (print-astring "_Complex" pstate)
     :atomic (b* ((pstate (print-astring "_Atomic(" pstate))
                  (pstate (print-tyname tyspec.type pstate))
                  (pstate (print-astring ")" pstate)))
               pstate)
     :struct (b* ((pstate (print-astring "struct " pstate))
                  (pstate (print-strunispec tyspec.unwrap pstate)))
               pstate)
     :union (b* ((pstate (print-astring "union " pstate))
                 (pstate (print-strunispec tyspec.unwrap pstate)))
              pstate)
     :enum (b* ((pstate (print-astring "enum " pstate))
                (pstate (print-enumspec tyspec.unwrap pstate)))
             pstate)
     :tydef (print-ident tyspec.name pstate))
    :measure (tyspec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-specqual ((specqual specqualp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a specifier or qualifier."
    (specqual-case
     specqual
     :tyspec (print-tyspec specqual.unwrap pstate)
     :tyqual (print-tyqual specqual.unwrap pstate)
     :alignspec (print-alignspec specqual.unwrap pstate))
    :measure (specqual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-specqual-list ((specquals specqual-listp) (pstate pristatep))
    :guard (consp specquals)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more specifiers and qualifiers,
            separated by spaces."
    (b* (((unless (mbt (consp specquals))) (pristate-fix pstate))
         (pstate (print-specqual (car specquals) pstate))
         ((when (endp (cdr specquals))) pstate)
         (pstate (print-astring " " pstate)))
      (print-specqual-list (cdr specquals) pstate))
    :measure (specqual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-alignspec ((alignspec alignspecp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an alignment specifier."
    (b* ((pstate (print-astring "_Alignas(" pstate))
         (pstate
          (alignspec-case
           alignspec
           :alignas-type (print-tyname alignspec.type pstate)
           :alignas-expr (print-const-expr alignspec.arg pstate)
           ;; We temporarily allow an ambiguous alignment specifier
           ;; as if its argument is an expression.
           ;; This must go away during static semantic elaboration,
           ;; which should be normally done prior to printing.
           :alignas-ambig
           (print-expr (amb-expr/tyname->expr alignspec.type/arg)
                       (expr-priority-expr)
                       pstate)))
         (pstate (print-astring ")" pstate)))
      pstate)
    :measure (alignspec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-declspec ((declspec declspecp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a declaration specifier."
    (declspec-case
     declspec
     :stocla (print-stoclaspec declspec.unwrap pstate)
     :tyspec (print-tyspec declspec.unwrap pstate)
     :tyqual (print-tyqual declspec.unwrap pstate)
     :funspec (print-funspec declspec.unwrap pstate)
     :alignspec (print-alignspec declspec.unwrap pstate))
    :measure (declspec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-declspec-list ((declspecs declspec-listp) (pstate pristatep))
    :guard (consp declspecs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more declaration specifiers,
            separated by spaces."
    (b* (((unless (mbt (consp declspecs))) (pristate-fix pstate))
         (pstate (print-declspec (car declspecs) pstate))
         ((when (endp (cdr declspecs))) pstate)
         (pstate (print-astring " " pstate)))
      (print-declspec-list (cdr declspecs) pstate))
    :measure (declspec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-initer ((initer initerp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "In the single initializer case,
       the expression is regarded as an assignment expression,
       according to the grammar.")
     (xdoc::p
      "For the list case, we ensure that the list is not empty."))
    (initer-case
     initer
     :single (print-expr initer.expr (expr-priority-asg) pstate)
     :list (b* ((pstate (print-astring "{" pstate))
                ((unless initer.elems)
                 (raise "Misusage error: ~
                         empty list of initializers.")
                 pstate)
                (pstate (print-desiniter-list initer.elems pstate))
                (pstate (if initer.final-comma
                            (print-astring ", }" pstate)
                          (print-astring "}" pstate))))
             pstate))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-desiniter ((desiniter desiniterp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter)
         (pstate (if desiniter.design
                     (b* ((pstate (print-designor-list desiniter.design pstate))
                          (pstate (print-astring " = " pstate)))
                       pstate)
                   pstate))
         (pstate (print-initer desiniter.init pstate)))
      pstate)
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-desiniter-list ((desiniters desiniter-listp)
                                (pstate pristatep))
    :guard (consp desiniters)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more initializers with optional designations,
            separated by commas."
    (b* (((unless (mbt (consp desiniters))) (pristate-fix pstate))
         (pstate (print-desiniter (car desiniters) pstate))
         ((when (endp (cdr desiniters))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-desiniter-list (cdr desiniters) pstate))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-designor ((designor designorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a designator."
    (designor-case
     designor
     :sub (b* ((pstate (print-astring "[" pstate))
               (pstate (print-const-expr designor.index pstate))
               (pstate (print-astring "]" pstate)))
            pstate)
     :dot (b* ((pstate (print-astring "." pstate))
               (pstate (print-ident designor.name pstate)))
            pstate))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-designor-list ((designors designor-listp)
                               (pstate pristatep))
    :guard (consp designors)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We print no separation between the designators."))
    (b* (((unless (mbt (consp designors))) (pristate-fix pstate))
         (pstate (print-designor (car designors) pstate))
         ((when (endp (cdr designors))) pstate))
      (print-designor-list (cdr designors) pstate))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-declor ((declor declorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a declarator."
    (b* (((declor declor) declor)
         (pstate (if (consp declor.pointers)
                     (print-tyqual-list-list declor.pointers pstate)
                   pstate))
         (pstate (print-dirdeclor declor.decl pstate)))
      pstate)
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-dirdeclor ((dirdeclor dirdeclorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "For the @(':array-static2') case,
       we ensure that the list of type qualifiers is not empty,
       as required in the grammar.")
     (xdoc::p
      "For the @(':function-params') case,
       we ensure that the list of parameter declarations is not empty,
       as required in the grammar."))
    (dirdeclor-case
     dirdeclor
     :ident (print-ident dirdeclor.unwrap pstate)
     :paren (b* ((pstate (print-astring "(" pstate))
                 (pstate (print-declor dirdeclor.unwrap pstate))
                 (pstate (print-astring ")" pstate)))
              pstate)
     :array
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirdeclor.tyquals
                      (print-tyqual-list dirdeclor.tyquals pstate)
                    pstate))
          (pstate (if (and dirdeclor.tyquals
                           dirdeclor.expr?)
                      (print-astring " " pstate)
                    pstate))
          (pstate (if (expr-option-case dirdeclor.expr? :some)
                      (print-expr (expr-option-some->val dirdeclor.expr?)
                                  (expr-priority-asg)
                                  pstate)
                    pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static1
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          (pstate (print-astring "static " pstate))
          (pstate (if dirdeclor.tyquals
                      (b* ((pstate (print-tyqual-list dirdeclor.tyquals pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-expr dirdeclor.expr (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static2
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          ((unless dirdeclor.tyquals)
           (raise "Misusage error: ~
                   empty list of type qualifiers.")
           pstate)
          (pstate (print-tyqual-list dirdeclor.tyquals pstate))
          (pstate (print-astring " static " pstate))
          (pstate (print-expr dirdeclor.expr (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-star
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirdeclor.tyquals
                      (b* ((pstate (print-tyqual-list dirdeclor.tyquals pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring "*]" pstate)))
       pstate)
     :function-params
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          (pstate (print-astring "(" pstate))
          ;; We relax this check for now, but we will re-introduce it
          ;; after we add an elaboration of the abstract syntax
          ;; that turns empty :function-params into empty :function-names,
          ;; consistently with the grammar:
          ;; ((unless dirdeclor.params)
          ;;  (raise "Misusage error: ~
          ;;          empty parameters.")
          ;;  pstate)
          (pstate (if dirdeclor.params
                      (print-paramdecl-list dirdeclor.params pstate)
                    pstate))
          (pstate (if dirdeclor.ellipsis
                      (print-astring ", ...)" pstate)
                    (print-astring ")" pstate))))
       pstate)
     :function-names
     (b* ((pstate (print-dirdeclor dirdeclor.decl pstate))
          (pstate (print-astring "(" pstate))
          (pstate (if dirdeclor.names
                      (print-ident-list dirdeclor.names pstate)
                    pstate))
          (pstate (print-astring ")" pstate)))
       pstate))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-absdeclor ((absdeclor absdeclorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the abstract declarator is not empty,
       i.e. it has at least the pointer part
       or the direct abstract declarator part."))
    (b* (((absdeclor absdeclor) absdeclor)
         ((unless (or absdeclor.pointers
                      absdeclor.decl?))
          (raise "Misusage error: ~
                  empty abstract declarator.")
          (pristate-fix pstate))
         (pstate (if absdeclor.pointers
                     (print-tyqual-list-list absdeclor.pointers pstate)
                   pstate))
         (pstate (if (dirabsdeclor-option-case absdeclor.decl? :some)
                     (print-dirabsdeclor (dirabsdeclor-option-some->val
                                          absdeclor.decl?)
                                         pstate)
                   pstate)))
      pstate)
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-dirabsdeclor ((dirabsdeclor dirabsdeclorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a direct abstract declarator."
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base
     (prog2$ (raise "Misusage error: ~
                     dummy base case of direct abstract declarator.")
             (pristate-fix pstate))
     :paren
     (b* ((pstate (print-astring "(" pstate))
          (pstate (print-absdeclor dirabsdeclor.unwrap pstate))
          (pstate (print-astring ")" pstate)))
       pstate)
     :array
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.decl? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.decl?)
                       pstate)
                    pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirabsdeclor.tyquals
                      (print-tyqual-list dirabsdeclor.tyquals pstate)
                    pstate))
          (pstate (if (and dirabsdeclor.tyquals
                           dirabsdeclor.expr?)
                      (print-astring " " pstate)
                    pstate))
          (pstate (if (expr-option-case dirabsdeclor.expr? :some)
                      (print-expr (expr-option-some->val dirabsdeclor.expr?)
                                  (expr-priority-asg)
                                  pstate)
                    pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static1
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.decl? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.decl?)
                       pstate)
                    pstate))
          (pstate (print-astring "static " pstate))
          (pstate (if dirabsdeclor.tyquals
                      (b* ((pstate (print-tyqual-list dirabsdeclor.tyquals
                                                      pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-expr dirabsdeclor.expr (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static2
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.decl? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.decl?)
                       pstate)
                    pstate))
          ((unless dirabsdeclor.tyquals)
           (raise "Misusage error: ~
                   empty list of type qualifiers.")
           (pristate-fix pstate))
          (pstate (print-tyqual-list dirabsdeclor.tyquals pstate))
          (pstate (print-astring " static " pstate))
          (pstate (print-expr dirabsdeclor.expr (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-star
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.decl? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.decl?)
                       pstate)
                    pstate))
          (pstate (print-astring "[*]" pstate)))
       pstate)
     :function
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.decl? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.decl?)
                       pstate)
                    pstate))
          (pstate (print-astring "(" pstate))
          (pstate (if dirabsdeclor.params
                      (b* ((pstate
                            (print-paramdecl-list dirabsdeclor.params pstate))
                           (pstate (if dirabsdeclor.ellipsis
                                       (print-astring ", ..." pstate)
                                     pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring ")" pstate)))
       pstate))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-paramdecl ((paramdecl paramdeclp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that there are declaration specifiers."))
    (b* (((paramdecl paramdecl) paramdecl)
         ((unless paramdecl.spec)
          (raise "Misusage error: no declaration specifiers.")
          (pristate-fix pstate))
         (pstate (print-declspec-list paramdecl.spec pstate))
         (pstate (print-paramdeclor paramdecl.decl pstate)))
      pstate)
    :measure (paramdecl-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-paramdecl-list ((paramdecls paramdecl-listp) (pstate pristatep))
    :guard (consp paramdecls)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more parameter declarations,
            separated by commas."
    (b* (((unless (mbt (consp paramdecls))) (pristate-fix pstate))
         (pstate (print-paramdecl (car paramdecls) pstate))
         ((when (endp (cdr paramdecls))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-paramdecl-list (cdr paramdecls) pstate))
    :measure (paramdecl-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-paramdeclor ((paramdeclor paramdeclorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is always called after printing
       the declaration specifiers that start a parameter declaration.
       Thus, if the parameter declarator is present,
       we print a space to separate the declaration specifiers
       from the declarator or abstract declarator."))
    (paramdeclor-case
     paramdeclor
     :declor (b* ((pstate (print-astring " " pstate))
                  (pstate (print-declor paramdeclor.unwrap pstate)))
               pstate)
     :absdeclor (b* ((pstate (print-astring " " pstate))
                     (pstate (print-absdeclor paramdeclor.unwrap pstate)))
                  pstate)
     :none (pristate-fix pstate)
     ;; We temporarily print an ambiguous parameter declarator
     ;; as if it were a (non-abstract) declarator.
     ;; This must go away during static semantic elaboration,
     ;; which should be normally done prior to printing.
     :ambig (b* ((pstate (print-astring " " pstate))
                 (pstate (print-declor
                          (amb-declor/absdeclor->declor paramdeclor.unwrap)
                          pstate)))
              pstate))
    :measure (paramdeclor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-tyname ((tyname tynamep) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the list of specifiers and qualifiers is not empty."))
    (b* (((tyname tyname) tyname)
         ((unless tyname.specqual)
          (raise "Misusage error: empty list of specifiers and qualifiers.")
          (pristate-fix pstate))
         (pstate (print-specqual-list tyname.specqual pstate))
         ((unless (absdeclor-option-case tyname.decl? :some)) pstate)
         (pstate (print-astring " " pstate))
         (pstate (print-absdeclor (absdeclor-option-some->val tyname.decl?)
                                  pstate)))
      pstate)
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-strunispec ((strunispec strunispecp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is called after printing
       the @('struct') or @('union') keyword followed by a space.
       Here we print what comes after that keyword.")
     (xdoc::p
      "We ensure that this is not empty, i.e. that there is at least
       the identifier or a non-empty member list.")
     (xdoc::p
      "For now we print all the members in the same line,
       but we should print them in different lines and with identation,
       at least in certain cases.
       Note that a structure or union specifier
       is not necessarily a top-level construct:
       it may occur in the middle of a sequence of declaration specifiers,
       so it is not so straightforward to always print it on multiple lines,
       because we may need to consider what surrounds it.
       Nonetheless, under certain conditions,
       e.g. when it is a lone top-level construct,
       we should print it on multiple lines."))
    (b* (((strunispec strunispec) strunispec)
         ((unless (or (ident-option-case strunispec.name :some)
                      strunispec.members))
          (raise "Misusage error: empty structure or union specifier.")
          (pristate-fix pstate))
         (pstate (ident-option-case
                  strunispec.name
                  :some (print-ident strunispec.name.val pstate)
                  :none pstate))
         (pstate (if (and strunispec.name
                          strunispec.members)
                     (print-astring " " pstate)
                   pstate))
         ((when (not strunispec.members)) pstate)
         (pstate (print-astring "{ " pstate))
         (pstate (print-structdecl-list strunispec.members pstate))
         (pstate (print-astring " }" pstate)))
      pstate)
    :measure (strunispec-count strunispec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdecl ((structdecl structdeclp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "For the case of a member, we ensure that
       the list of specifiers and qualifiers is not empty,
       as required in the grammar."))
    (structdecl-case
     structdecl
     :member
     (b* ((pstate (if structdecl.extension
                      (print-astring "__extension__ " pstate)
                    (pristate-fix pstate)))
          ((unless structdecl.specqual)
           (raise "Misusage error: empty specifier/qualifier list.")
           pstate)
          (pstate (print-specqual-list structdecl.specqual pstate))
          (pstate (if structdecl.declor
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-structdeclor-list structdecl.declor
                                                            pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring ";" pstate)))
       pstate)
     :statassert (print-statassert structdecl.unwrap pstate))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdecl-list ((structdecls structdecl-listp)
                                 (pstate pristatep))
    :guard (consp structdecls)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more structure declarations,
            separated by spaces."
    :long
    (xdoc::topstring
     (xdoc::p
      "As mentioned in @(tsee print-strunispec),
       for now we print all of them in one line,
       since a structure or union specifier may occur
       in the middle of a list of declaration specifiers,
       but we plan to print these in multiple lines,
       at least under certain conditions
       (e.g. when the structure or union specifier is at the top level."))
    (b* (((unless (mbt (consp structdecls))) (pristate-fix pstate))
         (pstate (print-structdecl (car structdecls) pstate))
         ((when (endp (cdr structdecls))) pstate)
         (pstate (print-astring " " pstate)))
      (print-structdecl-list (cdr structdecls) pstate))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdeclor ((structdeclor structdeclorp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the structure declarator is not empty,
       i.e. that there is a declarator or an expression,
       as required by the grammar."))
    (b* (((structdeclor structdeclor) structdeclor)
         ((unless (or (declor-option-case structdeclor.declor? :some)
                      (const-expr-option-case structdeclor.expr? :some)))
          (raise "Misusage error: empty structure declarator.")
          (pristate-fix pstate))
         (pstate (declor-option-case
                  structdeclor.declor?
                  :some (print-declor structdeclor.declor?.val pstate)
                  :none pstate))
         (pstate (if (and (declor-option-case structdeclor.declor? :some)
                          (const-expr-option-case structdeclor.expr? :some))
                     (print-astring " " pstate)
                   pstate))
         (pstate (const-expr-option-case
                  structdeclor.expr?
                  :some (b* ((pstate (print-astring ": " pstate))
                             (pstate (print-const-expr structdeclor.expr?.val
                                                       pstate)))
                          pstate)
                  :none pstate)))
      pstate)
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdeclor-list ((structdeclors structdeclor-listp)
                                   (pstate pristatep))
    :guard (consp structdeclors)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more structure declarators,
            separated by commas."
    (b* (((unless (mbt (consp structdeclors))) (pristate-fix pstate))
         (pstate (print-structdeclor (car structdeclors) pstate))
         ((when (endp (cdr structdeclors))) pstate)
         (pstate (print-astring " " pstate)))
      (print-structdeclor-list (cdr structdeclors) pstate))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumspec ((enumspec enumspecp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an enueration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the enumeration specifier is not empty,
       i.e. that there is a name or a non-empty list of enumerators."))
    (b* (((enumspec enumspec) enumspec)
         ((unless (or (ident-option-case enumspec.name :some)
                      enumspec.list))
          (raise "Misusage error: empty enumeration specifiers.")
          (pristate-fix pstate))
         (pstate (ident-option-case
                  enumspec.name
                  :some (print-ident enumspec.name.val pstate)
                  :none pstate))
         (pstate (if (and (ident-option-case enumspec.name :some)
                          enumspec.list)
                     (print-astring " " pstate)
                   pstate))
         ((unless enumspec.list) pstate)
         (pstate (print-astring "{" pstate))
         (pstate (print-enumer-list enumspec.list pstate))
         (pstate (if enumspec.final-comma
                     (print-astring ", }" pstate)
                   (print-astring "}" pstate))))
      pstate)
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumer ((enumer enumerp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print an enumerator."
    (b* (((enumer enumer) enumer)
         (pstate (print-ident enumer.name pstate))
         ((unless (const-expr-option-case enumer.value :some)) pstate)
         (pstate (print-astring " = " pstate))
         (pstate (print-const-expr (const-expr-option-some->val enumer.value)
                                   pstate)))
      pstate)
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumer-list ((enumers enumer-listp) (pstate pristatep))
    :guard (consp enumers)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a list of one or more enumerators, separated by commas."
    (b* (((unless (mbt (consp enumers))) (pristate-fix pstate))
         (pstate (print-enumer (car enumers) pstate))
         ((when (endp (cdr enumers))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-enumer-list (cdr enumers) pstate))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-statassert ((statassert statassertp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls)
    :short "Print a static assertion declaration."
    (b* (((statassert statassert) statassert)
         (pstate (print-astring "_Static_assert(" pstate))
         (pstate (print-const-expr statassert.test pstate))
         (pstate (print-astring ", " pstate))
         (pstate (print-stringlit statassert.message pstate))
         (pstate (print-astring ");" pstate)))
      pstate)
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :ruler-extenders :all

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards print-expr
    :hints (("Goal" :in-theory (disable (:e tau-system))))) ; for speed

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual print-exprs/decls))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib ((attr attribp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a GCC attribute."
  (attrib-case
   attr
   :name (print-ident attr.name pstate)
   :name-param (b* ((pstate (print-ident attr.name pstate))
                    (pstate (if attr.param
                                (print-expr-list attr.param pstate)
                              pstate)))
                 pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-list ((attrs attrib-listp) (pstate pristatep))
  :guard (consp attrs)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more GCC attributes, comma-separated."
  (b* (((unless (mbt (consp attrs))) (pristate-fix pstate))
       (pstate (print-attrib (car attrs) pstate))
       ((when (endp (cdr attrs))) pstate)
       (pstate (print-astring ", " pstate)))
    (print-attrib-list (cdr attrs) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-spec ((attrspec attrib-specp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an attribute specifier."
  (b* ((pstate (print-astring "__attribute__ ((" pstate))
       (attrs (attrib-spec->attribs attrspec))
       (pstate (if (consp attrs)
                   (print-attrib-list attrs pstate)
                 pstate))
       (pstate (print-astring "))" pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-spec-list ((attrspecs attrib-spec-listp)
                                (pstate pristatep))
  :guard (consp attrspecs)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more attribute specifiers,
          separated by single spaces."
  (b* (((unless (mbt (consp attrspecs))) (pristate-fix pstate))
       (pstate (print-attrib-spec (car attrspecs) pstate))
       ((when (endp (cdr attrspecs))) pstate))
    (print-attrib-spec-list (cdr attrspecs) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-name-spec ((asmspec asm-name-specp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an assembler name specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that there is at least one string literal."))
  (b* (((asm-name-spec asmspec) asmspec)
       (pstate (if asmspec.uscores
                   (print-astring "__asm__ (" pstate)
                 (print-astring "asm (" pstate)))
       ((unless (consp asmspec.strings))
        (raise "Misusage error: ~
                no string literals in assembler name specifier.")
        pstate)
       (pstate (print-stringlit-list asmspec.strings pstate))
       (pstate (print-astring ")" pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-initdeclor ((initdeclor initdeclorp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an initializer declarator."
  (b* (((initdeclor initdeclor) initdeclor)
       (pstate (print-declor initdeclor.declor pstate))
       ((when (initer-option-case initdeclor.init? :none)) pstate)
       (pstate (print-astring " = " pstate))
       (pstate (print-initer (initer-option-some->val initdeclor.init?)
                             pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-initdeclor-list ((initdeclors initdeclor-listp)
                               (pstate pristatep))
  :guard (consp initdeclors)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more initializer declarators,
          separated by commas."
  (b* (((unless (mbt (consp initdeclors))) (pristate-fix pstate))
       (pstate (print-initdeclor (car initdeclors) pstate))
       ((when (endp (cdr initdeclors))) pstate)
       (pstate (print-astring ", " pstate)))
    (print-initdeclor-list (cdr initdeclors) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-decl-inline ((decl declp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a declaration, inline."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here `inline' means that we print is as part of the current line,
     without adding new lines or indentation.")
   (xdoc::p
    "We ensure that there is at least one declaration specifier,
     as required by the grammar."))
  (decl-case
   decl
   :decl
   (b* ((pstate (if decl.extension
                    (print-astring "__extension__ " pstate)
                  (pristate-fix pstate)))
        ((unless decl.specs)
         (raise "Misusage error: ~
                 no declaration specifiers in declaration ~x0."
                decl)
         pstate)
        (pstate (print-declspec-list decl.specs pstate))
        (pstate
         (if decl.init
             (b* ((pstate (print-astring " " pstate))
                  (pstate (print-initdeclor-list decl.init pstate)))
               pstate)
           pstate))
        (pstate (if decl.asm?
                    (b* ((pstate (print-astring " " pstate))
                         (pstate (print-asm-name-spec decl.asm? pstate)))
                      pstate)
                  pstate))
        (pstate (if decl.attrib
                    (b* ((pstate (print-astring " " pstate))
                         (pstate (print-attrib-spec-list decl.attrib pstate)))
                      pstate)
                  pstate))
        (pstate (print-astring ";" pstate)))
     pstate)
   :statassert
   (print-statassert decl.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-decl ((decl declp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a declaration, in its own indented line."
  (b* ((pstate (print-indent pstate))
       (pstate (print-decl-inline decl pstate))
       (pstate (print-new-line pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-decl-list ((decls decl-listp) (pstate pristatep))
  :guard (consp decls)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more declarations,
          one per line, all with the same indentation."
  (b* (((unless (mbt (consp decls))) (pristate-fix pstate))
       (pstate (print-decl (car decls) pstate))
       ((when (endp (cdr decls))) pstate))
    (print-decl-list (cdr decls) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-label ((label labelp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a label."
  (label-case
   label
   :name (print-ident label.unwrap pstate)
   :const (b* ((pstate (print-astring "case " pstate))
               (pstate (print-const-expr label.unwrap pstate)))
            pstate)
   :default (print-astring "default" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines print-stmts/blocks
  :short "Print statements, blocks, and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since statements and blocks are mutually recursive
     in our abstract syntax (as in the grammar),
     their printing functions are mutually recursive.
     Termination is easily proved,
     based on the sizes of the fixtypes."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-stmt ((stmt stmtp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-stmts/blocks)
    :short "Print a statement, in one or more lines, with proper indentation."
    :long
    (xdoc::topstring
     (xdoc::p
      "When printing sub-statements of statements,
       we treat compound sub-statements slighly differently
       from non-compound sub-statements,
       because for compound sub-statements we print
       the open curly brace at the end of the line,
       and additionally the closed curly brace may be followed
       by more code on the same line (e.g. for an @('else')).
       We use a separate function @(tsee print-block) for that;
       see its documentation."))
    (stmt-case
     stmt
     :labeled
     (b* ((pstate (print-indent pstate))
          (pstate (print-label stmt.label pstate))
          (pstate (print-astring ":" pstate)))
       (if (stmt-case stmt.stmt :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.stmt) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.stmt pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :compound
     (b* ((pstate (print-indent pstate))
          (pstate (print-block stmt.items pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :expr
     (b* ((pstate (print-indent pstate))
          (pstate (expr-option-case
                   stmt.expr?
                   :some (print-expr (expr-option-some->val stmt.expr?)
                                     (expr-priority-expr)
                                     pstate)
                   :none pstate))
          (pstate (print-astring ";" pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :if
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "if (" pstate))
          (pstate (print-expr stmt.test (expr-priority-expr) pstate))
          (pstate (print-astring ")" pstate)))
       (if (stmt-case stmt.then :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.then) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.then pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :ifelse
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "if (" pstate))
          (pstate (print-expr stmt.test (expr-priority-expr) pstate))
          (pstate (print-astring ")" pstate))
          (pstate (if (stmt-case stmt.then :compound)
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-block (stmt-compound->items stmt.then)
                                                pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    (b* ((pstate (print-new-line pstate))
                         (pstate (inc-pristate-indent pstate))
                         (pstate (print-stmt stmt.then pstate))
                         (pstate (dec-pristate-indent pstate)))
                      pstate)))
          (pstate (print-astring "else" pstate))
          (pstate (if (stmt-case stmt.else :compound)
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-block (stmt-compound->items stmt.else)
                                                pstate))
                           (pstate (print-new-line pstate)))
                        pstate)
                    (b* ((pstate (print-new-line pstate))
                         (pstate (inc-pristate-indent pstate))
                         (pstate (print-stmt stmt.else pstate))
                         (pstate (dec-pristate-indent pstate)))
                      pstate))))
       pstate)
     :switch
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "switch (" pstate))
          (pstate (print-expr stmt.target (expr-priority-expr) pstate))
          (pstate (print-astring ")" pstate)))
       (if (stmt-case stmt.body :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.body) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.body pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :while
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "while (" pstate))
          (pstate (print-expr stmt.test (expr-priority-expr) pstate))
          (pstate (print-astring ")" pstate)))
       (if (stmt-case stmt.body :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.body) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.body pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :dowhile
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "do" pstate))
          (pstate (if (stmt-case stmt.body :compound)
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-block (stmt-compound->items stmt.body)
                                                pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    (b* ((pstate (print-new-line pstate))
                         (pstate (inc-pristate-indent pstate))
                         (pstate (print-stmt stmt.body pstate))
                         (pstate (dec-pristate-indent pstate)))
                      pstate)))
          (pstate (print-astring "while (" pstate))
          (pstate (print-expr stmt.test (expr-priority-expr) pstate))
          (pstate (print-astring ");" pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :for
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "for (" pstate))
          (pstate (expr-option-case
                   stmt.init
                   :some (print-expr stmt.init (expr-priority-expr) pstate)
                   :none (print-astring " " pstate)))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.test
                   :some (print-expr stmt.test (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.next
                   :some (print-expr stmt.next (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring ")" pstate)))
       (if (stmt-case stmt.body :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.body) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.body pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :fordecl
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "for (" pstate))
          (pstate (print-decl-inline stmt.init pstate))
          (pstate (print-astring " " pstate))
          (pstate (expr-option-case
                   stmt.test
                   :some (print-expr stmt.test (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.next
                   :some (print-expr stmt.next (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring ")" pstate)))
       (if (stmt-case stmt.body :compound)
           (b* ((pstate (print-astring " " pstate))
                (pstate (print-block (stmt-compound->items stmt.body) pstate))
                (pstate (print-new-line pstate)))
             pstate)
         (b* ((pstate (print-new-line pstate))
              (pstate (inc-pristate-indent pstate))
              (pstate (print-stmt stmt.body pstate))
              (pstate (dec-pristate-indent pstate)))
           pstate)))
     :goto
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "goto " pstate))
          (pstate (print-ident stmt.label pstate))
          (pstate (print-astring ";" pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :continue
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "continue;" pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :break
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "break;" pstate))
          (pstate (print-new-line pstate)))
       pstate)
     :return
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "return" pstate))
          (pstate
           (expr-option-case
            stmt.expr?
            :some (b* ((pstate (print-astring " " pstate))
                       (pstate (print-expr (expr-option-some->val stmt.expr?)
                                           (expr-priority-expr)
                                           pstate)))
                    pstate)
            :none pstate))
          (pstate (print-astring ";" pstate))
          (pstate (print-new-line pstate)))
       pstate))
    :measure (two-nats-measure (stmt-count stmt) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block-item ((item block-itemp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-stmts/blocks)
    :short "Print a block item."
    (block-item-case
     item
     :decl (print-decl item.unwrap pstate)
     :stmt (print-stmt item.unwrap pstate)
     ;; We temporarily print an ambiguous block item
     ;; as if it were a declaration.
     ;; This must go away during static semantic elaboration,
     ;; which should be normally done prior to printing.
     :ambig (print-decl (amb-decl/stmt->decl item.unwrap) pstate))
    :measure (two-nats-measure (block-item-count item) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block-item-list ((items block-item-listp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-stmts/blocks)
    :short "Print a list of zero or more block items."
    (b* (((when (endp items)) (pristate-fix pstate))
         (pstate (print-block-item (car items) pstate)))
      (print-block-item-list (cdr items) pstate))
    :measure (two-nats-measure (block-item-list-count items) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block ((items block-item-listp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-stmts/blocks)
    :short "Print a block."
    :long
    (xdoc::topstring
     (xdoc::p
      "This prints the open curly brace in the current position on the line,
       i.e. without printing any new line or indentation.
       Then it prints the block items after a new line
       and after incrementing the indentation level,
       and finally it restores the indentation level
       and prints the closed curly brace,
       without any new line after that.")
     (xdoc::p
      "In other words, this prints the block ``inline'',
       but the block items between the curly braces
       are printed on multiple lines, with appropriate indentation.
       This facilitates the compositional printing
       of compound sub-statements of statements;
       see how it is used in @(tsee print-stmt)."))
    (b* ((pstate (print-astring "{" pstate))
         (pstate (print-new-line pstate))
         (pstate (inc-pristate-indent pstate))
         (pstate (print-block-item-list items pstate))
         (pstate (dec-pristate-indent pstate))
         (pstate (print-indent pstate))
         (pstate (print-astring "}" pstate)))
      pstate)
    :measure (two-nats-measure (block-item-list-count items) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :ruler-extenders :all

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards print-stmt)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual print-stmts/blocks))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fundef ((fundef fundefp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one declaration specifier.")
   (xdoc::p
    "We ensure that the body is a compound statement.")
   (xdoc::p
    "Function definitions are always at the top level,
     so there is never any indentation to print.")
   (xdoc::p
    "If there is no declaration list,
     we print the open curly brace
     just after the declarator, separated by a space.
     Otherwise, we print a new line after the declarator,
     then the declarations at the left margin one per line,
     and finally the body with the curly brace starting at the left margin."))
  (b* (((fundef fundef) fundef)
       (pstate (if fundef.extension
                   (print-astring "__extension__ " pstate)
                 (pristate-fix pstate)))
       ((unless fundef.spec)
        (raise "Misusage error: no declaration specifiers.")
        pstate)
       ((unless (stmt-case fundef.body :compound))
        (raise "Misusage error: function body is not a compound statement.")
        (pristate-fix pstate))
       (pstate (print-declspec-list fundef.spec pstate))
       (pstate (print-astring " " pstate))
       (pstate (print-declor fundef.declor pstate))
       (pstate (if fundef.decls
                   (b* ((pstate (print-new-line pstate))
                        (pstate (print-decl-list fundef.decls pstate)))
                     pstate)
                 (print-astring " " pstate)))
       (pstate (print-block (stmt-compound->items fundef.body) pstate))
       (pstate (print-new-line pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-extdecl ((extdecl extdeclp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an external declaration."
  (extdecl-case
   extdecl
   :fundef (print-fundef extdecl.unwrap pstate)
   :decl (print-decl extdecl.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-extdecl-list ((extdecls extdecl-listp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a list of zero or more external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We separate them with blank lines."))
  (b* (((when (endp extdecls)) (pristate-fix pstate))
       (pstate (print-extdecl (car extdecls) pstate)))
    (print-extdecl-list (cdr extdecls) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-transunit ((tunit transunitp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that there is at least one external declaration,
     as required by the grammar."))
  (b* (((transunit tunit) tunit)
       ((unless tunit.decls)
        (raise "Misusage error: empty translation unit.")
        (pristate-fix pstate)))
    (print-extdecl-list tunit.decls pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-file ((tunit transunitp))
  :returns (data byte-listp)
  :short "Print (the data bytes of) a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input is a translation unit in the abstract syntax.
     We initialize the printing state,
     we print the translation unit,
     we extract the data bytes from the final printing state,
     and we reverse them (see @(tsee pristate)).")
   (xdoc::p
    "We set the indentation size to two spaces for now.
     In the future, we will make this a top-level parameter.
     We envision additional top-level parameters
     to customize various aspects of the printing (e.g. right margin)."))
  (b* ((indent-size 2)
       (pstate (init-pristate indent-size))
       (pstate (print-transunit tunit pstate))
       (bytes-rev (pristate->bytes-rev pstate)))
    (rev bytes-rev))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fileset ((tunits transunit-ensemblep))
  :returns (fileset filesetp)
  :short "Print a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input is a translation unit ensemble in the abstract syntax.
     We go through each translation unit in the ensemble and print it,
     obtaining a file for each.
     We return a file set that corresponds to the translation unit ensemble.
     The file paths are the same
     for the translation unit ensemble and for the file set
     (they are the keys of the maps)."))
  (fileset (print-fileset-loop (transunit-ensemble->unwrap tunits)))
  :hooks (:fix)

  :prepwork
  ((define print-fileset-loop ((tunitmap filepath-transunit-mapp))
     :returns (filemap filepath-filedata-mapp)
     :parents nil
     (b* (((when (omap::emptyp tunitmap)) nil)
          ((mv filepath tunit) (omap::head tunitmap))
          (data (print-file tunit))
          (filemap (print-fileset-loop (omap::tail tunitmap))))
       (omap::update (filepath-fix filepath) (filedata data) filemap))
     :verify-guards :after-returns

     ///

     (defret keys-of-print-fileset-loop
       (equal (omap::keys filemap)
              (omap::keys tunitmap))
       :hyp (filepath-transunit-mapp tunitmap)
       :hints (("Goal" :induct t))
     )))

  ///

  (defret keys-of-print-fileset
    (equal (omap::keys (fileset->unwrap fileset))
           (omap::keys (transunit-ensemble->unwrap tunits)))))

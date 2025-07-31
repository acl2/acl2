; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "files")
(include-book "grammar-characters")
(include-book "unambiguity")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)

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

(fty::defprod priopt
  :short "Fixtype of printer options."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixtype collects options that control
     various aspects of how the C code is printed.")
   (xdoc::p
    "Currently we support the following options:")
   (xdoc::ul
    (xdoc::li
     "The indentation size,
      i.e. how much each indentation level moves the starting column.
      This is measured in number of spaces, as a positive integer.")
    (xdoc::li
     "A flag saying whether conditional expressions
      nested in other conditional expressions
      should be parenthesized or not.
      For instance, whether the expression"
     (xdoc::codeblock "a ? b ? c : d : e ? f g")
     "should be printed as"
     (xdoc::codeblock "a ? (b ? c : e) : (e ? f : g)")
     "The two expressions are equivalent due to the precedence rules of C,
      but the second one is more readable.
      If the flag is @('t'), the printer adds the parentheses."))
   (xdoc::p
    "We may add more options in the future."))
  ((indent-size pos)
   (paren-nested-conds bool))
  :pred prioptp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define default-priopt ()
  :short "Default printer options."
  :long
  (xdoc::topstring
   (xdoc::p
    "For convenience, we provide a choice of default printer options,
     in the form of this nullary function,
     which can be passed to @(tsee print-fileset).")
   (xdoc::p
    "We set the indentation size to two spaces.")
   (xdoc::p
    "We do not add parentheses around nested conditionals."))
  (make-priopt :indent-size 2
               :paren-nested-conds nil))

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
    "We also keep track of the printing options (see @(tsee priopt)).
     These do not change in the course of the printing,
     but they are convenient to keep in the printing state,
     to avoid passing them around as an extra parameter.
     They are set when the printing state is initially created,
     and they never change.")
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
   (options priopt))
  :pred pristatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-pristate ((options prioptp))
  :returns (pstate pristatep)
  :short "Initial printer state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the printing options, which must be provided externally.")
   (xdoc::p
    "Initially, no data has been printed, and the indentation level is 0."))
  (make-pristate :bytes-rev nil
                 :indent-level 0
                 :options options)
  :hooks (:fix))

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
  :guard-hints (("Goal" :in-theory (enable grammar-character-p
                                           bytep
                                           unsigned-byte-p
                                           integer-range-p)))
  ///
  (fty::deffixequiv print-char
    :args ((pstate pristatep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                           (priopt->indent-size pstate.options))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
       (pstate (print-dec/oct/hex-const iconst.core pstate))
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
   :squote (print-astring "\\'" pstate)   ; \'
   :dquote (print-astring "\\\"" pstate)  ; \"
   :qmark (print-astring "\\?" pstate)    ; \?
   :bslash (print-astring "\\\\" pstate)  ; \\
   :a (print-astring "\\a" pstate)        ; \a
   :b (print-astring "\\b" pstate)        ; \b
   :f (print-astring "\\f" pstate)        ; \f
   :n (print-astring "\\n" pstate)        ; \n
   :r (print-astring "\\r" pstate)        ; \r
   :t (print-astring "\\t" pstate)        ; \t
   :v (print-astring "\\v" pstate)        ; \v
   :percent (print-astring "\\%" pstate)) ; \%
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
  (b* (((stringlit stringlit) stringlit)
       (pstate (print-eprefix-option stringlit.prefix? pstate))
       (pstate (print-astring "\"" pstate))
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

(define print-stor-spec ((stor-spec stor-specp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a storage class specifier."
  (stor-spec-case
   stor-spec
   :typedef (print-astring "typedef" pstate)
   :extern (print-astring "extern" pstate)
   :static (print-astring "static" pstate)
   :threadloc (print-astring "_Thread_local" pstate)
   :auto (print-astring "auto" pstate)
   :register (print-astring "register" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-type-qual ((tyqual type-qualp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a type qualifier."
  (type-qual-case
   tyqual
   :const (print-astring "const" pstate)
   :restrict (keyword-uscores-case
              tyqual.uscores
              :none (print-astring "restrict" pstate)
              :start (print-astring "__restrict" pstate)
              :both (print-astring "__restrict__" pstate))
   :volatile (keyword-uscores-case
              tyqual.uscores
              :none (print-astring "volatile" pstate)
              :start (print-astring "__volatile" pstate)
              :both (print-astring "__volatile__" pstate))
   :atomic (print-astring "_Atomic" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fun-spec ((funspec fun-specp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print a function specifier."
  (fun-spec-case
   funspec
   :inline (keyword-uscores-case
            funspec.uscores
            :none (print-astring "inline" pstate)
            :start (print-astring "__inline" pstate)
            :both (print-astring "__inline__" pstate))
   :noreturn (print-astring "_Noreturn" pstate))
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
       (pstate (keyword-uscores-case
                asmspec.uscores
                :none (print-astring "asm (" pstate)
                :start (print-astring "__asm (" pstate)
                :both (print-astring "__asm__ (" pstate)))
       ((unless (consp asmspec.strings))
        (raise "Misusage error: ~
                no string literals in assembler name specifier.")
        pstate)
       (pstate (print-stringlit-list asmspec.strings pstate))
       (pstate (print-astring ")" pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-qual ((qual asm-qualp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an assembler qualifier."
  (asm-qual-case
   qual
   :volatile (keyword-uscores-case
              qual.uscores
              :none (print-astring "volatile" pstate)
              :start (print-astring "__volatile" pstate)
              :both (print-astring "__volatile__" pstate))
   :inline (keyword-uscores-case
            qual.uscores
            :none (print-astring "inline" pstate)
            :start (print-astring "__inline" pstate)
            :both (print-astring "__inline__" pstate))
   :goto (print-astring "goto" pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-qual-list ((quals asm-qual-listp) (pstate pristatep))
  :guard (consp quals)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more assembler specifiers."
  (b* (((unless (mbt (consp quals))) (pristate-fix pstate))
       (pstate (print-asm-qual (car quals) pstate))
       ((when (endp (cdr quals))) pstate)
       (pstate (print-astring " " pstate)))
    (print-asm-qual-list (cdr quals) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-clobber ((clobber asm-clobberp) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an assembler clobber."
  (b* ((strings (asm-clobber->unwrap clobber))
       ((unless (consp strings))
        (raise "Misusage error: ~
                no string literals in assembler clobber.")
        (pristate-fix pstate)))
    (print-stringlit-list strings pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-asm-clobber-list ((clobbers asm-clobber-listp) (pstate pristatep))
  :guard (consp clobbers)
  :returns (new-pstate pristatep)
  :short "Print a list of one or more assembler clobbers, separated by commas."
  (b* (((unless (mbt (consp clobbers))) (pristate-fix pstate))
       (pstate (print-asm-clobber (car clobbers) pstate))
       ((when (endp (cdr clobbers))) pstate)
       (pstate (print-astring ", " pstate)))
    (print-asm-clobber-list (cdr clobbers) pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-attrib-name ((attrname attrib-namep) (pstate pristatep))
  :returns (new-pstate pristatep)
  :short "Print an attribute name."
  (attrib-name-case
   attrname
   :ident (print-ident attrname.unwrap pstate)
   :keyword (b* ((chars (acl2::string=>nats attrname.unwrap))
                 ((unless (grammar-character-listp chars))
                  (raise "Misusage error: ~
                          the attribute name keyword consists of ~
                          the character codes ~x0, ~
                          not all of which are allowed by the ABNF grammar."
                         chars)
                  (pristate-fix pstate)))
              (print-astring attrname.unwrap pstate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines print-exprs/decls/stmts
  :short "Print expressions, declarations, statements, and related entities."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-expr ((expr exprp)
                      (expected-prio expr-priorityp)
                      (pstate pristatep))
    :guard (expr-unambp expr)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
      "                          (expr-ident (ident \"x\") ...)"
      "                          (expr-ident (ident \"y\") ...))"
      "             (expr-ident (ident \"z\") ...)"
      "             ...)")
     (xdoc::p
      "(where @('...') is the additional information, irrelevant here)
       represents the expression @('(x + y) * z').
       When this expression is written in concrete syntax as just done,
       parentheses must be added,
       because @('*') binds tighter (i.e. has a higher priority) than @('+').")
     (xdoc::p
      "The relative priorities of C operators are implicitly defined
       by the grammar rules for expressions,
       which also define the left vs. right associativity
       of binary operators.
       For instance, the rules in [C17:6.5.5] and [C17:6.5.6] tell us that
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
       e.g. @('(expr-binary (binop-add) ... ... ...)')
       and @('(expr-binary (binop-sub) ... ... ...)')
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
       the nonterminal <i>expression</i> [C17:6.5.17].
       As we descend into subexpressions,
       the second argument of this function is changed according to
       the grammar rule corresponding to the super-expression.
       For instance, when printing the left and right subexpressions
       of a super-expression @('(expr-binary (binop-add) left right ...)'),
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
       different priorities (a form of subtyping).")
     (xdoc::p
      "We treat the printing of conditional expressions
       slightly differently based on the printer option
       about parenthesizing nested conditional expressions.
       The difference is in the expected priority
       used for the `then' and `else' subexpressions.
       If that flag is not set,
       we print things with minimal parentheses,
       and therefore we use
       the lowest expression priority
       for `then' and the conditional grade for `else',
       consistently with the grammar rule for conditional expressions.
       This means that if the `then' and/or `else' is a conditional expression,
       it is not parenthesized.
       If instead the flag is set,
       then we use a higher-priority for both `then' and `else',
       precisely the priority just one higher than conditional expressions,
       namely the priority of logical disjunction.
       This means that if the `then' and/or `else' is a conditional expression,
       it is parenthesized, in order to raise its priority."))
    (b* ((actual-prio (expr->priority expr))
         (parenp (expr-priority-< actual-prio expected-prio))
         (pstate (if parenp
                     (print-astring "(" pstate)
                   pstate))
         (pstate
          (expr-case
           expr
           :ident (print-ident expr.ident pstate)
           :const (print-const expr.const pstate)
           :string
           (b* (((unless expr.strings)
                 (raise "Misusage error: ~
                         empty list of string literals.")
                 (pristate-fix pstate)))
             (print-stringlit-list expr.strings pstate))
           :paren
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-expr expr.inner (expr-priority-expr) pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :gensel
           (b* ((pstate (print-astring "_Generic(" pstate))
                (pstate (print-expr expr.control (expr-priority-asg) pstate))
                (pstate (print-astring ", " pstate))
                ((unless expr.assocs)
                 (raise "Misusage error: ~
                         empty generic association list.")
                 pstate)
                (pstate (print-genassoc-list expr.assocs pstate))
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
                (pstate
                 (if (consp expr.elems)
                     (b* ((pstate (print-desiniter-list expr.elems pstate))
                          (pstate (if expr.final-comma
                                      (print-astring ", }" pstate)
                                    (print-astring "}" pstate))))
                       pstate)
                   (print-astring " }" pstate))))
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
           :sizeof-ambig (prog2$ (impossible) (pristate-fix pstate))
           :alignof
           (b* ((pstate (keyword-uscores-case
                         expr.uscores
                         :none (print-astring "_Alignof(" pstate)
                         :start (print-astring "__alignof(" pstate)
                         :both (print-astring "__alignof__(" pstate)))
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
           (b* ((raise-prio
                 (priopt->paren-nested-conds (pristate->options pstate)))
                (pstate (print-expr expr.test (expr-priority-logor) pstate))
                (pstate (print-astring " ? " pstate))
                (pstate (expr-option-case
                         expr.then
                         :some (b* ((pstate
                                     (print-expr expr.then.val
                                                 (if raise-prio
                                                     (expr-priority-logor)
                                                   (expr-priority-expr))
                                                 pstate))
                                    (pstate (print-astring " " pstate)))
                                 pstate)
                         :none pstate))
                (pstate (print-astring ": " pstate))
                (pstate (print-expr expr.else
                                    (if raise-prio
                                        (expr-priority-logor)
                                      (expr-priority-cond))
                                    pstate)))
             pstate)
           :comma
           (b* ((pstate (print-expr expr.first (expr-priority-expr) pstate))
                (pstate (print-astring ", " pstate))
                (pstate (print-expr expr.next (expr-priority-asg) pstate)))
             pstate)
           :cast/call-ambig (prog2$ (impossible) (pristate-fix pstate))
           :cast/mul-ambig (prog2$ (impossible) (pristate-fix pstate))
           :cast/add-ambig (prog2$ (impossible) (pristate-fix pstate))
           :cast/sub-ambig (prog2$ (impossible) (pristate-fix pstate))
           :cast/and-ambig (prog2$ (impossible) (pristate-fix pstate))
           :stmt
           (b* ((pstate (print-astring "(" pstate))
                (pstate (print-block expr.items pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :tycompat
           (b* ((pstate (print-astring "__builtin_types_compatible_p(" pstate))
                (pstate (print-tyname expr.type1 pstate))
                (pstate (print-astring ", " pstate))
                (pstate (print-tyname expr.type2 pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :offsetof
           (b* ((pstate (print-astring "__builtin_offsetof(" pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ", " pstate))
                (pstate (print-member-designor expr.member pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :va-arg
           (b* ((pstate (print-astring "__builtin_va_arg(" pstate))
                (pstate (print-expr expr.list (expr-priority-asg) pstate))
                (pstate (print-astring ", " pstate))
                (pstate (print-tyname expr.type pstate))
                (pstate (print-astring ")" pstate)))
             pstate)
           :extension
           (b* ((pstate (print-astring "__extension__ " pstate))
                (pstate (print-expr expr.expr (expr-priority-primary) pstate)))
             pstate)))
         (pstate (if parenp
                     (print-astring ")" pstate)
                   pstate)))
      pstate)
    :measure (two-nats-measure (expr-count expr) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-expr-list ((exprs expr-listp) (pstate pristatep))
    :guard (and (consp exprs)
                (expr-list-unambp exprs))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more expressions, separated by commas."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is used to print argument expressions of function calls,
       as well as parameters of GCC attributes
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
    :measure (two-nats-measure (expr-list-count exprs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-const-expr ((cexpr const-exprp) (pstate pristatep))
    :guard (const-expr-unambp cexpr)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "A constant expression is
       a synonym of a conditional expression in the grammar,
       so we use that as priority."))
    (print-expr (const-expr->expr cexpr) (expr-priority-cond) pstate)
    :measure (two-nats-measure (const-expr-count cexpr) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-genassoc ((genassoc genassocp) (pstate pristatep))
    :guard (genassoc-unambp genassoc)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (genassoc-count genassoc) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-genassoc-list ((genassocs genassoc-listp) (pstate pristatep))
    :guard (and (consp genassocs)
                (genassoc-list-unambp genassocs))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (genassoc-list-count genassocs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-member-designor ((memdes member-designorp) (pstate pristatep))
    :guard (member-designor-unambp memdes)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a member designator."
    (member-designor-case
     memdes
     :ident (print-ident memdes.ident pstate)
     :dot (b* ((pstate (print-member-designor memdes.member pstate))
               (pstate (print-astring "." pstate))
               (pstate (print-ident memdes.name pstate)))
            pstate)
     :sub (b* ((pstate (print-member-designor memdes.member pstate))
               (pstate (print-astring "[" pstate))
               (pstate (print-expr memdes.index (expr-priority-expr) pstate)))
            pstate))
    :measure (two-nats-measure (member-designor-count memdes) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-type-spec ((tyspec type-specp) (pstate pristatep))
    :guard (type-spec-unambp tyspec)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a type specifier."
    (type-spec-case
     tyspec
     :void (print-astring "void" pstate)
     :char (print-astring "char" pstate)
     :short (print-astring "short" pstate)
     :int (print-astring "int" pstate)
     :long (print-astring "long" pstate)
     :float (print-astring "float" pstate)
     :double (print-astring "double" pstate)
     :signed (keyword-uscores-case
              tyspec.uscores
              :none (print-astring "signed" pstate)
              :start (print-astring "__signed" pstate)
              :both (print-astring "__signed__" pstate))
     :unsigned (print-astring "unsigned" pstate)
     :bool (print-astring "_Bool" pstate)
     :complex (print-astring "_Complex" pstate)
     :atomic (b* ((pstate (print-astring "_Atomic(" pstate))
                  (pstate (print-tyname tyspec.type pstate))
                  (pstate (print-astring ")" pstate)))
               pstate)
     :struct (b* ((pstate (print-astring "struct " pstate))
                  (pstate (print-struni-spec tyspec.spec pstate)))
               pstate)
     :union (b* ((pstate (print-astring "union " pstate))
                 (pstate (print-struni-spec tyspec.spec pstate)))
              pstate)
     :enum (b* ((pstate (print-astring "enum " pstate))
                (pstate (print-enumspec tyspec.spec pstate)))
             pstate)
     :typedef (print-ident tyspec.name pstate)
     :int128 (print-astring "__int128" pstate)
     :float32 (print-astring "_Float32" pstate)
     :float32x (print-astring "_Float32x" pstate)
     :float64 (print-astring "_Float64" pstate)
     :float64x (print-astring "_Float64x" pstate)
     :float128 (print-astring "_Float128" pstate)
     :float128x (print-astring "_Float128x" pstate)
     :builtin-va-list (print-astring "__builtin_va_list" pstate)
     :struct-empty (b* ((pstate (print-astring "struct" pstate))
                        (pstate (if tyspec.name?
                                    (b* ((pstate (print-astring " " pstate))
                                         (pstate (print-ident tyspec.name?
                                                              pstate)))
                                      pstate)
                                  pstate))
                        (pstate (print-astring " { }" pstate)))
                     pstate)
     :typeof-expr
     (b* ((pstate (keyword-uscores-case
                   tyspec.uscores
                   :none (print-astring "typeof(" pstate)
                   :start (print-astring "__typeof(" pstate)
                   :both (print-astring "__typeof__(" pstate)))
          (pstate (print-expr tyspec.expr (expr-priority-expr) pstate))
          (pstate (print-astring ")" pstate)))
       pstate)
     :typeof-type
     (b* ((pstate (keyword-uscores-case
                   tyspec.uscores
                   :none (print-astring "typeof(" pstate)
                   :start (print-astring "__typeof(" pstate)
                   :both (print-astring "__typeof__(" pstate)))
          (pstate (print-tyname tyspec.type pstate))
          (pstate (print-astring ")" pstate)))
       pstate)
     :typeof-ambig (prog2$ (impossible) (pristate-fix pstate))
     :auto-type (print-astring "__auto_type" pstate))
    :measure (two-nats-measure (type-spec-count tyspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-spec/qual ((specqual spec/qual-p) (pstate pristatep))
    :guard (spec/qual-unambp specqual)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a specifier or qualifier."
    (spec/qual-case
     specqual
     :typespec (print-type-spec specqual.spec pstate)
     :typequal (print-type-qual specqual.qual pstate)
     :align (print-align-spec specqual.spec pstate)
     :attrib (print-attrib-spec specqual.spec pstate))
    :measure (two-nats-measure (spec/qual-count specqual) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-spec/qual-list ((specquals spec/qual-listp) (pstate pristatep))
    :guard (and (consp specquals)
                (spec/qual-list-unambp specquals))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more specifiers and qualifiers,
            separated by spaces."
    (b* (((unless (mbt (consp specquals))) (pristate-fix pstate))
         (pstate (print-spec/qual (car specquals) pstate))
         ((when (endp (cdr specquals))) pstate)
         (pstate (print-astring " " pstate)))
      (print-spec/qual-list (cdr specquals) pstate))
    :measure (two-nats-measure (spec/qual-list-count specquals) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-align-spec ((alignspec align-specp) (pstate pristatep))
    :guard (align-spec-unambp alignspec)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an alignment specifier."
    (b* ((pstate (print-astring "_Alignas(" pstate))
         (pstate
          (align-spec-case
           alignspec
           :alignas-type (print-tyname alignspec.type pstate)
           :alignas-expr (print-const-expr alignspec.expr pstate)
           :alignas-ambig (prog2$ (impossible) (pristate-fix pstate))))
         (pstate (print-astring ")" pstate)))
      pstate)
    :measure (two-nats-measure (align-spec-count alignspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-decl-spec ((declspec decl-specp) (pstate pristatep))
    :guard (decl-spec-unambp declspec)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a declaration specifier."
    (decl-spec-case
     declspec
     :stoclass (print-stor-spec declspec.spec pstate)
     :typespec (print-type-spec declspec.spec pstate)
     :typequal (print-type-qual declspec.qual pstate)
     :function (print-fun-spec declspec.spec pstate)
     :align (print-align-spec declspec.spec pstate)
     :attrib (print-attrib-spec declspec.spec pstate)
     :stdcall (print-astring "__stdcall" pstate)
     :declspec (b* ((pstate (print-astring "__declspec(" pstate))
                    (pstate (print-ident declspec.arg pstate))
                    (pstate (print-astring ")" pstate)))
                 pstate))
    :measure (two-nats-measure (decl-spec-count declspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-decl-spec-list ((declspecs decl-spec-listp) (pstate pristatep))
    :guard (and (consp declspecs)
                (decl-spec-list-unambp declspecs))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more declaration specifiers,
            separated by spaces."
    (b* (((unless (mbt (consp declspecs))) (pristate-fix pstate))
         (pstate (print-decl-spec (car declspecs) pstate))
         ((when (endp (cdr declspecs))) pstate)
         (pstate (print-astring " " pstate)))
      (print-decl-spec-list (cdr declspecs) pstate))
    :measure (two-nats-measure (decl-spec-list-count declspecs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-typequal/attribspec ((tyqualattrib typequal/attribspec-p)
                                     (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a type qualifier or attribute specifier."
    (typequal/attribspec-case
     tyqualattrib
     :type (print-type-qual tyqualattrib.unwrap pstate)
     :attrib (print-attrib-spec tyqualattrib.unwrap pstate))
    :measure (two-nats-measure (typequal/attribspec-count tyqualattrib) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-typequal/attribspec-list
    ((tyqualattribs typequal/attribspec-listp)
     (pstate pristatep))
    :guard (consp tyqualattribs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more
            type qualifiers and attribute specifiers,
            separated by spaces."
    (b* (((unless (mbt (consp tyqualattribs))) (pristate-fix pstate))
         (pstate (print-typequal/attribspec (car tyqualattribs) pstate))
         ((when (endp (cdr tyqualattribs))) pstate)
         (pstate (print-astring " " pstate)))
      (print-typequal/attribspec-list (cdr tyqualattribs) pstate))
    :measure (two-nats-measure (typequal/attribspec-list-count tyqualattribs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-typequal/attribspec-list-list
    ((tyqualattribss typequal/attribspec-list-listp)
     (pstate pristatep))
    :guard (consp tyqualattribss)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list or one or more lists of
            type qualifiers and attribute specifiers
            corresponding to a `pointer' in the grammar."
    :long
    (xdoc::topstring
     (xdoc::p
      "Our abstract syntax uses lists of lists of
       type qualifiers and attribute specifiers
       to model what the grammar calls `pointer',
       which is a sequence of one or more stars,
       each star followed by zero or more
       type qualifiers and attribute specifiers;
       see @(tsee declor) and @(tsee absdeclor).
       Here we print such a `pointer',
       from its representation as a list of lists of
       type qualifiers and attribute specifiers.")
     (xdoc::p
      "The outer list must not be empty, as required in the guard.
       We go through each inner list, printing a star for each;
       if the inner list under consideration is empty,
       the star is all we print;
       if the inner list is not empty,
       we also print a space,
       the type qualifiers and attribute specifiers (separated by spaces),
       and a space.
       That is, we provide separation when there are
       type qualifiers or attribute specifiers.
       But there are no extra separations for stars,
       e.g. we print @('**') for the list of lists @('(list nil nil)').
       Note that the last inner list is printed as just star."))
    (b* (((unless (mbt (consp tyqualattribss))) (pristate-fix pstate))
         (pstate (print-astring "*" pstate))
         (tyqualattribs (car tyqualattribss))
         (pstate (if (consp tyqualattribs)
                     (b* ((pstate (print-astring " " pstate))
                          (pstate (print-typequal/attribspec-list tyqualattribs
                                                                  pstate))
                          (pstate (print-astring " " pstate)))
                       pstate)
                   pstate))
         ((when (endp (cdr tyqualattribss))) pstate))
      (print-typequal/attribspec-list-list (cdr tyqualattribss) pstate))
    :measure (two-nats-measure
              (typequal/attribspec-list-list-count tyqualattribss) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-initer ((initer initerp) (pstate pristatep))
    :guard (initer-unambp initer)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (initer-count initer) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-desiniter ((desiniter desiniterp) (pstate pristatep))
    :guard (desiniter-unambp desiniter)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter)
         (pstate (if desiniter.designors
                     (b* ((pstate (print-designor-list desiniter.designors
                                                       pstate))
                          (pstate (print-astring " = " pstate)))
                       pstate)
                   pstate))
         (pstate (print-initer desiniter.initer pstate)))
      pstate)
    :measure (two-nats-measure (desiniter-count desiniter) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-desiniter-list ((desiniters desiniter-listp)
                                (pstate pristatep))
    :guard (and (consp desiniters)
                (desiniter-list-unambp desiniters))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more initializers with optional designations,
            separated by commas."
    (b* (((unless (mbt (consp desiniters))) (pristate-fix pstate))
         (pstate (print-desiniter (car desiniters) pstate))
         ((when (endp (cdr desiniters))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-desiniter-list (cdr desiniters) pstate))
    :measure (two-nats-measure (desiniter-list-count desiniters) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-designor ((designor designorp) (pstate pristatep))
    :guard (designor-unambp designor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (designor-count designor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-designor-list ((designors designor-listp)
                               (pstate pristatep))
    :guard (and (consp designors)
                (designor-list-unambp designors))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We print no separation between the designators."))
    (b* (((unless (mbt (consp designors))) (pristate-fix pstate))
         (pstate (print-designor (car designors) pstate))
         ((when (endp (cdr designors))) pstate))
      (print-designor-list (cdr designors) pstate))
    :measure (two-nats-measure (designor-list-count designors) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-declor ((declor declorp) (pstate pristatep))
    :guard (declor-unambp declor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a declarator."
    (b* (((declor declor) declor)
         (pstate (if (consp declor.pointers)
                     (print-typequal/attribspec-list-list declor.pointers
                                                          pstate)
                   pstate))
         (pstate (print-dirdeclor declor.direct pstate)))
      pstate)
    :measure (two-nats-measure (declor-count declor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-dirdeclor ((dirdeclor dirdeclorp) (pstate pristatep))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
     :ident (print-ident dirdeclor.ident pstate)
     :paren (b* ((pstate (print-astring "(" pstate))
                 (pstate (print-declor dirdeclor.inner pstate))
                 (pstate (print-astring ")" pstate)))
              pstate)
     :array
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirdeclor.qualspecs
                      (print-typequal/attribspec-list dirdeclor.qualspecs
                                                      pstate)
                    pstate))
          (pstate (if (and dirdeclor.qualspecs
                           dirdeclor.size?)
                      (print-astring " " pstate)
                    pstate))
          (pstate (if (expr-option-case dirdeclor.size? :some)
                      (print-expr (expr-option-some->val dirdeclor.size?)
                                  (expr-priority-asg)
                                  pstate)
                    pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static1
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
          (pstate (print-astring "static " pstate))
          (pstate (if dirdeclor.qualspecs
                      (b* ((pstate (print-typequal/attribspec-list
                                    dirdeclor.qualspecs
                                    pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-expr dirdeclor.size (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static2
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
          ((unless dirdeclor.qualspecs)
           (raise "Misusage error: ~
                   empty list of type qualifiers.")
           pstate)
          (pstate (print-typequal/attribspec-list dirdeclor.qualspecs pstate))
          (pstate (print-astring " static " pstate))
          (pstate (print-expr dirdeclor.size (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-star
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirdeclor.qualspecs
                      (b* ((pstate (print-typequal/attribspec-list
                                    dirdeclor.qualspecs
                                    pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring "*]" pstate)))
       pstate)
     :function-params
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
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
                      (print-param-declon-list dirdeclor.params pstate)
                    pstate))
          (pstate (if dirdeclor.ellipsis
                      (print-astring ", ...)" pstate)
                    (print-astring ")" pstate))))
       pstate)
     :function-names
     (b* ((pstate (print-dirdeclor dirdeclor.declor pstate))
          (pstate (print-astring "(" pstate))
          (pstate (if dirdeclor.names
                      (print-ident-list dirdeclor.names pstate)
                    pstate))
          (pstate (print-astring ")" pstate)))
       pstate))
    :measure (two-nats-measure (dirdeclor-count dirdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-absdeclor ((absdeclor absdeclorp) (pstate pristatep))
    :guard (absdeclor-unambp absdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the abstract declarator is not empty,
       i.e. it has at least the pointer part
       or the direct abstract declarator part."))
    (b* (((absdeclor absdeclor) absdeclor)
         ((unless (or absdeclor.pointers
                      absdeclor.direct?))
          (raise "Misusage error: ~
                  empty abstract declarator.")
          (pristate-fix pstate))
         (pstate (if absdeclor.pointers
                     (print-typequal/attribspec-list-list absdeclor.pointers
                                                          pstate)
                   pstate))
         (pstate (if (dirabsdeclor-option-case absdeclor.direct? :some)
                     (print-dirabsdeclor (dirabsdeclor-option-some->val
                                          absdeclor.direct?)
                                         pstate)
                   pstate)))
      pstate)
    :measure (two-nats-measure (absdeclor-count absdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-dirabsdeclor ((dirabsdeclor dirabsdeclorp) (pstate pristatep))
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a direct abstract declarator."
    (dirabsdeclor-case
     dirabsdeclor
     :dummy-base
     (prog2$ (raise "Misusage error: ~
                     dummy base case of direct abstract declarator.")
             (pristate-fix pstate))
     :paren
     (b* ((pstate (print-astring "(" pstate))
          (pstate (print-absdeclor dirabsdeclor.inner pstate))
          (pstate (print-astring ")" pstate)))
       pstate)
     :array
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.declor? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.declor?)
                       pstate)
                    pstate))
          (pstate (print-astring "[" pstate))
          (pstate (if dirabsdeclor.qualspecs
                      (print-typequal/attribspec-list dirabsdeclor.qualspecs
                                                      pstate)
                    pstate))
          (pstate (if (and dirabsdeclor.qualspecs
                           dirabsdeclor.size?)
                      (print-astring " " pstate)
                    pstate))
          (pstate (if (expr-option-case dirabsdeclor.size? :some)
                      (print-expr (expr-option-some->val dirabsdeclor.size?)
                                  (expr-priority-asg)
                                  pstate)
                    pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static1
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.declor? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.declor?)
                       pstate)
                    pstate))
          (pstate (print-astring "static " pstate))
          (pstate (if dirabsdeclor.qualspecs
                      (b* ((pstate (print-typequal/attribspec-list
                                    dirabsdeclor.qualspecs
                                    pstate))
                           (pstate (print-astring " " pstate)))
                        pstate)
                    pstate))
          (pstate (print-expr dirabsdeclor.size (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-static2
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.declor? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.declor?)
                       pstate)
                    pstate))
          ((unless dirabsdeclor.qualspecs)
           (raise "Misusage error: ~
                   empty list of type qualifiers.")
           (pristate-fix pstate))
          (pstate (print-typequal/attribspec-list dirabsdeclor.qualspecs pstate))
          (pstate (print-astring " static " pstate))
          (pstate (print-expr dirabsdeclor.size (expr-priority-asg) pstate))
          (pstate (print-astring "]" pstate)))
       pstate)
     :array-star
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.declor? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.declor?)
                       pstate)
                    pstate))
          (pstate (print-astring "[*]" pstate)))
       pstate)
     :function
     (b* ((pstate (if (dirabsdeclor-option-case dirabsdeclor.declor? :some)
                      (print-dirabsdeclor
                       (dirabsdeclor-option-some->val dirabsdeclor.declor?)
                       pstate)
                    pstate))
          (pstate (print-astring "(" pstate))
          (pstate (if dirabsdeclor.params
                      (b* ((pstate
                            (print-param-declon-list dirabsdeclor.params pstate))
                           (pstate (if dirabsdeclor.ellipsis
                                       (print-astring ", ..." pstate)
                                     pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring ")" pstate)))
       pstate))
    :measure (two-nats-measure (dirabsdeclor-count dirabsdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-param-declon ((param param-declonp) (pstate pristatep))
    :guard (param-declon-unambp param)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that there are declaration specifiers."))
    (b* (((param-declon param) param)
         ((unless param.specs)
          (raise "Misusage error: no declaration specifiers.")
          (pristate-fix pstate))
         (pstate (print-decl-spec-list param.specs pstate))
         (pstate (print-param-declor param.declor pstate)))
      pstate)
    :measure (two-nats-measure (param-declon-count param) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-param-declon-list ((params param-declon-listp)
                                   (pstate pristatep))
    :guard (and (consp params)
                (param-declon-list-unambp params))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more parameter declarations,
            separated by commas."
    (b* (((unless (mbt (consp params))) (pristate-fix pstate))
         (pstate (print-param-declon (car params) pstate))
         ((when (endp (cdr params))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-param-declon-list (cdr params) pstate))
    :measure (two-nats-measure (param-declon-list-count params) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-param-declor ((paramdeclor param-declorp) (pstate pristatep))
    :guard (param-declor-unambp paramdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is always called after printing
       the declaration specifiers that start a parameter declaration.
       Thus, if the parameter declarator is present,
       we print a space to separate the declaration specifiers
       from the declarator or abstract declarator."))
    (param-declor-case
     paramdeclor
     :nonabstract (b* ((pstate (print-astring " " pstate))
                       (pstate (print-declor paramdeclor.declor pstate)))
                    pstate)
     :abstract (b* ((pstate (print-astring " " pstate))
                    (pstate (print-absdeclor paramdeclor.declor pstate)))
                 pstate)
     :none (pristate-fix pstate)
     :ambig (prog2$ (impossible) (pristate-fix pstate)))
    :measure (two-nats-measure (param-declor-count paramdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-tyname ((tyname tynamep) (pstate pristatep))
    :guard (tyname-unambp tyname)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "We ensure that the list of specifiers and qualifiers is not empty."))
    (b* (((tyname tyname) tyname)
         ((unless tyname.specquals)
          (raise "Misusage error: empty list of specifiers and qualifiers.")
          (pristate-fix pstate))
         (pstate (print-spec/qual-list tyname.specquals pstate))
         ((unless (absdeclor-option-case tyname.declor? :some)) pstate)
         (pstate (print-astring " " pstate))
         (pstate (print-absdeclor (absdeclor-option-some->val tyname.declor?)
                                  pstate)))
      pstate)
    :measure (two-nats-measure (tyname-count tyname) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-struni-spec ((struni-spec struni-specp) (pstate pristatep))
    :guard (struni-spec-unambp struni-spec)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    (b* (((struni-spec struni-spec) struni-spec)
         ((unless (or (ident-option-case struni-spec.name? :some)
                      struni-spec.members))
          (raise "Misusage error: empty structure or union specifier.")
          (pristate-fix pstate))
         (pstate (ident-option-case
                  struni-spec.name?
                  :some (print-ident struni-spec.name?.val pstate)
                  :none pstate))
         (pstate (if (and struni-spec.name?
                          struni-spec.members)
                     (print-astring " " pstate)
                   pstate))
         ((when (not struni-spec.members)) pstate)
         (pstate (print-astring "{ " pstate))
         (pstate (print-structdecl-list struni-spec.members pstate))
         (pstate (print-astring " }" pstate)))
      pstate)
    :measure (two-nats-measure (struni-spec-count struni-spec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdecl ((structdecl structdeclp) (pstate pristatep))
    :guard (structdecl-unambp structdecl)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
          (pstate (print-spec/qual-list structdecl.specqual pstate))
          (pstate (if structdecl.declor
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-structdeclor-list structdecl.declor
                                                            pstate)))
                        pstate)
                    pstate))
          (pstate (if structdecl.attrib
                      (b* ((pstate (print-astring " " pstate))
                           (pstate (print-attrib-spec-list structdecl.attrib
                                                           pstate)))
                        pstate)
                    pstate))
          (pstate (print-astring ";" pstate)))
       pstate)
     :statassert (print-statassert structdecl.unwrap pstate)
     :empty (print-astring ";" pstate))
    :measure (two-nats-measure (structdecl-count structdecl) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdecl-list ((structdecls structdecl-listp)
                                 (pstate pristatep))
    :guard (and (consp structdecls)
                (structdecl-list-unambp structdecls))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more structure declarations,
            separated by spaces."
    :long
    (xdoc::topstring
     (xdoc::p
      "As mentioned in @(tsee print-struni-spec),
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
    :measure (two-nats-measure (structdecl-list-count structdecls) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdeclor ((structdeclor structdeclorp) (pstate pristatep))
    :guard (structdeclor-unambp structdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (structdeclor-count structdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-structdeclor-list ((structdeclors structdeclor-listp)
                                   (pstate pristatep))
    :guard (and (consp structdeclors)
                (structdeclor-list-unambp structdeclors))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more structure declarators,
            separated by commas."
    (b* (((unless (mbt (consp structdeclors))) (pristate-fix pstate))
         (pstate (print-structdeclor (car structdeclors) pstate))
         ((when (endp (cdr structdeclors))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-structdeclor-list (cdr structdeclors) pstate))
    :measure (two-nats-measure (structdeclor-list-count structdeclors) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumspec ((enumspec enumspecp) (pstate pristatep))
    :guard (enumspec-unambp enumspec)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
    :measure (two-nats-measure (enumspec-count enumspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumer ((enumer enumerp) (pstate pristatep))
    :guard (enumer-unambp enumer)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an enumerator."
    (b* (((enumer enumer) enumer)
         (pstate (print-ident enumer.name pstate))
         ((unless (const-expr-option-case enumer.value :some)) pstate)
         (pstate (print-astring " = " pstate))
         (pstate (print-const-expr (const-expr-option-some->val enumer.value)
                                   pstate)))
      pstate)
    :measure (two-nats-measure (enumer-count enumer) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-enumer-list ((enumers enumer-listp) (pstate pristatep))
    :guard (and (consp enumers)
                (enumer-list-unambp enumers))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more enumerators, separated by commas."
    (b* (((unless (mbt (consp enumers))) (pristate-fix pstate))
         (pstate (print-enumer (car enumers) pstate))
         ((when (endp (cdr enumers))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-enumer-list (cdr enumers) pstate))
    :measure (two-nats-measure (enumer-list-count enumers) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-statassert ((statassert statassertp) (pstate pristatep))
    :guard (statassert-unambp statassert)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a static assertion declaration."
    (b* (((statassert statassert) statassert)
         (pstate (print-astring "_Static_assert(" pstate))
         (pstate (print-const-expr statassert.test pstate))
         (pstate (print-astring ", " pstate))
         ((unless statassert.message)
          (raise "Misusage error: ~
                  empty message in static assertion declaration.")
          pstate)
         (pstate (print-stringlit-list statassert.message pstate))
         (pstate (print-astring ");" pstate)))
      pstate)
    :measure (two-nats-measure (statassert-count statassert) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-attrib ((attr attribp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a GCC attribute."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since our unambiguity predicates currently do not include attributes,
       here we perform a run-time check on the expressions."))
    (attrib-case
     attr
     :name-only (print-attrib-name attr.name pstate)
     :name-param
     (b* ((pstate (print-attrib-name attr.name pstate))
          (pstate (print-astring "(" pstate))
          ((unless (expr-list-unambp attr.param))
           (raise "Internal error: ambiguous expressions in attribute ~x0."
                  (attrib-fix attr))
           pstate)
          (pstate (if attr.param
                      (print-expr-list attr.param pstate)
                    pstate))
          (pstate (print-astring ")" pstate)))
       pstate))
    :measure (two-nats-measure (attrib-count attr) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-attrib-list ((attrs attrib-listp) (pstate pristatep))
    :guard (consp attrs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more GCC attributes, comma-separated."
    (b* (((unless (mbt (consp attrs))) (pristate-fix pstate))
         (pstate (print-attrib (car attrs) pstate))
         ((when (endp (cdr attrs))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-attrib-list (cdr attrs) pstate))
    :measure (two-nats-measure (attrib-list-count attrs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-attrib-spec ((attrspec attrib-specp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an attribute specifier."
    (b* (((attrib-spec attrspec) attrspec)
         (pstate (if attrspec.uscores
                     (print-astring "__attribute__ ((" pstate)
                   (print-astring "__attribute ((" pstate)))
         (pstate (if (consp attrspec.attribs)
                     (print-attrib-list attrspec.attribs pstate)
                   pstate))
         (pstate (print-astring "))" pstate)))
      pstate)
    :measure (two-nats-measure (attrib-spec-count attrspec) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-attrib-spec-list ((attrspecs attrib-spec-listp)
                                  (pstate pristatep))
    :guard (consp attrspecs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more attribute specifiers,
          separated by single spaces."
    (b* (((unless (mbt (consp attrspecs))) (pristate-fix pstate))
         (pstate (print-attrib-spec (car attrspecs) pstate))
         ((when (endp (cdr attrspecs))) pstate)
         (pstate (print-astring " " pstate)))
      (print-attrib-spec-list (cdr attrspecs) pstate))
    :measure (two-nats-measure (attrib-spec-list-count attrspecs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-initdeclor ((initdeclor initdeclorp) (pstate pristatep))
    :guard (initdeclor-unambp initdeclor)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an initializer declarator."
    (b* (((initdeclor initdeclor) initdeclor)
         (pstate (print-declor initdeclor.declor pstate))
         (pstate (if initdeclor.asm?
                     (b* ((pstate (print-astring " " pstate))
                          (pstate (print-asm-name-spec initdeclor.asm? pstate)))
                       pstate)
                   pstate))
         (pstate (if (consp initdeclor.attribs)
                     (b* ((pstate (print-astring " " pstate))
                          (pstate (print-attrib-spec-list initdeclor.attribs
                                                          pstate)))
                       pstate)
                   pstate))
         ((when (initer-option-case initdeclor.init? :none)) pstate)
         (pstate (print-astring " = " pstate))
         (pstate (print-initer (initer-option-some->val initdeclor.init?)
                               pstate)))
      pstate)
    :measure (two-nats-measure (initdeclor-count initdeclor) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-initdeclor-list ((initdeclors initdeclor-listp)
                                 (pstate pristatep))
    :guard (and (consp initdeclors)
                (initdeclor-list-unambp initdeclors))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more initializer declarators,
            separated by commas."
    (b* (((unless (mbt (consp initdeclors))) (pristate-fix pstate))
         (pstate (print-initdeclor (car initdeclors) pstate))
         ((when (endp (cdr initdeclors))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-initdeclor-list (cdr initdeclors) pstate))
    :measure (two-nats-measure (initdeclor-list-count initdeclors) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-decl-inline ((decl declp) (pstate pristatep))
    :guard (decl-unambp decl)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
          (pstate (print-decl-spec-list decl.specs pstate))
          (pstate
           (if decl.init
               (b* ((pstate (print-astring " " pstate))
                    (pstate (print-initdeclor-list decl.init pstate)))
                 pstate)
             pstate))
          (pstate (print-astring ";" pstate)))
       pstate)
     :statassert
     (print-statassert decl.unwrap pstate))
    :measure (two-nats-measure (decl-count decl) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-decl ((decl declp) (pstate pristatep))
    :guard (decl-unambp decl)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a declaration, in its own indented line."
    (b* ((pstate (print-indent pstate))
         (pstate (print-decl-inline decl pstate))
         (pstate (print-new-line pstate)))
      pstate)
    :measure (two-nats-measure (decl-count decl) 1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-decl-list ((decls decl-listp) (pstate pristatep))
    :guard (and (consp decls)
                (decl-list-unambp decls))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more declarations,
          one per line, all with the same indentation."
    (b* (((unless (mbt (consp decls))) (pristate-fix pstate))
         (pstate (print-decl (car decls) pstate))
         ((when (endp (cdr decls))) pstate))
      (print-decl-list (cdr decls) pstate))
    :measure (two-nats-measure (decl-list-count decls) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-label ((label labelp) (pstate pristatep))
    :guard (label-unambp label)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a label."
    (label-case
     label
     :name (print-ident label.unwrap pstate)
     :casexpr (b* ((pstate (print-astring "case " pstate))
                   (pstate (print-const-expr label.expr pstate)))
                (const-expr-option-case
                 label.range?
                 :some (b* ((pstate (print-astring " ... " pstate))
                            (pstate (print-const-expr label.range?.val pstate)))
                         pstate)
                 :none pstate))
     :default (print-astring "default" pstate))
    :measure (two-nats-measure (label-count label) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-asm-output ((output asm-outputp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an assembler output operand."
    (b* (((asm-output output) output)
         (pstate (if output.name
                     (b* ((pstate (print-astring "[" pstate))
                          (pstate (print-ident output.name pstate))
                          (pstate (print-astring "] " pstate)))
                       pstate)
                   pstate))
         (pstate (if (consp output.constraint)
                     (print-stringlit-list output.constraint pstate)
                   (prog2$
                    (raise "Misusage error: ~
                          no constraint in assembler output operand ~x0."
                           (asm-output-fix output))
                    pstate)))
         (pstate (print-astring " (" pstate))
         ((unless (expr-unambp output.lvalue))
          (raise "Internal error: ~
                ambiguous expression ~x0 in assembler output operand."
                 output.lvalue)
          pstate)
         (pstate (print-expr output.lvalue (expr-priority-expr) pstate))
         (pstate (print-astring ")" pstate)))
      pstate)
    :measure (two-nats-measure (asm-output-count output) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-asm-output-list ((outputs asm-output-listp) (pstate pristatep))
    :guard (consp outputs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more assembler output operands,
          separated by commas."
    (b* (((unless (mbt (consp outputs))) (pristate-fix pstate))
         (pstate (print-asm-output (car outputs) pstate))
         ((when (endp (cdr outputs))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-asm-output-list (cdr outputs) pstate))
    :measure (two-nats-measure (asm-output-list-count outputs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-asm-input ((input asm-inputp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an assembler input operand."
    (b* (((asm-input input) input)
         (pstate (if input.name
                     (b* ((pstate (print-astring "[" pstate))
                          (pstate (print-ident input.name pstate))
                          (pstate (print-astring "] " pstate)))
                       pstate)
                   pstate))
         (pstate (if (consp input.constraint)
                     (print-stringlit-list input.constraint pstate)
                   (prog2$
                    (raise "Misusage error: ~
                          no constraint in assembler input operand ~x0."
                           (asm-input-fix input))
                    pstate)))
         (pstate (print-astring " (" pstate))
         ((unless (expr-unambp input.rvalue))
          (raise "Internal error: ~
                ambiguous expression ~x0 in assembler input operand."
                 input.rvalue)
          pstate)
         (pstate (print-expr input.rvalue (expr-priority-expr) pstate))
         (pstate (print-astring ")" pstate)))
      pstate)
    :measure (two-nats-measure (asm-input-count input) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-asm-input-list ((inputs asm-input-listp) (pstate pristatep))
    :guard (consp inputs)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of one or more assembler input operands,
            separated by commas."
    (b* (((unless (mbt (consp inputs))) (pristate-fix pstate))
         (pstate (print-asm-input (car inputs) pstate))
         ((when (endp (cdr inputs))) pstate)
         (pstate (print-astring ", " pstate)))
      (print-asm-input-list (cdr inputs) pstate))
    :measure (two-nats-measure (asm-input-list-count inputs) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-asm-stmt ((asm asm-stmtp) (pstate pristatep))
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print an assembler statement."
    (b* (((asm-stmt stmt) asm)
         (pstate (print-indent pstate))
         (pstate (keyword-uscores-case
                  stmt.uscores
                  :none (print-astring "asm" pstate)
                  :start (print-astring "__asm" pstate)
                  :both (print-astring "__asm__" pstate)))
         (pstate (if (consp stmt.quals)
                     (b* ((pstate (print-astring " " pstate))
                          (pstate (print-asm-qual-list stmt.quals pstate)))
                       pstate)
                   pstate))
         (pstate (print-astring " (" pstate))
         ((unless (consp stmt.template))
          (raise "Misusage error: no string literals in assembler template.")
          pstate)
         (pstate (print-stringlit-list stmt.template pstate))
         ((unless (case stmt.num-colons
                    (0 (and (endp stmt.outputs)
                            (endp stmt.inputs)
                            (endp stmt.clobbers)
                            (endp stmt.labels)))
                    (1 (and (endp stmt.inputs)
                            (endp stmt.clobbers)
                            (endp stmt.labels)))
                    (2 (and (endp stmt.clobbers)
                            (endp stmt.labels)))
                    (3 (endp stmt.labels))
                    (4 t)
                    (otherwise nil)))
          (raise "Misusage error: ~
                  non-empty outputs, inputs, clobbers, or labels ~
                  with insufficient number of colons ~
                  in assembler statement ~x0."
                 (asm-stmt-fix stmt))
          pstate)
         (pstate
          (if (>= stmt.num-colons 1)
              (b* ((pstate (print-astring " :" pstate))
                   (pstate
                    (if (consp stmt.outputs)
                        (b* ((pstate (print-astring " " pstate))
                             (pstate (print-asm-output-list stmt.outputs
                                                            pstate)))
                          pstate)
                      pstate)))
                pstate)
            pstate))
         (pstate
          (if (>= stmt.num-colons 2)
              (b* ((pstate (print-astring " :" pstate))
                   (pstate
                    (if (consp stmt.inputs)
                        (b* ((pstate (print-astring " " pstate))
                             (pstate (print-asm-input-list stmt.inputs
                                                           pstate)))
                          pstate)
                      pstate)))
                pstate)
            pstate))
         (pstate
          (if (>= stmt.num-colons 3)
              (b* ((pstate (print-astring " :" pstate))
                   (pstate
                    (if (consp stmt.clobbers)
                        (b* ((pstate (print-astring " " pstate))
                             (pstate (print-asm-clobber-list stmt.clobbers
                                                             pstate)))
                          pstate)
                      pstate)))
                pstate)
            pstate))
         (pstate
          (if (>= stmt.num-colons 4)
              (b* ((pstate (print-astring " :" pstate))
                   (pstate
                    (if (consp stmt.labels)
                        (b* ((pstate (print-astring " " pstate))
                             (pstate (print-ident-list stmt.labels pstate)))
                          pstate)
                      pstate)))
                pstate)
            pstate))
         (pstate (print-astring " );" pstate))
         (pstate (print-new-line pstate)))
      pstate)
    :measure (two-nats-measure (asm-stmt-count asm) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-stmt ((stmt stmtp) (pstate pristatep))
    :guard (stmt-unambp stmt)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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
     :for-expr
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "for (" pstate))
          (pstate (expr-option-case
                   stmt.init
                   :some (print-expr stmt.init.val (expr-priority-expr) pstate)
                   :none (print-astring " " pstate)))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.test
                   :some (print-expr stmt.test.val (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.next
                   :some (print-expr stmt.next.val (expr-priority-expr) pstate)
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
     :for-decl
     (b* ((pstate (print-indent pstate))
          (pstate (print-astring "for (" pstate))
          (pstate (print-decl-inline stmt.init pstate))
          (pstate (print-astring " " pstate))
          (pstate (expr-option-case
                   stmt.test
                   :some (print-expr stmt.test.val (expr-priority-expr) pstate)
                   :none pstate))
          (pstate (print-astring "; " pstate))
          (pstate (expr-option-case
                   stmt.next
                   :some (print-expr stmt.next.val (expr-priority-expr) pstate)
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
     :for-ambig (prog2$ (impossible) (pristate-fix pstate))
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
       pstate)
     :asm
     (print-asm-stmt stmt.unwrap pstate))
    :measure (two-nats-measure (stmt-count stmt) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block-item ((item block-itemp) (pstate pristatep))
    :guard (block-item-unambp item)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a block item."
    (block-item-case
     item
     :decl (print-decl item.unwrap pstate)
     :stmt (print-stmt item.unwrap pstate)
     :ambig (prog2$ (impossible) (pristate-fix pstate)))
    :measure (two-nats-measure (block-item-count item) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block-item-list ((items block-item-listp) (pstate pristatep))
    :guard (block-item-list-unambp items)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
    :short "Print a list of zero or more block items."
    (b* (((when (endp items)) (pristate-fix pstate))
         (pstate (print-block-item (car items) pstate)))
      (print-block-item-list (cdr items) pstate))
    :measure (two-nats-measure (block-item-list-count items) 0))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define print-block ((items block-item-listp) (pstate pristatep))
    :guard (block-item-list-unambp items)
    :returns (new-pstate pristatep)
    :parents (printer print-exprs/decls/stmts)
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

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil

  ///

  (verify-guards print-expr
    :hints (("Goal" :in-theory (disable (:e tau-system))))) ; for speed

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual print-exprs/decls/stmts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fundef ((fundef fundefp) (pstate pristatep))
  :guard (fundef-unambp fundef)
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
       (pstate (print-decl-spec-list fundef.spec pstate))
       (pstate (print-astring " " pstate))
       (pstate (print-declor fundef.declor pstate))
       (pstate (if fundef.asm?
                   (b* ((pstate (print-astring " " pstate))
                        (pstate (print-asm-name-spec fundef.asm? pstate)))
                     pstate)
                 pstate))
       (pstate (if (consp fundef.attribs)
                   (b* ((pstate (print-astring " " pstate))
                        (pstate (print-attrib-spec-list fundef.attribs pstate)))
                     pstate)
                 pstate))
       (pstate (if fundef.decls
                   (b* ((pstate (print-new-line pstate))
                        (pstate (print-decl-list fundef.decls pstate)))
                     pstate)
                 (print-astring " " pstate)))
       ((unless (stmt-case fundef.body :compound))
        (raise "Misusage error: function body is not a compound statement.")
        (pristate-fix pstate))
       (pstate (print-block (stmt-compound->items fundef.body) pstate))
       (pstate (print-new-line pstate)))
    pstate)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-extdecl ((extdecl extdeclp) (pstate pristatep))
  :guard (extdecl-unambp extdecl)
  :returns (new-pstate pristatep)
  :short "Print an external declaration."
  (extdecl-case
   extdecl
   :fundef (print-fundef extdecl.unwrap pstate)
   :decl (print-decl extdecl.unwrap pstate)
   :empty (b* ((pstate (print-astring ";" pstate))
               (pstate (print-new-line pstate)))
            pstate)
   :asm (print-asm-stmt extdecl.unwrap pstate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-extdecl-list ((extdecls extdecl-listp) (pstate pristatep))
  :guard (extdecl-list-unambp extdecls)
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
  :guard (transunit-unambp tunit)
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

(define print-file ((tunit transunitp) (options prioptp))
  :guard (transunit-unambp tunit)
  :returns (data byte-listp)
  :short "Print (the data bytes of) a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input is a translation unit in the abstract syntax.
     We initialize the printing state,
     with the printing options passed as input.
     We print the translation unit,
     we extract the data bytes from the final printing state,
     and we reverse them (see @(tsee pristate))."))
  (b* ((pstate (init-pristate options))
       (pstate (print-transunit tunit pstate))
       (bytes-rev (pristate->bytes-rev pstate)))
    (rev bytes-rev))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-filepath-transunit-map ((tunitmap filepath-transunit-mapp)
                                      (options prioptp))
  :guard (filepath-transunit-map-unambp tunitmap)
  :returns (filemap filepath-filedata-mapp)
  :short "Print the files in a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input is a map from file paths to translation units,
     i.e. the core content of a translation unit ensemble.
     We also pass the printer options as additional input.
     We go through each translation unit in the map and print it,
     obtaining a file for each.
     We return a map from file paths to files
     that corresponds to the map from file paths to translation units.
     The two maps have the same keys."))
  (b* (((when (omap::emptyp tunitmap)) nil)
       ((mv filepath tunit) (omap::head tunitmap))
       (data (print-file tunit options))
       (filemap (print-filepath-transunit-map (omap::tail tunitmap) options)))
    (omap::update (filepath-fix filepath) (filedata data) filemap))
  :verify-guards :after-returns

  ///

  (defret keys-of-print-filepath-transunit-map
    (equal (omap::keys filemap)
           (omap::keys tunitmap))
    :hyp (filepath-transunit-mapp tunitmap)
    :hints (("Goal" :induct t)))

  (fty::deffixequiv print-filepath-transunit-map
    :args ((options prioptp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-fileset ((tunits transunit-ensemblep) (options prioptp))
  :guard (transunit-ensemble-unambp tunits)
  :returns (fileset filesetp)
  :short "Print a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input is a translation unit ensemble in the abstract syntax.
     We also pass the printer options as additional input.
     We unwrap the translation unit ensemble obtainining a map,
     we print the translation units of the map to files into a file map,
     and we wrap the file map into a file set."))
  (fileset
   (print-filepath-transunit-map (transunit-ensemble->unwrap tunits) options))
  :hooks (:fix)

  ///

  (defret keys-of-print-fileset
    (equal (omap::keys (fileset->unwrap fileset))
           (omap::keys (transunit-ensemble->unwrap tunits)))))

; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(include-book "std/strings/letter-uscore-chars" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-lexemes
  :parents (preprocessor)
  :short "Lexemes used by the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "These include not only preprocessing tokens,
     but also comments and white space (including new lines).")
   (xdoc::p
    "We introduce fixtypes for lexemes,
     along with operations on them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pnumber
  :short "Fixtype of preprocessing numbers [C17:6.4.8] [C17:A.1.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like an abstract syntax for preprocessing numbers,
     corresponding to the rule for @('pp-number') in the ABNF grammar.
     We need to capture their structure, in order to do preprocessing."))
  (:digit ((digit character
                  :reqfix (if (dec-digit-char-p digit)
                              digit
                            #\0)))
   :require (dec-digit-char-p digit))
  (:dot-digit ((digit character
                      :reqfix (if (dec-digit-char-p digit)
                                  digit
                                #\0)))
   :require (dec-digit-char-p digit))
  (:number-digit ((number pnumber)
                  (digit character
                         :reqfix (if (dec-digit-char-p digit)
                                     digit
                                   #\0)))
   :require (dec-digit-char-p digit))
  (:number-nondigit ((number pnumber)
                     (nondigit character
                               :reqfix (if (str::letter/uscore-char-p nondigit)
                                           nondigit
                                         #\_)))
   :require (str::letter/uscore-char-p nondigit))
  (:number-locase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-e-sign ((number pnumber)
                          (sign sign)))
  (:number-locase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-upcase-p-sign ((number pnumber)
                          (sign sign)))
  (:number-dot ((number pnumber)))
  :pred pnumberp
  :prepwork ((set-induction-depth-limit 1)
             (local (in-theory (enable fix (:e str::letter/uscore-char-p))))))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pnumber
  :short "An irrelevant preprocessing number."
  :type pnumberp
  :body (pnumber-digit #\0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum newline
  :short "Fixtype of new lines."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the rule @('new-line') in the ABNF grammar.
     Our preprocessor does not collapse them into a single new-line
     because it preserves white space, which includes new lines."))
  (:lf ())
  (:cr ())
  (:crlf ())
  :pred newlinep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-newline
  :short "An irrelevant new line."
  :type newlinep
  :body (newline-lf))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum plexeme
  :short "Fixtype of preprocessing lexemes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of preprocessing tokens [C17:6.4] [C17:A.1.1],
     with the addition of comments and white space:
     these are all the preprocessing lexemes,
     although [C17] does not use the word `lexeme'.")
   (xdoc::p
    "We reuse some of the fixtypes for ASTs here.")
   (xdoc::p
    "The @(':other') summand corresponds to
     the last alternative in the ABNF grammar rule for @('preprocessing-token'),
     as well as the prose description of the rule in [C17].
     It consists of the code of the character.")
   (xdoc::p
    "For (block and line) comments, we include the content,
     consisting of the codes of the characters.
     For block comments, these are all the characters
     from just after the opening @('/*') to just before the closing @('*/').
     For line comments, these are all the characters
     from just after the opening @('//') to just before the closing new line;
     recall that line comments exclude the ending new line [C17:6.4.9/2].")
   (xdoc::p
    "We keep the information about the three possible kinds of new-line,
     and of all other white space characters,
     according to the ABNF grammar rule for @('white-space').
     Since spaces (code 32) often occur in consecutive chunks,
     we represent them more efficiently as chunks, via positive counts."))
  (:header ((name header-name)))
  (:ident ((ident ident)))
  (:number ((number pnumber)))
  (:char ((const cconst)))
  (:string ((literal stringlit)))
  (:punctuator ((punctuator string)))
  (:other ((char nat)))
  (:block-comment ((content nat-list)))
  (:line-comment ((content nat-list)))
  (:newline ((chars newline)))
  (:spaces ((count pos)))
  (:horizontal-tab ())
  (:vertical-tab ())
  (:form-feed ())
  :pred plexemep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-plexeme
  :short "An irrelevant preprocessing lexeme."
  :type plexemep
  :body (plexeme-ident (ident :irrelevant)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption plexeme-option
  plexeme
  :short "Fixtype of optional preprocessing lexemes."
  :pred plexeme-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist plexeme-list
  :short "Fixtype of lists of preprocessing lexemes."
  :elt-type plexeme
  :true-listp t
  :elementp-of-nil nil
  :pred plexeme-listp

  ///

  (defruled true-listp-when-plexeme-listp
    (implies (plexeme-listp x)
             (true-listp x))
    :induct t
    :enable plexeme-listp)

  (defruled cdr-of-plexeme-list-fix
    (equal (cdr (plexeme-list-fix x))
           (plexeme-list-fix (cdr x)))
    :enable plexeme-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist plexeme-option-list
  :short "Fixtype of lists of optional preprocessing lexemes."
  :elt-type plexeme-option
  :true-listp t
  :elementp-of-nil t
  :pred plexeme-option-listp

  ///

  (defrule plexeme-option-listp-when-plexeme-listp
    (implies (plexeme-listp x)
             (plexeme-option-listp x))
    :induct t
    :enable plexeme-option-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-tokenp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to the grammar rule for <i>preprocessing-token</i>
     [C17:6.4] [C17:A.1.1]."))
  (and (member-eq (plexeme-kind lexeme)
                  '(:header
                    :ident
                    :number
                    :char
                    :string
                    :punctuator
                    :other))
       t)

  ///

  (defruled plexeme-tokenp-alt-def
    (equal (plexeme-tokenp lexeme)
           (not (member-eq (plexeme-kind lexeme)
                           '(:block-comment
                             :line-comment
                             :newline
                             :spaces
                             :horizontal-tab
                             :vertical-tab
                             :form-feed))))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-tokenp
    :args ((x plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-tokenp (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token."
  (plexeme-tokenp x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-tokenp
    :args ((x plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-token/newline-p ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token or a new line."
  :long
  (xdoc::topstring
   (xdoc::p
    "During preprocessing, new-line characters are significant:
     see grammar rules in [C17:6.10/1].
     Preprocessing is largely line-oriented.
     In our preprocessor, new-line characters are captured as new-line lexemes
     (see @(tsee plexeme))."))
  (or (plexeme-tokenp lexeme)
      (plexeme-case lexeme :newline)))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list is a token or new line."
  (plexeme-token/newline-p x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-token/newline-p
    :args ((x plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-not-token/newline-p (x)
  :guard (plexeme-listp x)
  :short "Check if no preprocessing lexeme in a list is a token or new line."
  (plexeme-token/newline-p x)
  :negatedp t
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-not-token/newline-p
    :args ((x plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-token/space-p ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a preprocessing lexeme is a token or a (single) space."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to represent, and facilitate comparison of,
     replacement lists of macros, as explained in more detail elsewhere."))
  (or (plexeme-tokenp lexeme)
      (and (plexeme-case lexeme :spaces)
           (equal (plexeme-spaces->count lexeme) 1))))

;;;;;;;;;;;;;;;;;;;;

(std::deflist plexeme-list-token/space-p (x)
  :guard (plexeme-listp x)
  :short "Check if every preprocessing lexeme in a list
          is a token or (single) space."
  (plexeme-token/space-p x)
  :elementp-of-nil t
  ///
  (fty::deffixequiv plexeme-list-token/space-p
    :args ((x plexeme-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-punctuatorp ((lexeme plexemep) (punctuator stringp))
  :returns (yes/no booleanp)
  :short "Check if a lexeme is a given punctuator."
  (and (plexeme-case lexeme :punctuator)
       (equal (plexeme-punctuator->punctuator lexeme)
              (str-fix punctuator))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-hashp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a lexeme is a hash @('#')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the lexeme is the punctuator @('#'),
     or also if the lexeme is the digraph @('%:') [C17:6.4.6/3]."))
  (and (plexeme-case lexeme :punctuator)
       (b* ((string (plexeme-punctuator->punctuator lexeme)))
         (or (equal string "#")
             (equal string "%:")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexeme-hashhashp ((lexeme plexemep))
  :returns (yes/no booleanp)
  :short "Check if a lexeme is a double hash @('##')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the lexeme is the punctuator @('#'),
     or also if the lexeme is the digraph @('%:%:') [C17:6.4.6/3]."))
  (and (plexeme-case lexeme :punctuator)
       (b* ((string (plexeme-punctuator->punctuator lexeme)))
         (or (equal string "##")
             (equal string "%:%:")))))

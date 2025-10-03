; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "parser-states")

(include-book "kestrel/fty/character-list" :dir :system)
(include-book "std/strings/letter-uscore-chars" :dir :system)

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor
  :parents (preprocessing)
  :short "A preprocessor for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a preprocessor for C that, unlike typical preprocessors,
     preserves the information about the @('#include') directives.
     That is, it does not replace such directives
     with the (preprocessed) contents of the referenced files,
     but it otherwise performs the rest of the preprocessing.")
   (xdoc::p
    "Our preprocessor maps a file set to a file set (see @(see files)).
     It reads characters and lexes them into lexemes,
     while executing the preprocessing directives.
     The resulting sequence of lexemes is then turned into characters
     that are written into files.
     The resulting file set is amenable to our parser
     (more precisely, it will be, once we have extended our parser
     to accept @('#include') directives in certain places,
     which we plan to do).
     Our preprocessor preserves white space, in order to preserve the layout
     (modulo the inherent layout changes caused by preprocessing).
     Our preprocessor also preserves comments,
     although some comments may no longer apply to preprocessed code
     (e.g. comments talking about macros).")
   (xdoc::p
    "Currently some of this preprocessor's code duplicates, at some level,
     some of the code in the @(see parser)
     (including the @(see lexer) and the @(see reader)).
     At some point we should integrate the preprocessor into the parser.")
   (xdoc::p
    "This preprocessor is very much work in progress."))
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
                  :reqfix (if (str::dec-digit-char-p digit)
                              digit
                            #\0)))
   :require (str::dec-digit-char-p digit))
  (:dot-digit ((digit character
                      :reqfix (if (str::dec-digit-char-p digit)
                                  digit
                                #\0)))
   :require (str::dec-digit-char-p digit))
  (:number-digit ((number pnumber)
                  (digit character
                         :reqfix (if (str::dec-digit-char-p digit)
                                     digit
                                   #\0)))
   :require (str::dec-digit-char-p digit))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum plexeme
  :short "Fixtype of preprocessing lexems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of preprocessing tokens [C17:6.4] [C17:A.1.1],
     with the addition of comments and white space.")
   (xdoc::p
    "We reuse some of the fixtypes for ASTs here.")
   (xdoc::p
    "The @(':other') case corresponds to
     the last alternative in the ABNF grammar rule for @('preprocessing-token'),
     as well as the prose description of the rule in [C17].
     It consists of the code of the character.")
   (xdoc::p
    "For (block and line) comments, we include the content,
     consisting of the codes of the characters.
     For block comments, these are all the characters
     from just after the opening @('/*') to just before the closing @('*/').
     For line comments, these are all the characters
     from just after the opening @('//') to just before the closing new-line.")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue

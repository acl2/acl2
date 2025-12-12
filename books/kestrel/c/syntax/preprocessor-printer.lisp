; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-states")

(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-printer
  :parents (preprocessor)
  :short "Printer component of the preprocessor."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our preprocessor
     reads files from specified paths,
     preprocessed them,
     and generates a file set with the files after preprocessing;
     see @(see preprocessor).
     The preprocessing of the files results in a list of lexemes,
     which we turn into bytes via this printer.")
   (xdoc::p
    "Since our preprocessing lexemes include whitespace,
     the printing is relatively easy.
     We do not need to add whitespace, keep track of indentation, etc.
     Compare this with the @(see printer).")
   (xdoc::p
    "Our printing functions take as input and return as output a list of bytes,
     which form the growing result in reverse.
     The list of bytes is extended by the printing functions
     via @(tsee cons) (which motivates the reversal of the list).
     The list of bytes is reversed after it is complete."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-lexeme ((lexeme plexemep) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a lexeme after preprocessing."
  (plexeme-case
   lexeme
   :header (byte-list-fix bytes) ; TODO
   :ident (byte-list-fix bytes) ; TODO
   :number (byte-list-fix bytes) ; TODO
   :char (byte-list-fix bytes) ; TODO
   :string (byte-list-fix bytes) ; TODO
   :punctuator (byte-list-fix bytes) ; TODO
   :other (byte-list-fix bytes) ; TODO
   :block-comment (byte-list-fix bytes) ; TODO
   :line-comment (byte-list-fix bytes) ; TODO
   :newline (byte-list-fix bytes) ; TODO
   :spaces (byte-list-fix bytes) ; TODO
   :horizontal-tab (byte-list-fix bytes) ; TODO
   :vertical-tab (byte-list-fix bytes) ; TODO
   :form-feed (byte-list-fix bytes) ; TODO
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-lexeme-list ((lexemes plexeme-listp) (bytes byte-listp))
  :returns (new-bytes byte-listp)
  :short "Print a list of lexemes after preprocessing."
  (b* (((when (endp lexemes)) (byte-list-fix bytes))
       (bytes (pprint-lexeme (car lexemes) bytes)))
    (pprint-lexeme-list (cdr lexemes) bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define plexemes-to-bytes ((lexemes plexeme-listp))
  :returns (bytes byte-listp)
  :short "Turn a list of preprocessor lexemes into a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top-level function of our printer.
     The reversed list of bytes is initialized to empty,
     and we call the top-level printing function,
     reversing the final byte list."))
  (rev (pprint-lexeme-list lexemes nil)))

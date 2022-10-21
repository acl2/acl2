; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-definer/defgrammar")
(include-book "../operations/in-terminal-set")

; (depends-on "imap.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imap-example
  :parents (examples)
  :short "The ABNF grammar of
          the IMAP (Internet Message Access Protocol) 4rev1 syntax."
  :long
  (xdoc::topstring-p
   "The IMAP 4rev1 syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc3501" "RFC 3501")
   ".")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *imap-grammar-rules*
  :short "The IMAP grammar rules from RFC 3501."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('imap.abnf') contains the grammar rules,
     copied and pasted from RFC 3501.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the IMAP grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The IMAP grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  :file "imap.abnf"
  :untranslate t
  :well-formed t)

; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 BAE Systems
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Letitia Li (letitia.li@baesystems.com)
;          Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-definer/defgrammar")
(include-book "../grammar-definer/deftreeops")

; (depends-on "pdf.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pdf-example
  :parents (examples)
  :short "An ABNF grammar of a subset of
          the PDF (Portable Document Format) syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "The PDF format is defined in "
    (xdoc::ahref "https://www.iso.org/standard/75839.html" "ISO 32000")
    ". The ABNF grammar given here is based on that standard,
     but is not part of that standard."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *pdf-grammar-rules*
  :short "The PDF grammar rules from our grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('pdf.abnf') contains the grammar rules.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the PDF grammar rules.")
   (xdoc::p
    "The PDF grammar rules are well-formed and closed.")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  :file "pdf.abnf"
  :untranslate t
  :well-formed t
  :closed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftreeops *pdf-grammar-rules* :prefix pdf-cst)

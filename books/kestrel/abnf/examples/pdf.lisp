; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2023 BAE Systems, Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Letitia Li (letitia.li@baesystems.com)
;          Alessandro Coglio (coglio@kestrel.edu)

(in-package "ACL2")

(include-book "../grammar-parser/executable")
(include-book "../notation/syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse the ABNF grammar of PDF into ACL2,
; and check that it is well-formed and closed.

(defsection *pdf-grammar-rules*
  :parents (examples)

  (make-event
   (mv-let (tree state)
     (abnf::parse-grammar-from-file "pdf.abnf" state)
     (value `(defconst *pdf-grammar-rules*
               (abnf::abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *pdf-grammar-rules*)

  (defrule rulelist-wfp-of-*pdf-grammar-rules*
    (abnf::rulelist-wfp *pdf-grammar-rules*))

  (defrule rulelist-closedp-of-*all-pdf-grammar-rules*
    (abnf::rulelist-closedp *pdf-grammar-rules*)))

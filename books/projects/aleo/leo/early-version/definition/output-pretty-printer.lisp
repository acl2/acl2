; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "output-files")
(include-book "pretty-printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions

(defrulel msgp-when-stringp
  (implies (stringp x)
           (msgp x)))

(defrulel msgp-when-consp-and-stringp-and-character-alistp
  (implies (and (consp x)
                (stringp (car x))
                (character-alistp (cdr x)))
           (msgp x)))

(local (in-theory (disable msgp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ output-pretty-printer
  :parents (concrete-syntax)
  :short "A pretty-printer for Leo output files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to the pretty-printer for Leo code files
     and to the pretty-printer for Leo input files.
     See @(see pretty-printer) for some information that applies here too."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-output-expression ((outexpr output-expressionp))
  :returns (part msgp)
  :short "Pretty-print an output expression."
  (pprint-expression (output-expression->get outexpr) (expr-grade-top))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-output-item ((outitem output-itemp) (level natp))
  :returns (line msgp)
  :short "Pretty-print an output item."
  (b* (((output-item outitem) outitem))
    (pprint-line
     (msg "~@0;"
          (pprint-output-expression outitem.get))
     level))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-output-title ((level natp))
  :returns (line msgp)
  :short "Pretty-print an output title."
  (pprint-line "[output]" level)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-output-section ((outsec output-sectionp))
  :returns (lines msg-listp)
  :short "Pretty-print an output section."
  :long
  (xdoc::topstring
   (xdoc::p
    "Add a blank line at the end."))
  (b* (((output-section outsec) outsec)
       (title (pprint-output-title 0))
       (item (pprint-output-item outsec.item 0)))
    (append (list title)
            (list item)
            (list (pprint-line-blank))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-output-file ((outfile output-filep))
  :returns (lines msg-listp)
  :short "Pretty-print an output file."
  (pprint-output-section (output-file->get outfile))
  :hooks (:fix))

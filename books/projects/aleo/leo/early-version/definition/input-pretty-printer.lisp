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

(include-book "input-files")
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

(defxdoc+ input-pretty-printer
  :parents (concrete-syntax)
  :short "A pretty-printer for Leo input files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to the pretty-printer for Leo code files.
     See @(see pretty-printer) for some information that applies here too."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-type ((intype input-typep))
  :returns (part msgp)
  :short "Pretty-print an input type."
  (pprint-type (input-type->get intype))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-expression ((inexpr input-expressionp))
  :returns (part msgp)
  :short "Pretty-print an input expression."
  (pprint-expression (input-expression->get inexpr) (expr-grade-top))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-item ((initem input-itemp) (level natp))
  :returns (line msgp)
  :short "Pretty-print an input item."
  (b* (((input-item initem) initem))
    (pprint-line
     (msg "~@0: ~@1 = ~@2;"
          (pprint-identifier initem.name)
          (pprint-input-type initem.type)
          (pprint-input-expression initem.value))
     level))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-item-list ((items input-item-listp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of input items."
  (cond ((endp items) nil)
        (t (cons (pprint-input-item (car items) level)
                 (pprint-input-item-list (cdr items) level)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-title ((intitle input-titlep) (level natp))
  :returns (line msgp)
  :short "Pretty-print an input title."
  (pprint-line (msg "[~@0]"
                    (input-title->sort intitle))
               level)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-section ((insec input-sectionp))
  :returns (lines msg-listp)
  :short "Pretty-print an input section."
  :long
  (xdoc::topstring
   (xdoc::p
    "Add a blank line at the end."))
  (b* (((input-section insec) insec)
       (first (pprint-input-title insec.title 0))
       (rest (pprint-input-item-list insec.items 0)))
    (append (list first)
            rest
            (list (pprint-line-blank)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-section-list ((insecs input-section-listp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of input sections."
  (cond ((endp insecs) nil)
        (t (append (pprint-input-section (car insecs))
                   (pprint-input-section-list (cdr insecs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-input-file ((infile input-filep))
  :returns (lines msg-listp)
  :short "Pretty-print an input file."
  (pprint-input-section-list (input-file->sections infile)))

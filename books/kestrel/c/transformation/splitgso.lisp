; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/unambiguity")

(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "std/system/w" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file is not complete. It is a partially filled template, to be completed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ splitgso
  :parents (transformation-tools)
  :short "A transformation to split a global struct object."
  :long
  (xdoc::topstring
   (xdoc::p
    "This transformation targets a global struct object,
     i.e. a file-scope (i.e. top-level) object (i.e. a global variable),
     that has a struct type.
     The transformation splits it into two objects, of two new struct types,
     each with a subset of the original struct members,
     which are divided between the two new struct types (and objects).
     References to (members of) the original object
     are replaced with references to one or the other object.")
   (xdoc::p
    "Currently this transformation operates on a single translation unit."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing splitgso)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that const-old is a symbol that denotes a named constant
; whole value is a translation unit ensemble with a single translation unit.
; Return its file path and translation unit if successful.

; Check that const-new is a symbol usable as a new named constant.
; (At least check that it is a symbol at all.)
; Return it unchanged, but with type symbolp for further use
; (or use suitable theorems).

; Check that object-name is an ACL2 string that is the name of
; a file-scope object with a single declaration in the translation unit,
; and satisfying additional conditions.
; Return it as an identifier, or more likely return more information,
; such as the whole declaration, or better its key constituents,
; maybe also the key constituents of the struct type.

; Probably add separate functions splitgso-process-<name-of-input>,
; which the following function calls.

(define splitgso-process-inputs (const-old
                                 const-new
                                 object-name
                                 (wrld plist-worldp))
  :returns (mv erp
               (filepath filepathp)
               (tunit transunitp)
               (object-ident identp)
               (const-new$ symbolp))
  :short "Process the inputs."
  (declare (ignore const-old const-new object-name wrld))
  (b* (((reterr)
        (filepath :irrelevant) (c$::irr-transunit) (c$::irr-ident) nil))
    (reterr :todo)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defpred)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate a defconst event with name const-new
; and value a translation unit ensemble consisting of
; a single translation unit with the given filepath.
; That single translation unit is the result of transforming tunit-old
; according to the design of the transformation.

; A call of deftrans would go here somethere.

(define splitgso-gen-everything ((filepath filepathp)
                                 (tunit transunitp)
                                 (object-ident identp)
                                 (const-new symbolp))
  :returns (mv erp (event pseudo-event-formp))
  :short "Generate all the events."
  (declare (ignore filepath tunit object-ident const-new))
  (b* (((reterr) '(_)))
    (reterr :todo)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-process-inputs-and-gen-everything (const-old
                                                    const-new
                                                    object-name
                                                    (wrld plist-worldp))
  :returns (mv erp (event pseudo-event-formp))
  :parents (splitgso-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp filepath
             tunit
             object-ident
             const-new)
        (splitgso-process-inputs const-old const-new object-name wrld))
       ((erp event)
        (splitgso-gen-everything filepath tunit object-ident const-new)))
    (retok event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define splitgso-fn (const-old
                     const-new
                     object-name
                     (ctx ctxp)
                     state)
  :returns (mv erp (event acl2::pseudo-event-formp) state)
  :parents (splitgso-implementation)
  :short "Event expansion of @(tsee splitgso)."
  (b* (((mv erp event)
        (splitgso-process-inputs-and-gen-everything const-old
                                                    const-new
                                                    object-name
                                                    (w state)))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection splitgso-macro-definition
  :parents (splitgso-implementation)
  :short "Definition of @(tsee splitgso)."
  (defmacro splitgso (const-old const-new &key object-name)
    `(make-event (splitgso-fn ',const-old
                              ',const-new
                              ',object-name
                              (w state)))))

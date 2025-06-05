; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "concrete-syntax")
(include-book "syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-interface
  :parents (pfcs)
  :short "API functions for parsing PFCS specifications."
  :long
  (xdoc::topstring
   (xdoc::p
    "This section defines API functions for parsing PFCS specifications
     from :")
   (xdoc::ul
; Uncomment when implemented.
;    (xdoc::li "a list of Unicode code points")
;    (xdoc::li "a list of UTF-8 bytes")
    (xdoc::li "an ACL2 string (in UTF-8)")
;    (xdoc::li "a file")
    )
   (xdoc::p
    "By \"parsing\", we mean lexing, tokenization, and parsing.
     We define functions that output CSTs and ASTs, so we honorarily
     include syntax abstraction as part of the parsing interface."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-from-string-to-cst ((pfcs-string stringp))
  :returns (tree abnf::tree-resultp)
  :short "Parse UTF-8 ACL2 string into a PFCS @('system') in CST form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a PFCS system expressed
     as a string of acl2 characters whose char-codes are UTF-8 bytes.
     Returns a PFCS @('system') CST (concrete syntax tree).")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('pfcs-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((tokens (tokenize-pfcs pfcs-string))
       ((when (reserrp tokens))
        tokens)
       ((mv top-object next-token rest-tokens) (parse-system tokens))
       ((when (reserrp top-object))
        top-object)
       ((unless (and (null next-token) (null rest-tokens)))
; A better error message such as the following would be good,
; but it currently doesn't work because fms-to-string is not in logic mode!
;        (reserrf (fms-to-string
;                "After parsing top-level PFCS system, there should be no more tokens.
; Next token is ~x0" (list next-token)))
        (reserrf (list next-token rest-tokens))))
    top-object))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example

(assert-event
 (let ((cst (parse-from-string-to-cst "boolean_and(x,y,z) := {
  x * y == z
}
boolean_and(w0, w1, w2)")))
   (and (not (reserrp cst))
        (abnf::treep cst)
        (abnf::check-tree-nonleaf-1-1 cst "system"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This could be called parse-from-string-to-AST,
; but we expect this to be the main API so we shorten the name.

(define parse ((pfcs-string stringp))
  :returns (sys system-resultp)
  :short "Parse UTF-8 ACL2 string into a PFCS @('system') in AST form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a PFCS system expressed
     as a string of ACL2 characters whose char-codes are UTF-8 bytes.
     Returns a PFCS @('system') AST (abstract syntax tree).")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('pfcs-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((cst (parse-from-string-to-cst pfcs-string))
       ((when (reserrp cst))
        cst)
       (ast (abs-system cst))
       ((when (reserrp ast))
          (reserrf (cons :problem-abstracting cst))))
    ast))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example

(assert-event
 (let ((cst (parse "boolean_and(x,y,z) := {
  x * y == z
}
boolean_and(w0, w1, w2)")))
   (equal cst
          '(:SYSTEM (DEFINITIONS (:DEFINITION (NAME . "boolean_and")
                                  (PARA "x" "y" "z")
                                  (BODY (:EQUAL (:MUL (:VAR "x") (:VAR "y"))
                                                (:VAR "z")))))
            (CONSTRAINTS (:RELATION "boolean_and"
                          ((:VAR "w0") (:VAR "w1") (:VAR "w2"))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a single definition.

(define parse-def ((pfcs-string stringp))
  :returns (sys definition-resultp)
  :short "Parse string into a PFCS @('definition') in AST form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lexes, tokenizes, and parses a PFCS @('system') containing a single
     definition and no extra constraints,
     as a string of ACL2 characters whose char-codes are UTF-8 bytes.
     Returns a PFCS @('definition') AST (abstract syntax tree).")
   (xdoc::p
    "If any step fails, returns a @(see reserr).
     The parse consumes the entire string or a @(see reserr) is returned.
     If the parsed PFCS @('system') contains other than one definition
     and zero constraints, returns a @(see reserr).")
   (xdoc::p
    "Since ACL2 strings are sequences of characters with codes from 0 to 255,
     @('pfcs-string'), when converted to codes, is required to be valid
     UTF-8."))
  (b* ((cst (parse-from-string-to-cst pfcs-string))
       ((when (reserrp cst))
        cst)
       (ast (abs-system cst))
       ((when (reserrp ast))
          (reserrf (cons :problem-abstracting cst)))
       (defs (system->definitions ast))
       (constraints (system->constraints ast))
       ((unless (and (consp defs) (null constraints)))
        (reserrf (cons :wrong-number-of-system-components cst))))
    (first defs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example

(assert-event
 (let ((def (parse-def "
  boolean_and(x,y,z) := {
    x * y == z
  }")))
   (equal def
          '(:DEFINITION (NAME . "boolean_and")
            (PARA "x" "y" "z")
            (BODY (:EQUAL (:MUL (:VAR "x") (:VAR "y"))
                   (:VAR "z")))))))

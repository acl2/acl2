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

(include-book "parser-interface")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (let ((cst (parse-from-string-to-cst "boolean_and(x,y,z) := {
  x * y == z
}
boolean_and(w0, w1, w2)")))
   (and (not (reserrp cst))
        (abnf::treep cst)
        (abnf::check-tree-nonleaf-1-1 cst "system"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (let ((ast (parse "boolean_and(x,y,z) := {
                    x * y == z
                    }
                    boolean_and(w0, w1, w2)")))
   (equal ast
          '(:SYSTEM
            (DEFINITIONS (:DEFINITION
                          (NAME :SIMPLE "boolean_and")
                          (PARA (:SIMPLE "x")
                                (:SIMPLE "y")
                                (:SIMPLE "z"))
                          (BODY (:EQUAL (:MUL (:VAR (:SIMPLE "x"))
                                         (:VAR (:SIMPLE "y")))
                                 (:VAR (:SIMPLE "z"))))))
            (CONSTRAINTS (:RELATION
                          (:SIMPLE "boolean_and")
                          ((:VAR (:SIMPLE "w0"))
                           (:VAR (:SIMPLE "w1"))
                           (:VAR (:SIMPLE "w2")))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (let ((def (parse-def"boolean_and(x,y,z) := {
                       x * y == z
                       }")))
   (equal def
          '(:DEFINITION (NAME :SIMPLE "boolean_and")
            (PARA (:SIMPLE "x")
                  (:SIMPLE "y")
                  (:SIMPLE "z"))
            (BODY (:EQUAL (:MUL (:VAR (:SIMPLE "x"))
                           (:VAR (:SIMPLE "y")))
                   (:VAR (:SIMPLE "z"))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Examples of neg and sub

;; sub and neg of identifier
(assert-event
 (let ((ast (parse "a - 1 == -b")))
   (equal ast
          '(:SYSTEM
            (DEFINITIONS)
            (CONSTRAINTS (:EQUAL
                          (:SUB (:VAR (:SIMPLE "a")) (:CONST 1))
                          (:NEG (:VAR (:SIMPLE "b")))))))))

;; sub and neg of numeral and neg of expression
(assert-event
 (let ((ast (parse "-2 == 1--(3 * 4)")))
   (equal ast
          '(:SYSTEM
            (DEFINITIONS)
            (CONSTRAINTS
             (:EQUAL (:NEG (:CONST 2))
              (:SUB (:CONST 1)
               (:NEG (:MUL (:CONST 3) (:CONST 4))))))))))

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
          '(:SYSTEM (DEFINITIONS (:DEFINITION (NAME . "boolean_and")
                                  (PARA "x" "y" "z")
                                  (BODY (:EQUAL (:MUL (:VAR "x") (:VAR "y"))
                                                (:VAR "z")))))
            (CONSTRAINTS (:RELATION "boolean_and"
                          ((:VAR "w0") (:VAR "w1") (:VAR "w2"))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Examples of neg and sub

;; sub and neg of identifier
(assert-event
 (let ((ast (parse "a - 1 == -b")))
   (equal ast
          '(:SYSTEM (DEFINITIONS)
            (CONSTRAINTS (:EQUAL (:SUB (:VAR "a") (:CONST 1))
                          (:NEG (:VAR "b"))))))))

;; sub and neg of numeral and neg of expression
(assert-event
 (let ((ast (parse "-2 == 1--(3 * 4)")))
   (equal ast
          '(:SYSTEM (DEFINITIONS)
            (CONSTRAINTS (:EQUAL (:NEG (:CONST 2))
                          (:SUB (:CONST 1)
                                (:NEG (:MUL (:CONST 3) (:CONST 4))))))))))

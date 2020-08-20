; Solidity Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOLIDITY")

(include-book "boolean-values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-operations
  :parents (boolean-values)
  :short (xdoc::topstring "Boolean operations " xdoc::*sld-types-booleans* ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "Since here we are formalizing the boolean operations on values,
     we do not capture here the short-circuiting of @('&&') and @('||') here.
     That is captured when formalizing the evaluation of expressions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-not ((operand boolp))
  :returns (result boolp)
  :short "Logical negation of boolean values."
  (b* ((x (bool->get operand)))
    (bool (not x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-and ((left-operand boolp) (right-operand boolp))
  :returns (result boolp)
  :short "Logical conjunction of boolean values."
  (b* ((x (bool->get left-operand))
       (y (bool->get right-operand)))
    (bool (and x y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-or ((left-operand boolp) (right-operand boolp))
  :returns (result boolp)
  :short "Logical disjunction of boolean values."
  (b* ((x (bool->get left-operand))
       (y (bool->get right-operand)))
    (bool (or x y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-eq ((left-operand boolp) (right-operand boolp))
  :returns (result boolp)
  :short "Equality of boolean values."
  (b* ((x (bool->get left-operand))
       (y (bool->get right-operand)))
    (bool (equal x y)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bool-ne ((left-operand boolp) (right-operand boolp))
  :returns (result boolp)
  :short "Inequality of boolean values."
  (b* ((x (bool->get left-operand))
       (y (bool->get right-operand)))
    (bool (not (equal x y))))
  :hooks (:fix))

; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/symbolic-execution-rules/top" :dir :system)
(include-book "kestrel/c/proof-support/const-ast-accessors" :dir :system)
(include-book "kestrel/c/proof-support/const-folding" :dir :system)
(include-book "kestrel/c/proof-support/exec-stmt-openers" :dir :system)
(include-book "kestrel/c/proof-support/exec-stmt-while-openers" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains supporting material for
; the strcpy-safe-induction.lisp example.
; This supporting material is generic, not specific to that example;
; it could be moved to general libraries.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#!c
(define varp ((var identp) (compst compustatep))
  :returns (yes/no booleanp)
  :short "Check if a named variable is in the computation state."
  (b* ((objdes (objdesign-of-var var compst)))
    (and objdes t)))

#!c
(define var->val ((var identp) (compst compustatep))
  :guard (varp var compst)
  :returns (val valuep)
  :short "Value of a variable in the computation state."
  (value-fix (read-object (objdesign-fix (objdesign-of-var var compst)) compst))
  :guard-hints
  (("Goal"
    :in-theory (enable varp valuep-of-read-object-of-objdesign-of-var))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#!c
(define val-pointer-uchar-array-alloc-p ((val valuep) (compst compustatep))
  :returns (yes/no booleanp)
  :short "Check is a value is a valid pointer (not null, not dangling)
          to an array of unsigned char values in allocated storage."
  (and (value-case val :pointer)
       (equal (value-pointer->reftype val) (type-uchar))
       (value-pointer-validp val)
       (b* ((objdes (value-pointer->designator val)))
         (and (objdesign-case objdes :alloc)
              (b* ((array (read-object objdes compst)))
                (uchar-arrayp array))))))

#!c
(define val-pointer-uchar-array-alloc->get ((val valuep) (compst compustatep))
  :guard (val-pointer-uchar-array-alloc-p val compst)
  :returns (mv (objdes objdesignp)
               (array uchar-arrayp)
               (vals value-listp))
  :short "Object designator, array value, and array component values of
          the array in allocated storage pointed to by a value."
  (b* ((objdes (value-pointer->designator val))
       (array (c::uchar-array-fix (read-object objdes compst)))
       (vals (value-array->elements array)))
    (mv objdes array vals))
  :guard-hints (("Goal" :in-theory (enable val-pointer-uchar-array-alloc-p
                                           valuep-when-uchar-arrayp
                                           value-kind-when-uchar-arrayp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#!c
(define var-pointer-uchar-array-alloc-p ((var identp) (compst compustatep))
  :returns (yes/no booleanp)
  :short "Check if a named variable contains
          a valid pointer (not null, not dangling)
          to an array of unsigned char values in allocated storage."
  (and (varp var compst)
       (b* ((val (var->val var compst)))
         (val-pointer-uchar-array-alloc-p val compst))))

#!c
(define var-pointer-uchar-array-alloc->get ((var identp) (compst compustatep))
  :guard (var-pointer-uchar-array-alloc-p var compst)
  :returns (mv (objdes objdesignp)
               (array uchar-arrayp)
               (vals value-listp))
  :short "Object designator, array value, and array component values of
          the array in allocated storage pointed to by a value in a variable."
  (val-pointer-uchar-array-alloc->get (var->val var compst) compst)
  :guard-hints (("Goal" :in-theory (enable var-pointer-uchar-array-alloc-p))))

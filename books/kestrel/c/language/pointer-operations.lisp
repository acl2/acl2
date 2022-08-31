; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pointer-operations
  :parents (language)
  :short "Operations on C pointers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-null ((reftype typep))
  :returns (ptr valuep)
  :short "Null pointer for a given referenced type."
  (make-value-pointer :designator? nil :reftype reftype)
  :hooks (:fix)
  ///
  (defret value-kind-of-value-pointer-null
    (equal (value-kind ptr) :pointer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-nullp ((ptr valuep))
  :guard (value-case ptr :pointer)
  :returns (yes/no booleanp)
  :short "Check if a pointer is null."
  (not (value-pointer->designator? ptr))
  :hooks (:fix)
  ///

  (defrule value-pointer-nullp-of-value-pointer
    (equal (value-pointer-nullp (value-pointer objdes type))
           (not objdes))
    :enable value-pointer-nullp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer->designator ((ptr valuep))
  :guard (and (value-case ptr :pointer)
              (not (value-pointer-nullp ptr)))
  :returns (design objdesignp)
  :short "Object designator of a non-null pointer."
  (objdesign-fix (value-pointer->designator? ptr))
  :guard-hints (("Goal" :in-theory (enable value-pointer-nullp)))
  :hooks (:fix)
  ///

  (defrule value-pointer->designator-of-value-pointer
    (equal (value-pointer->designator (value-pointer designator type))
           (objdesign-fix designator))
    :enable value-pointer->designator))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-pointer-value ((val valuep))
  :guard (value-case val :pointer)
  :returns (res booleanp)
  :short "Test a pointer value logically."
  :long
  (xdoc::topstring
   (xdoc::p
    "In some contexts (e.g. conditional tests),
     a pointer is treated as a logical boolean:
     false if null, true if not null.
     This is captured by this ACL2 function."))
  (not (value-pointer-nullp val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lognot-pointer-value ((val valuep))
  :guard (value-case val :pointer)
  :returns (resval valuep)
  :short "Apply @('!') to a pointer value [C:6.5.3.3/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This always returns an @('int') (never an error), either 0 or 1.
     It is equivalent to comparing the pointer for equality to 0,
     i.e. to check whether the pointer is null or not."))
  (if (value-pointer-nullp val)
      (value-sint 1)
    (value-sint 0))
  :hooks (:fix))

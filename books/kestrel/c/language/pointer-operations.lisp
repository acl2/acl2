; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "values")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
  (make-value-pointer :core (pointer-null) :reftype reftype)
  :hooks (:fix)
  ///
  (defret value-kind-of-value-pointer-null
    (equal (value-kind ptr) :pointer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-nullp ((ptr valuep))
  :guard (value-case ptr :pointer)
  :returns (yes/no booleanp)
  :short "Check if a pointer is null."
  (pointer-case (value-pointer->core ptr) :null)
  :hooks (:fix)
  ///

  (defrule value-pointer-nullp-of-value-pointer
    (equal (value-pointer-nullp (value-pointer core type))
           (pointer-case core :null))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-dangling ((reftype typep))
  :returns (ptr valuep)
  :short "Danling pointer for a given referenced type."
  (make-value-pointer :core (pointer-dangling) :reftype reftype)
  :hooks (:fix)
  ///
  (defret value-kind-of-value-pointer-dangling
    (equal (value-kind ptr) :pointer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-danglingp ((ptr valuep))
  :guard (value-case ptr :pointer)
  :returns (yes/no booleanp)
  :short "Check if a pointer is dangling."
  (pointer-case (value-pointer->core ptr) :dangling)
  :hooks (:fix)
  ///

  (defrule value-pointer-danglingp-of-value-pointer
    (equal (value-pointer-danglingp (value-pointer core type))
           (pointer-case core :dangling))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer-validp ((ptr valuep))
  :guard (value-case ptr :pointer)
  :returns (yes/no booleanp)
  :short "Check if a pointer is valid, i.e. it can be dereferenced."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this just means that the pointer is not null.
     However, when (as planned) we extend our model with dangling pointers,
     this predicate will also exclude dangling pointers.")
   (xdoc::p
    "Using `valid' for this notion is perhaps not ideal
     because null pointers are perfectly ``valid''values
     (in the sense of being legitimate values
     usable in correct and well-written code),
     even though they cannot be dereferenced.
     Perhaps we might change the name of this predicate in the future."))
  (pointer-case (value-pointer->core ptr) :valid)
  :hooks (:fix)
  ///

  (defrule value-pointer-validp-of-value-pointer
    (iff (value-pointer-validp (value-pointer core type))
         (pointer-case core :valid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer->designator ((ptr valuep))
  :guard (and (value-case ptr :pointer)
              (value-pointer-validp ptr))
  :returns (design objdesignp)
  :short "Object designator of a valid pointer."
  (pointer-valid->get (value-pointer->core ptr))
  :guard-hints (("Goal" :in-theory (enable value-pointer-validp)))
  :hooks (:fix)
  ///

  (defrule value-pointer->designator-of-value-pointer
    (equal (value-pointer->designator (value-pointer core type))
           (pointer-valid->get core))
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
  :short "Apply @('!') to a pointer value [C17:6.5.3.3/5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This always returns an @('int') (never an error), either 0 or 1.
     It is equivalent to comparing the pointer for equality to 0,
     i.e. to check whether the pointer is null or not."))
  (if (value-pointer-nullp val)
      (value-sint 1)
    (value-sint 0))
  :hooks (:fix)

  ///

  (defret type-of-value-of-lognot-pointer-value
    (equal (type-of-value resval)
           (type-sint))))

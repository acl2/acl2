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
  :short "Some operations on C pointers."
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
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-pointer->designator ((ptr valuep))
  :guard (and (value-case ptr :pointer)
              (not (value-pointer-nullp ptr)))
  :returns (design objdesignp)
  :short "Object designator of a non-null pointer."
  (objdesign-fix (value-pointer->designator? ptr))
  :guard-hints (("Goal" :in-theory (enable value-pointer-nullp)))
  :hooks (:fix))

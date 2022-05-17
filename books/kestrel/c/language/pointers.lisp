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

(include-book "types")
(include-book "object-designators")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pointers
  :parents (language)
  :short "A model of C pointers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Pointers are mentioned in several places in [C],
     but there seems to be no specific place in [C] that defines them.
     Nonetheless, we can get a precise picture from various places.
     [C:6.2.5/20] says that pointer types describe objects
     whose values provide references to entities.
     [C:6.3.2.3] specifies several things about pointers;
     in particular, it talks about null pointers.
     Thus, the picture is the following:
     a pointer is either an object designator or a null pointer
     (see the discussion in @(see object-designators)
     about lower-level addresses vs. higher-level object designators).
     In our defensive dynamic semantics, where values are tagged by their types,
     we also include, as part of the pointer,
     the type of its referenced value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pointer
  :short "Fixtype of pointers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Thus, we define a pointer as consisting of
     an optional object designator and a type.
     The object designator is absent for a null pointer;
     note that [C] does not prescribe 0 to represent a null pointer,
     even though 0 is used in null pointer constants [C:6.3.2.3/3].
     The type is not the pointer type, but the referenced type;
     this way, we avoid having to constrain the type to be a pointer type."))
  ((designator? objdesign-option)
   (reftype type))
  :tag :pointer
  :layout :list
  :pred pointerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer-nullp ((ptr pointerp))
  :returns (yes/no booleanp)
  :short "Check if a pointer is null."
  (not (pointer->designator? ptr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer-null ((reftype typep))
  :returns (ptr pointerp)
  :short "Null pointer for a given referenced type."
  (make-pointer :designator? nil :reftype reftype)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer->address ((ptr pointerp))
  :guard (not (pointer-nullp ptr))
  :returns (address addressp)
  :short "Address of a non-null pointer."
  (address-fix (objdesign->get (pointer->designator? ptr)))
  :guard-hints (("Goal" :in-theory (enable pointer-nullp)))
  :hooks (:fix))

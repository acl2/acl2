; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-pointers
  :parents (atc-dynamic-semantics)
  :short "A model of C pointers for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we use a simple model of pointers,
     which suffices for our current purposes.
     A pointer in our model is either null or an address,
     where an address is an essentially opaque entity
     whose sole purpose is to identify an object (in the C sense)
     allocated in some (externally populated) memory."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod address
  :short "Fixtype of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "Addresses are mentioned in several places in [C],
     but there seems to be no specific place in [C] that defines them.
     Nonetheless, based on how they are mentioned,
     it is quite clear that an address is essentially a hardware address,
     i.e. a number that identifies a memory location,
     even though [C] does not prescribe a particular representation.")
   (xdoc::p
    "For now we treat addresses as essentially abstract entities,
     whose only purpose is to identify objects in memory.
     We model addresses as natural numbers,
     but we do not use any properties of natural numbers.
     This fixtype wraps these natural numbers, for better abstraction."))
  ((number nat))
  :tag :address
  :pred addressp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption address-option
  address
  :short "Fixtype of optional addresses."
  :pred address-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pointer
  :short "Fixtype of pointers."
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
     a pointer is either an address or a null pointer.
     In our defensive dynamic semantics, where values are tagged by their types,
     we also include, as part of the pointer,
     the type of its referenced value.")
   (xdoc::p
    "Thus, we define a pointer as consisting of an optional address and a type.
     The address is absent for a null pointer;
     note that [C] does not prescribe 0 to represent a null pointer,
     even though 0 is used in null pointer constants [C:6.3.2.3/3].
     The type is not the pointer type, but the referenced type;
     this way, we avoid having to constrain the type to be a pointer type.
     The type of the pointer is the type of pointer to the referenced type."))
  ((address? address-option)
   (reftype type))
  :tag :pointer
  :pred pointerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer-nullp ((ptr pointerp))
  :returns (yes/no booleanp)
  :short "Check if a pointer is null."
  (not (pointer->address? ptr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointer-null ((reftype typep))
  :returns (ptr pointerp)
  :short "Null pointer for a given referenced type."
  (make-pointer :address? nil :reftype reftype)
  :hooks (:fix))

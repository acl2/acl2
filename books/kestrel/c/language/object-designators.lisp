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

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ object-designators
  :parents (language)
  :short "C object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C, an object is a region of storage that contains a value [C:3.15].
     This notion of object is not in the sense of object-oriented programming
     (in fact, C is not an object-oriented programming language).
     Here we introduce a notion of object designator,
     as an entity that (potentially) designates an object.
     This is in line with the terminology that defines the notion of lvalue
     [C:6.3.2/1].")
   (xdoc::p
    "At a low level, an object designator is an address in memory.
     However, in our model, we introduce
     a higher-level notion of object designator.
     We start by defining a notion of abstract addresses,
     used as top-level object designators,
     i.e. to designate separate objects in the heap.
     Then we allow object designators
     to include information that selects sub-objects of the those objects,
     and sub-sub-objects of those sub-objects,
     and so on.
     The selection information is of two kinds:
     an identifier that is
     the name of a member sub-object of a structure super-object,
     or a natural number that is
     the index of an element sub-object of an array super-object."))
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
     This fixtype wraps these natural numbers, for better abstraction.")
   (xdoc::p
    "As explained in @(see object-designators),
     we use these addresses to designate only whole objects in the heap,
     and not their sub-objects."))
  ((number nat))
  :tag :address
  :pred addressp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum objdesign
  :short "Fixtype of object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "An object designator is an address,
     or a (structure) member of an object designator,
     or an (array) element of an object designator.
     See @(see object-designators)."))
  (:address ((get address)))
  (:element ((super objdesign)
             (index nat)))
  (:member ((super objdesign)
            (name ident)))
  :pred objdesignp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption objdesign-option
  objdesign
  :short "Fixtype of optional object designators."
  :pred objdesign-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define objdesign->base-address ((objdes objdesignp))
  :returns (addr addressp)
  :short "Base address of an object designator."
  (objdesign-case objdes
                  :address objdes.get
                  :element (objdesign->base-address objdes.super)
                  :member (objdesign->base-address objdes.super))
  :measure (objdesign-count objdes)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define object-disjointp ((objdes1 objdesignp) (objdes2 objdesignp))
  :returns (yes/no booleanp)
  :short "Check if two designated objects are disjoint."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has to be a sufficient condition for disjointness,
     but not necessarily a necessary condition;
     that is, it can be a conservative definition,
     because it is only used to express when
     object updates are independent.
     For now, we require the two object designators to be addresses
     (i.e. top-level objects in the heap)
     and to be distinct.
     We may relax this notion in the future,
     but for now this suffices for our needs."))
  (and (objdesign-case objdes1 :address)
       (objdesign-case objdes2 :address)
       (not (equal (objdesign-address->get objdes1)
                   (objdesign-address->get objdes2))))
  :hooks (:fix)
  ///

  (defrule object-disjointp-commutative
    (equal (object-disjointp x y)
           (object-disjointp y x))))

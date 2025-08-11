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

(include-book "identifiers")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ object-designators
  :parents (language)
  :short "C object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C, an object is a region of storage that contains a value [C17:3.15].
     This notion of object is not in the sense of object-oriented programming
     (in fact, C is not an object-oriented programming language).
     Here we introduce a notion of object designator,
     as an entity that (potentially) designates an object.
     This is in line with the terminology that defines the notion of lvalue
     [C17:6.3.2/1].")
   (xdoc::p
    "At a low level, an object designator is an address in memory.
     However, in our model, we introduce
     a higher-level notion of object designator.
     We start by defining a notion of abstract addresses,
     used as top-level object designators for allocated storage,
     i.e. to designate separate objects in the heap.
     We also include top-level object designators for global variables,
     i.e. objects declared with file scope in static storage.
     We also include top-level object designators for local variables,
     i.e. objects declared with block scope in automatic storage.
     Then we allow object designators
     to include information that selects sub-objects of the top-level objects,
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
    "Addresses are mentioned in several places in [C17],
     but there seems to be no specific place in [C17] that defines them.
     Nonetheless, based on how they are mentioned,
     it is quite clear that an address is essentially a hardware address,
     i.e. a number that identifies a memory location,
     even though [C17] does not prescribe a particular representation.")
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
  :pred addressp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum objdesign
  :short "Fixtype of object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "An object designator is
     a named variable in static storage,
     or a named variable in automatic storage,
     or an address in allocated storage (i.e. the heap),
     or a (structure) member of an object designator,
     or an (array) element of an object designator.
     For a variable in automatic storage,
     we need not only the name,
     but also an indication of which scope in which frame the variable is in:
     we use natural numbers for this purpose,
     meant to be indices in the frame stack and scope stack.
     For both frames and scopes, index 0 refers to the bottom of the stack;
     this is the opposite order in which the stacks of frames and scopes
     are indexed as ACL2 lists (via @(tsee nth)),
     but we need this opposite order in order for the indices
     to be stable against frames and scopes being pushed and popped.")
   (xdoc::p
    "Also see @(see object-designators)."))
  (:static ((name ident)))
  (:auto ((name ident)
          (frame nat)
          (scope nat)))
  (:alloc ((get address)))
  (:element ((super objdesign)
             (index nat)))
  (:member ((super objdesign)
            (name ident)))
  :pred objdesignp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption objdesign-option
  objdesign
  :short "Fixtype of optional object designators."
  :pred objdesign-optionp)

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
     For now, we require the two object designators
     to be top-level designators in allocated storage
     and to be distinct.
     We may relax this notion in the future,
     but for now this suffices for our needs."))
  (and (objdesign-case objdes1 :alloc)
       (objdesign-case objdes2 :alloc)
       (not (equal (objdesign-alloc->get objdes1)
                   (objdesign-alloc->get objdes2))))
  :hooks (:fix)
  ///

  (defrule object-disjointp-commutative
    (equal (object-disjointp x y)
           (object-disjointp y x))))

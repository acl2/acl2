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

(include-book "centaur/fty/top" :dir :system)

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
    "At a low level, an object designator is an address.
     However, in our model, we introduce
     a higher-level notion of object designator.
     We start by defining it as an (abstract) address,
     but we plan to extend it to encompass more structured entities."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod objdesign
  :short "Fixtype of object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this is just a wrapper of an address,
     but we will extend with richer information."))
  ((get address))
  :pred objdesignp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption objdesign-option
  objdesign
  :short "Fixtype of optional object designators."
  :pred objdesign-optionp)

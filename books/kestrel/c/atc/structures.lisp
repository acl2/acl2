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

(defxdoc+ atc-structures
  :parents (atc-dynamic-semantics)
  :short "A model of C structures for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a model of structures (i.e. values of structure types).
     A structure is modeled as consisting of a tag
     and of a sequence of named members.
     For now each member has one of the values in @(tsee value),
     i.e. either an integer value or a pointer value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod member
  :short "Fixtype of structure members."
  :long
  (xdoc::topstring
   (xdoc::p
    "A member consists of a name and a value."))
  ((member ident)
   (value value))
  :tag :member
  :pred memberp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist member-list
  :short "Fixtype of lists of structure members."
  :elt-type member
  :true-listp t
  :elementp-of-nil nil
  :pred member-lisp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct
  :short "Fixtype of structures [C:6.2.5/20]."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be at least one member.
     The members must have distinct names.
     These requirements are currently not captured in this fixtype."))
  ((tag ident)
   (members member-list))
  :tag :struct
  :pred structp)

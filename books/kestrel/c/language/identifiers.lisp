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

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)

; to generate more typed list theorems in FTY::DEFLIST:
(local (include-book "std/lists/append" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifiers
  :parents (abstract-syntax)
  :short "Identifiers in the C abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an abstract notion of identifiers,
     used in our abstract syntax of C."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident
  :short "Fixtype of identifiers [C17:6.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we represent C identifiers as ACL2 strings,
     which suffice to represent all the ASCII C identifiers.
     We wrap ACL2 strings into a one-field product fixtype
     to make it easier to modify or extend this fixtype in the future.")
   (xdoc::p
    "Unconstrained ACL2 strings may not be valid C ASCII identifiers.
     In the future we may extend this fixtype
     with suitable restrictions on the ACL2 string.")
   (xdoc::p
    "A C implementation may limit
     the number of significant characters in identifiers
     [C17:6.4.2.1/5] [C17:6.4.2.1/6] [C17:5.2.4.1],
     to 31 for external identifiers and 63 for internal identifiers.
     In the future, we may add this constraint to this fixtype."))
  ((name string))
  :tag :ident
  :pred identp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ident-list
  :short "Fixtype of lists of identifiers."
  :elt-type ident
  :true-listp t
  :elementp-of-nil nil
  :pred ident-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset ident-set
  :short "Fixtype of sets of identifiers."
  :elt-type ident
  :elementp-of-nil nil
  :pred ident-setp)

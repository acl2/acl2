; Built-Ins Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "collect")
(include-book "document")
(include-book "disable")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc built-ins
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library about the ACL2 built-ins."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('collect.lisp') contains code
     to collect the names of all the built-in ACL2 events
     and to store them into named constants.
     That file also defines additional named constants
     that categorize functions and axioms and theorems;
     these could be potentially moved to a new file
     called @('categorize.lisp') at some point.")
   (xdoc::p
    "The file @('document.lisp') contains code
     to generate XDOC topics for the built-in axioms and theorems,
     organized in different ways.
     This makes it easier to see the built-in axioms and theorems
     than looking or searching through the source code.")
   (xdoc::p
    "The file @('disable.lisp') contains code
     that can be used to disable built-in functions and rules
     (the latter are axioms or theorems that have rule classes).
     This may be useful for more controlled and efficient proofs.")))

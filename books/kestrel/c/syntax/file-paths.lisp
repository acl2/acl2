; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ file-paths
  :parents (concrete-syntax)
  :short "File paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is more general than C,
     so it could be moved to a more general library."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod filepath
  :short "Fixtype of file paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize a file path as an isomorphic wrapping of a string.
     File paths can be normally represented as strings (e.g. in a terminal),
     and ACL2 strings, being isomorphic to lists of bytes,
     are expressive enough to represent Unicode (via UTF-8).")
   (xdoc::p
    "In the future we may refine this type with more internal structure,
     and/or with additional restrictions on the strings."))
  ((string string))
  :pred filepathp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-filepath
  :short "An irrelevant @(see filepath)."
  :type filepathp
  :body (filepath ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption filepath-option
  filepath
  :short "Fixtype of optional file paths."
  :pred filepath-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist filepath-list
  :short "Fixtype of lists of file paths."
  :elt-type filepath
  :true-listp t
  :elementp-of-nil nil
  :pred filepath-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset filepath-set
  :short "Fixtype of sets of file paths."
  :elt-type filepath
  :pred filepath-setp)

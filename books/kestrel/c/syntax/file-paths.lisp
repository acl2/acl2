; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ file-paths
  :parents (abstract-syntax concrete-syntax)
  :short "A simple notion of file paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used both for the concrete syntax notion of file sets
     and for the abstract syntax notion of ensembles of translation units.
     Both entities are finite maps from file paths to something,
     so the notion of file path is common to the two."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod filepath
  :short "Fixtype of file paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we formalize a file path as anything,
     which we wrap to keep things more abstract and separate.
     In the future we may refine this type with more structure.
     But note that, for instance,
     we could already use strings with slashes and such as file paths."))
  ((unwrap any))
  :pred filepathp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset filepath-set
  :short "Fixtype of sets of file paths."
  :elt-type filepath
  :pred filepath-setp)

; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ file-paths
  :parents (concrete-syntax)
  :short "A simple notion of file paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is factored into its own file and XDOC topic because,
     besides its primary use in our model of @(see files),
     it is also used in the abstract syntax,
     which can therefore just include this
     without including the model of files."))
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

(fty::defset filepath-set
  :short "Fixtype of sets of file paths."
  :elt-type filepath
  :pred filepath-setp)

; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc scalars
  :parents (basics)
  :short "Scalars."
  :long
  (xdoc::topstring
   (xdoc::p
    "[YP:3] says that scalars are
     non-negative integers in the set @($\\mathbb{N}$),
     i.e. natural numbers.")
   (xdoc::p
    "We use the library type <see topic='@(url fty::basetypes)'>@('nat')</see>
     to model scalars in our Ethereum model.")))

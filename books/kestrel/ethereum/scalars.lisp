; Ethereum Library -- Scalars
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc scalars
  :parents (basics)
  :short "Scalars."
  :long
  (xdoc::toppstring
   "[YP:3] says that scalars are
    non-negative integers in the set @($\\mathbb{N}$),
    i.e. natural numbers.
    We use the library type <see topic='@(url fty::basetypes)'>@('nat')</see>
    to model scalars in our Ethereum model."))

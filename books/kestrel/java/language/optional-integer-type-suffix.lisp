; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum optional-integer-type-suffix
  :parents (integer-literals)
  :short "Fixtype of optional integer type suffixes
          for integer literals [JLS:3.10.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer literal may have no integer type suffix,
     a lowercase @('l') integer type suffix, or
     an uppercase @('L') integer type suffix.
     Here we capture these three possibilities.")
   (xdoc::p
    "The lowercase and uppercase suffixes are equivalent,
     but we want to preserve the full information here."))
  (:none ())
  (:lowercase ())
  (:uppercase ()))

; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection mbt$
  :parents (std/basic-extensions std/basic)
  :short "Variant of @(tsee mbt) that allows any non-@('nil') value."
  :long
  (xdoc::topstring
   (xdoc::p
    "While @(tsee mbt)'s guard obligation requires
     the argument to be @(tsee equal) to @('t'),
     this variant only requires it to be @(tsee iff)-equivalent to @('t'),
     i.e. non-@('nil').")
   (xdoc::@def "mbt$"))

  (defmacro mbt$ (x)
    `(mbt (if ,x t nil))))

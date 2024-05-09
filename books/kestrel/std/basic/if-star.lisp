; Standard Basic Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/basic/if*
  :parents (std/basic-extensions std/basic)
  :short "Rules about @(tsee if*)."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules are unrelated to
     the special status of @(tsee if*) in BDD reasoning.
     These rules are useful when @(tsee if*) is used
     as a more controllable version of the built-in @(tsee if),
     e.g. so that ACL2 does not do unwanted case splits."))

  (defthmd if*-when-true
    (implies a
             (equal (if* a b c)
                    b)))

  (defthmd if*-when-false
    (implies (not a)
             (equal (if* a b c)
                    c)))

  (defthmd if*-when-same
    (equal (if* a b b) b)))

(in-theory (disable if*))

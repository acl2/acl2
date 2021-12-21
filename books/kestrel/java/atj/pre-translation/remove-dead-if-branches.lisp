; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "kestrel/std/system/remove-dead-if-branches" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-pre-translation-remove-dead-if-branches
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of dead @(tsee if) branches."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "If the test of an @(tsee if) is @('t'),
     we replace the @(tsee if) with the `then' branch;
     if the test of an @(tsee if) is @('nil'),
     we replace the @(tsee if) with the `else' branch.
     Note that the previous translation step
     may turn @(tsee mbt)s in @(tsee if) tests into @('t')s,
     so it is appropriate for this pre-translation step
     to come after the previous one.")
   (xdoc::p
    "We use the @(tsee remove-dead-if-branches) system utility.
     No other code is needed to do this in ATJ.")))

; Testing Utilities
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "misc/assert" :dir :system)
(include-book "misc/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-testing-utilities
  :parents (kestrel-utilities)
  :short "Utilities for testing that are part of the @(see kestrel-books)."
  :long
  "<p>
   The utilities that used to be here have been moved into
   @('[books]/misc/eval.lisp') and @('[books]/misc/assert.lisp').
   They can be found under the @(see testing-utilities) topic in the manual.
   </p>
   <p>
   New utilities may be (perhaps temporarily) added here in the future.
   </p>")

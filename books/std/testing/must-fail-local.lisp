; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-fail")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-local

  :parents (std/testing errors must-fail)

  :short "A @(see local) variant of @(tsee must-fail)."

  :long

  "<p>This is useful to overcome the problem discussed in the caveat
   in the documentation of @(tsee must-fail).</p>

   @(def must-fail-local)"

  (defmacro must-fail-local (&rest args)
    `(local (must-fail ,@args))))

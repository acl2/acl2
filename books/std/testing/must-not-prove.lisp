; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-fail")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-not-prove

  :parents (std/testing errors)

  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula does not get proved."

  :long

  "<p>This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-fail).</p>

   @(def must-not-prove)"

  (defmacro must-not-prove (&rest args)
    `(must-fail (thm ,@args))))

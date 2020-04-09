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

(include-book "must-succeed")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-prove

  :parents (std/testing errors)

  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula gets proved."

  :long

  "<p>This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-succeed).</p>

   @(def must-prove)"

  (defmacro must-prove (&rest args)
    `(must-succeed (thm ,@args))))

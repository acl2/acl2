; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/dumb-negate-lit
  :parents (std/system/term-transformations)
  :short "Theorems about @(tsee dumb-negate-lit)."

  (defthm pseudo-termp-of-dumb-negate-lit
    (implies (pseudo-termp term)
             (pseudo-termp (dumb-negate-lit term)))))

(in-theory (disable dumb-negate-lit))

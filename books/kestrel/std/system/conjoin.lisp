; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/conjoin
  :parents (std/system/term-transformations)
  :short "Theorems about @(tsee conjoin) and @(tsee conjoin2)."

  (defthm pseudo-termp-of-conjoin
    (implies (pseudo-term-listp terms)
             (pseudo-termp (conjoin terms))))

  (defthm pseudo-termp-of-conjoin2
    (implies (and (pseudo-termp term1)
                  (pseudo-termp term2))
             (pseudo-termp (conjoin2 term1 term2)))))

(in-theory (disable conjoin conjoin2))

; Lists of Values that are not Positive Integers
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist zp-listp (x)
  (posp x)
  :parents (kestrel-utilities)
  :short "Recognize true lists of @(tsee zp) values."
  :long
  "<p>
   A value satisfies @(tsee zp) iff it does not satisfy @(tsee posp).
   </p>
   <p>
   We use the @(':negatedp') feature of @(tsee std::deflist)
   because using @(tsee zp) (without @(':negatedp'))
   causes a guard violation.
   </p>"
  :true-listp t
  :negatedp t
  :elementp-of-nil nil)

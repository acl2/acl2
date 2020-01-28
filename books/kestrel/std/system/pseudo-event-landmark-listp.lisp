; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/pseudo-event-landmarkp" :dir :system)

(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-event-landmark-listp (x)
  (pseudo-event-landmarkp x)
  :parents (std/system)
  :short "Recognize true lists of event landmarks."
  :long
  (xdoc::topstring-p
   "See @('pseudo-event-landmarkp')
    in @('[books]/system/pseudo-event-landmarkp.lisp').")
  :true-listp t
  :elementp-of-nil nil)

; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/pseudo-event-form-listp" :dir :system)

(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pseudo-event-form-listp (x)
  (pseudo-event-formp x)
  :parents (std/system)
  :short (xdoc::topstring
          "Recognize true lists whose elements all have the "
          (xdoc::seetopic "pseudo-event-formp"
                          "basic structure of an event form")
          ".")
  :long (xdoc::topstring-@def "pseudo-event-form-listp")
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthmd true-listp-when-pseudo-event-form-listp-rewrite
    (implies (pseudo-event-form-listp x)
             (true-listp x))))

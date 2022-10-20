; FTY Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-event-form")

(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist pseudo-event-form-list
  :parents (fty::fty-extensions fty::specific-types pseudo-event-form-listp)
  :short "Fixtype of lists of pseudo event forms."
  :elt-type pseudo-event-form
  :true-listp t
  :elementp-of-nil nil
  :pred pseudo-event-form-listp)

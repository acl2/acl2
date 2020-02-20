; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-event-formp")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-pseudo-event-formp (x)
  :returns (yes/no booleanp)
  :parents (std/system)
  :short "Recognize @(tsee pseudo-event-formp) values and @('nil')."
  (or (pseudo-event-formp x)
      (null x))
  ///

  (defthm maybe-pseudo-event-formp-when-pseudo-event-formp
    (implies (pseudo-event-formp x)
             (maybe-pseudo-event-formp x))))

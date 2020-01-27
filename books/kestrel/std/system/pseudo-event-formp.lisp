; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/pseudo-event-formp" :dir :system)

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/pseudo-event-formp
  :parents (std/system)
  :short "Theorems about @(tsee pseudo-event-formp)."

  (defthm booleanp-of-pseudo-event-formp
    (booleanp (pseudo-event-formp x)))

  (defthm pseudo-event-formp-of-cons
    (equal (pseudo-event-formp (cons a b))
           (and (symbolp a)
                (true-listp b)))))

(in-theory (disable pseudo-event-formp))

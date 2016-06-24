; Event Forms
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides recognizers for event forms and lists thereof.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pseudo-event-formp (x)
  :returns (yes/no booleanp)
  :parents (kestrel-system-utilities)
  :short
  "True iff @('x') has the basic structure of an event form."
  :long
  "<p>
  Check whether @('x') is a
  non-empty, @('nil')-terminated list that starts with a symbol
  (like a function or macro call).
  </p>
  <p>
  This is a &ldquo;shallow&rdquo; check.
  Its satisfaction does not guarantee that @('x') is a valid event form.
  </p>"
  (and x
       (true-listp x)
       (symbolp (car x)))

  ///

  (defrule pseudo-event-formp-of-cons
    (equal (pseudo-event-formp (cons a b))
           (and (symbolp a)
                (true-listp b)))))

(std::deflist pseudo-event-form-listp (x)
  (pseudo-event-formp x)
  :parents (pseudo-event-formp)
  :short
  "True iff @('x') is a @('nil')-terminated list
  each of whose elements has the
  <see topic='@(url pseudo-event-formp)'>basic structure
  of an event form</see>."
  :true-listp t
  :elementp-of-nil nil)

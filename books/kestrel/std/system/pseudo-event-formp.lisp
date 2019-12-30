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

(defsection pseudo-event-formp
  :parents (std/system)
  :short "Recognize the basic structure of an event form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Check whether @('x') is a non-empty true list that starts with a symbol
     (like a function or macro call).")
   (xdoc::p
    "This is a shallow check.
     Its satisfaction does not guarantee that @('x') is a valid event form.")
   (xdoc::p
    "This function is defined in @('[books]/system/pseudo-event-formp.lisp').
     Here we add some documentation and theorems,
     and we disable the function.
     Perhaps the contents of this and that file could be merged at some point.")
   (xdoc::@def "pseudo-event-formp"))

  (defthm booleanp-of-pseudo-event-formp
    (booleanp (pseudo-event-formp x)))

  (defthm pseudo-event-formp-of-cons
    (equal (pseudo-event-formp (cons a b))
           (and (symbolp a)
                (true-listp b))))

  (in-theory (disable pseudo-event-formp)))

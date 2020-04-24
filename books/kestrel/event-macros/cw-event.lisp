; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection cw-event
  :parents (event-macros)
  :short "Event form of @(tsee cw)."
  :long
  (xdoc::topstring
   (xdoc::p
    "When this macro is processed as an event,
     its arguments are passed to @(tsee cw).")
   (xdoc::p
    "Exception: No printing is done while including a book
     or during the second pass of an @(tsee encapsulate) event.")
   (xdoc::@def "cw-event"))

  (defmacro cw-event (str &rest args)
    `(value-triple (cw ,str ,@args)
                   :on-skip-proofs :interactive)))

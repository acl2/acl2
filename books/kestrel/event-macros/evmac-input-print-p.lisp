; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defenum" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum evmac-input-print-p (nil :error :result :info :all)
  :short "Recognize a valid @(':print') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are ordered printing levels")
   (xdoc::codeblock
    "nil < :error < :result < :info < :all")
   (xdoc::p
    "where the amount of printed material increases monotonically.")
   (xdoc::p
    "When @(':print') is @('nil'),
     nothing is printed (not even errors).")
   (xdoc::p
    "When @(':print') is @(':error'),
     only errors (if any) are printed.")
   (xdoc::p
    "When @(':print') is @(':result'),
     besides errors (if any),
     also the generated events described in
     the event macro's reference documentation
     are printed,
     i.e. the resulting events.")
   (xdoc::p
    "When @(':print') is @(':info'),
     besides errors (if any)
     and the resulting events,
     also some additional information, specific to the event macro,
     is printed.")
   (xdoc::p
    "When @(':print') is @(':all'),
     besides errors (if any),
     the resulting events,
     and the additional information,
     also all the ACL2 output in response to the submitted events
     (the resulting ones and some ancillary ones).")))

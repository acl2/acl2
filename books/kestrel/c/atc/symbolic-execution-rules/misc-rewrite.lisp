; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/utilities/omaps/core" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-misc-rewrite-rules
  :short "Some miscellaneous rewrite rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "We should organize these into more clear categories,
     as done for most of the other rules."))

  (defval *atc-misc-rewrite-rules*
    '(car-cons
      cdr-cons
      compustate-fix-when-compustatep
      heap-fix-when-heapp
      mv-nth-of-cons
      omap::in-of-update
      value-list-fix-of-cons)))

; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classes ((thm symbolp) (wrld plist-worldp))
  :returns (classes "A @(tsee keyword-to-keyword-value-list-alistp).")
  :parents (std/system/theorem-queries)
  :short "Rule classes of a theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee classes+) for an enhanced variant of this utility."))
  (getpropc thm 'classes nil wrld))

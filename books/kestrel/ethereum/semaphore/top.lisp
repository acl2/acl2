; Ethereum Semaphore Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKSEMAPHORE")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semaphore
  :parents (ethereum::ethereum)
  :short "Ethereum's Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a proposed zero-knowledge gadget for Ethereum,
     but it may have wider applicability.
     See the "
    (xdoc::ahref "https://github.com/appliedzkp/semaphore"
                 "Ethereum Semaphore repository")
    " for more information."))
  :order-subtopics t)

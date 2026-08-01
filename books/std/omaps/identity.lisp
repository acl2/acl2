; Ordered Maps (Omaps) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "identityp")

(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identity ((keys set::setp))
  :returns (map mapp)
  :short "Build an identity map from a set."
  (b* (((when (set::emptyp keys)) nil)
       (key (set::head keys)))
    (update key key (identity (set::tail keys))))
  :verify-guards :after-returns

  ///

  (defret identityp-of-identity
    (identityp map)
    :hints (("Goal" :induct t)))

  (defret keys-of-identity
    (equal (keys map)
           (set::sfix keys))
    :hints (("Goal" :induct t))))

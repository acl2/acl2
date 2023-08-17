; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local (include-book "eviscerate-top-support"))

(verify-termination make-sharp-atsign) ; and guards
(verify-termination get-sharp-atsign) ; and guards
(verify-termination iprint-alistp1) ; and guards
(verify-termination iprint-alistp) ; and guards
(verify-termination iprint-falp) ; and guards
(verify-termination update-iprint-alist-fal) ; and guards
(verify-termination eviscerate1 (declare (xargs :verify-guards t)))
(verify-termination eviscerate1p) ; and guards
(verify-termination eviscerate) ; and guards
(verify-termination eviscerate-simple)
(verify-termination iprint-hard-bound (declare (xargs :verify-guards t)))
(verify-termination iprint-soft-bound (declare (xargs :verify-guards t)))
(verify-termination iprint-last-index*) ; and guards
(verify-termination iprint-last-index) ; and guards
(verify-termination iprint-ar-illegal-index) ; and guards
(verify-termination iprint-enabledp) ; and guards
(verify-termination iprint-blockedp) ; and guards
#+acl2-devel (verify-termination iprint-ar-aref1) ; and guards
(verify-termination iprint-alistp1-weak) ; and guards
(verify-termination collect-posp-indices-to-header) ; and guards
(verify-termination aset1-lst) ; and guards
(verify-termination iprint-fal-name) ; and guards
(verify-termination iprint-eager-p) ; and guards
(verify-termination init-iprint-fal) ; and guards
(verify-termination iprint-array-p) ; and guards
(verify-termination rollover-iprint-ar) ; and guards
(verify-termination update-iprint-fal-rec) ; and guards
(verify-termination update-iprint-fal) ; and guards
(verify-termination update-iprint-ar-fal) ; and guards
(verify-termination iprint-oracle-updates?) ; and guards
(verify-termination eviscerate-top-state-p) ; and guards
(verify-termination eviscerate-top) ; and guards

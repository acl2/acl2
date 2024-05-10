;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(defpkg "CLOSER"
  (append '(acl2::rfix-rfix
            acl2::REMOVE-RECIPORICALS-<
            acl2::remove-reciporicals-=
            )
          *acl2-exports*
          *common-lisp-symbols-from-main-lisp-package*))

; Printing an item to a string
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (in-theory (disable w table-alist get-global eviscerate-top-state-p
                           standard-evisc-tuplep fmt-state-p error1-state-p open-output-channel-p1
                           fmt1!
                           fmt1
                           fmt0
                           fmt-abbrev1
                           ;chk-current-package
                           error1
                           ;set-current-package
                           error-fms
                           add-pair
                           error-fms-channel
                           princ$
                           )))

(verify-termination chk-current-package)
;(verify-guards chk-current-package :otf-flg t) ;todo
(in-theory (disable chk-current-package))
(verify-termination set-current-package)
;(verify-guards set-current-package :hints (("Goal" :in-theory (enable chk-current-package error1))))
(verify-termination set-current-package-state)
;(verify-guards set-current-package-state :hints (("Goal" :in-theory (enable chk-current-package error1 error-fms))))
(verify-termination set-ppr-flat-right-margin)
;(verify-guards set-ppr-flat-right-margin)
(verify-termination set-iprint-ar)
;(verify-guards set-iprint-ar) ;todo
(verify-termination block-iprint-ar)
;(verify-guards block-iprint-ar) ;todo
(verify-termination override-global-evisc-table)
;(verify-guards override-global-evisc-table) ; todo: needs a guard
;(verify-guards set-ppr-flat-right-margin) ; todo: needs a aguard
(set-verify-guards-eagerness 0) ; todo
(verify-termination fmt1-to-string-fn)

;; todo: make this lowercase?
;; todo: verify guards
(defun print-to-string (item)
  (mv-let (col string)
    (fmt1-to-string "~X01" (acons #\0 item (acons #\1 nil nil)) 0
                    :fmt-control-alist
                    `((fmt-soft-right-margin . 10000)
                      (fmt-hard-right-margin . 10000)))
    (declare (ignore col))
    string))


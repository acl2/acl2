; Renaming functions in untranslated terms
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns the acl2-defaults-table as an alist.
(defund acl2-defaults-table-alist (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((result (table-alist 'acl2-defaults-table wrld)))
    (if (not (alistp result))
        (er hard? 'acl2-defaults-table-alist "ACL2 defaults table is not an alist.") ; should never happen
      result)))

(defthm alistp-of-acl2-defaults-table-alist
  (alistp (acl2-defaults-table-alist wrld))
  :hints (("Goal" :in-theory (enable acl2-defaults-table-alist))))

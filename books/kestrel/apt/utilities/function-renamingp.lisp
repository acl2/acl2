; Recognizer for an alist indicating how to rename functions
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/alists-light/lookup-equal" :dir :system)

(defun function-renamingp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (not (member-eq 'quote (strip-cdrs alist)))
       (symbol-listp (strip-cdrs alist))))

;recall that lookup-eq gets rewritten to lookup-equal, so we phrase this in terms of lookup-equal
(defthm symbolp-of-lookup-equal-when-function-renamingp
  (implies (function-renamingp function-renaming)
           (symbolp (lookup-equal key function-renaming)))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal))))

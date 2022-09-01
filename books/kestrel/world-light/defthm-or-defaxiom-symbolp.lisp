; A lightweight utility to recognize a defthm or axiom
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Can anything else have a 'theorem property?
(defun defthm-or-defaxiom-symbolp (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))))
  (if (getpropc name 'theorem
                nil ; no theorem can have a body of nil (it would be 'nil)
                wrld)
      t nil))

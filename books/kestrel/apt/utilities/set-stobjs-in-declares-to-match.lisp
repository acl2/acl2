; Setting the :stobjs xarg
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/declares0" :dir :system)

;; Set the :stobjs xarg in DECLARES to match what it would be for FN
(defun set-stobjs-in-declares-to-match (declares fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (all-declarep declares)
                              (true-listp declares)
                              (plist-worldp wrld))))
  (let* ((stobjs-in (getprop fn 'stobjs-in nil 'current-acl2-world wrld))
         (stobjs-in (true-list-fix stobjs-in)) ;todo: make a nicer accessor for stobjs-in that checks true-listp
         (stobj-formals (remove nil stobjs-in))
         (declares (if stobj-formals
                       (replace-xarg-in-declares :stobjs stobj-formals declares)
                     ;; Removal here may not be necesary but lets us completely
                     ;; control the :stobjs xarg:
                     (remove-xarg-in-declares :stobjs declares))))
    declares))

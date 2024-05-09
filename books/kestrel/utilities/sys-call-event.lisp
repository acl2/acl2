; A version of sys-call that is an event
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defttag sys-call-event)

;; Returns (mv erp event state).
(defun sys-call-event-fn (cmd args state)
  (declare (xargs :guard (and (stringp cmd)
                              (string-listp args))
                  :stobjs state))
  (mv-let (erp val state)
    (sys-call+ cmd args state)
    (prog2$ (cw "Command output:~%~s0~%" val)
            (if erp
                (prog2$ (er hard? 'sys-call-event-fn "Calling ~s0 on args ~x1 returned an error (status ~x2)." cmd args erp)
                        (mv :nonzero-exit-status nil state))
              (mv nil ; no error
                  '(value-triple :sys-call-event-ok)
                  state)))))

;; This is like sys-call but can be used in an event context.  Should throw an
;; error if the CMD returns a nonzero exit status (assuming the host Lisp
;; cooperates).
(defmacro sys-call-event (cmd args)
  `(make-event (sys-call-event-fn ,cmd ,args state)))

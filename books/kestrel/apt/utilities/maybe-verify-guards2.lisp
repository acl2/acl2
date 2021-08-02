; A utility for guard verification
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns a (possibly empty) list of events.  The verify-guards, if attempted,
;; is done in an empty ambient theory and with the supplied hints.
(defun maybe-verify-guards2 (verify-guards fn hints)
  (declare (xargs :guard (and (member-eq verify-guards '(t nil :auto))
                              (symbolp fn))))
  (and verify-guards
       `((encapsulate ()
           ;; attempt to prevent simplification from messing up the guard
           ;; conjecture before we try to prove it:
           (local (in-theory nil))
           (verify-guards ,fn
             :hints ,hints)))))

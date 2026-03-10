; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun eval-events-from-file-fn (filename state)
  (er-let* ((events (read-file filename state)))
    (value (cons 'progn events))))

(defmacro eval-events-from-file (filename)
  `(make-event (eval-events-from-file-fn ,filename state)))

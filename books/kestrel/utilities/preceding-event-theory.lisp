; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(program)

(defun preceding-event-theory-fn (wrld)
  (let* ((wrld0 (scan-to-event wrld)) ; as in (current-theory :here)
         (wrld1 (scan-to-event (cdr wrld0))))
    (current-theory-fn1 wrld1 wrld)))

(defmacro preceding-event-theory (&optional (world 'world))
; This gives the current-theory as of the immediately preceding event.
  (list 'preceding-event-theory-fn world))

; A variant of make-event that inhibits all output (except errors).
;
; Copyright (C) 2017 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defmacro make-event-quiet (&rest args)
  `(with-output
     :off :all
     ;; Keep errors and stuff printed using CW (which can be suppressed by
     ;; simply not calling CW):
     :on (comment error)
     :gag-mode nil
     (make-event ,@args)))


;; test:
(local (make-event-quiet '(defun f (x) x)))

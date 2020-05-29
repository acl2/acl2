; A utility to filter lists of events
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defun remove-event-types (bad-types events)
  (declare (xargs :guard (symbol-listp bad-types)))
  (if (atom events)
      nil
    (let ((event (first events)))
      (if (and (consp event)
               (not (member-eq (car event) bad-types)))
          (cons event (remove-event-types bad-types (rest events)))
        (remove-event-types bad-types (rest events))))))

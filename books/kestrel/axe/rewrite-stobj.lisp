; A stobj to gather parameters used in rewriting
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defstobj-plus" :dir :system)

(include-book "print-levels")

;; TODO: rename print0 to print once defstobj+ is fixed
(defstobj+ rewrite-stobj
  (known-booleans :type (satisfies symbol-listp) :initially nil)
  (monitored-symbols :type (satisfies symbol-listp) :initially nil)
  (print0 :type (satisfies axe-print-levelp) :initially nil)
  :inline t
  :renaming ((known-booleans get-known-booleans)
             (update-known-booleans put-known-booleans)
             (monitored-symbols get-monitored-symbols)
             (update-monitored-symbols put-monitored-symbols)
             (print0p printp)
             (print0 get-print)
             (update-print0 put-print)))

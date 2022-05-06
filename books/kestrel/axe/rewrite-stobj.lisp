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

(defstobj+ rewrite-stobj
  (known-booleans :type (satisfies symbol-listp) :initially nil)
  (monitored-symbols :type (satisfies symbol-listp) :initially nil)
  (print :type (satisfies axe-print-levelp) :initially nil)
  (normalize-xors :type (satisfies booleanp) :initially nil)
  :inline t
  :renaming ((known-booleans get-known-booleans)
             (update-known-booleans put-known-booleans)
             (monitored-symbols get-monitored-symbols)
             (update-monitored-symbols put-monitored-symbols)
             (common-lisp::printp printp)
             (common-lisp::print get-print)
             (common-lisp::update-print put-print)
             (normalize-xors get-normalize-xors)
             (update-normalize-xors put-normalize-xors)))

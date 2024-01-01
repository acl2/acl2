; A stobj to gather parameters used in rewriting
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/print-levels" :dir :system)

;; TODO: Consider adding more things to this, such as:
;; interpreted-function-alist, memoization, info, tries, limits.

(defstobj+ rewrite-stobj
  ;; Functions that are known to be boolean in the current world:
  (known-booleans :type (satisfies symbol-listp) :initially nil)
  ;; Names of rules we are monitoring:
  (monitored-symbols :type (satisfies symbol-listp) :initially nil)
  ;; How much to print while rewriting:
  (print :type (satisfies print-levelp) :initially nil)
  ;; Whether to use our special-purpose code to normalize nests of XORs:
  (normalize-xors :type (satisfies booleanp) :initially nil)
  :inline t
  :renaming ((known-booleans get-known-booleans)
             (update-known-booleans put-known-booleans)
             (monitored-symbols get-monitored-symbols)
             (update-monitored-symbols put-monitored-symbols)
             (common-lisp::printp printp) ; can we avoid having defstobj define printp, which just calls print-levelp?
             (common-lisp::print get-print)
             (common-lisp::update-print put-print)
             (normalize-xors get-normalize-xors)
             (update-normalize-xors put-normalize-xors)))

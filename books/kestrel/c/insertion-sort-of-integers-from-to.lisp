; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "insertion-sort")

(include-book "kestrel/utilities/integers-from-to" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled insertion-sort-of-integers-from-to
  :parents (insertion-sort integers-from-to)
  :short "Applying insertion sort to an ordered list of integers in a range
          yields the same list."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be moved to a more general library."))
  (implies (and (integerp min)
                (integerp max))
           (equal (insertion-sort (integers-from-to min max))
                  (integers-from-to min max)))
  :induct t
  :enable (integers-from-to
           insertion-sort
           ifix)
  :prep-lemmas
  ((defrule lemma
     (implies (and (integerp min)
                   (integerp max)
                   (<= min max))
              (equal (insertion-sort-insert min
                                            (integers-from-to (1+ min) max))
                     (integers-from-to min max)))
     :induct t
     :enable (integers-from-to
              insertion-sort-insert
              ifix
              <<
              lexorder
              alphorder))))

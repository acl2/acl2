; Adding a conjunct
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)

;; Conjoin CONJUNCT to ITEM, adding it as the last conjunct (in case its guard
;; requires ITEM to be true), unless it is already clearly present as a
;; conjunct.  CONJUNCT and ITEM are untranslated terms.
;; TODO: Handle the case of CONJUNCT equal to or already present in ITEM.
(defund add-conjunct-to-uterm (conjunct item)
  (declare (xargs :guard t))
  (if (or (equal conjunct *t*)
          (eq conjunct 't))
      ;; Special case (conjoining t has no effect):
      item
    (if (or (equal item *t*)
            (eq item 't))
        ;; Special case (item as just "true"):
        conjunct
      (if (and (call-of 'and item)
               (true-listp item) ;for the guard proof
               )
          ;; Special case (avoid creating a nested AND):
          `(and ,@(fargs item) ,conjunct)
        `(and ,item ,conjunct)))))

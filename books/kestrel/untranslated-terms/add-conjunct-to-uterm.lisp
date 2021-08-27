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

;; Conjoin CONJUNCT to UTERM, adding it as the last conjunct (in case its guard
;; requires UTERM to be true), unless it is already clearly present as a
;; conjunct.  CONJUNCT and UTERM are untranslated terms.
;; TODO: Consider recognizing an IF nest that represents an AND and treating it
;; like we treat a call of AND below.
(defund add-conjunct-to-uterm (conjunct uterm)
  (declare (xargs :guard t))
  (if (equal conjunct uterm)
      ;; Special case (they are the same, so just keep one):
      uterm
    (if (or (equal conjunct *t*)
            (eq conjunct 't))
        ;; Special case (conjoining t has no effect):
        uterm
      (if (or (equal uterm *t*)
              (eq uterm 't))
          ;; Special case (uterm is just "true"):
          conjunct
        (if (and (call-of 'and uterm)
                 (true-listp uterm) ;for the guard proof
                 )
            ;; uterm is already an AND:
            (let ((existing-conjuncts (fargs uterm)))
              (if (member-equal conjunct existing-conjuncts)
                  ;; Special case (conjunct already present):
                  uterm
                ;; Special case (avoid creating a nested AND):
                `(and ,@existing-conjuncts ,conjunct)))
          ;; Normal case:
          `(and ,uterm ,conjunct))))))

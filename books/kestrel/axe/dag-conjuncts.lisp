; Extracting conjuncts from a DAGs
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-to-term")
(include-book "kestrel/utilities/conjuncts-and-disjuncts2" :dir :system)

;; Extracts the conjuncts of DAG, as a list of terms.  May explode if there is
;; a lot of shared structure.
(defun dag-conjuncts (dag)
  (get-conjuncts-of-term2 (dag-to-term dag)))

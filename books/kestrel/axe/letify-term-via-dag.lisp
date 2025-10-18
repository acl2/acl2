; A tool to add lets to a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Uses DAGs under the hood, for efficiency

(include-book "dag-to-term-with-lets")
(include-book "dagify0") ;for dagify-term

;; Returns (mv erp term).
;; Only used in the equivalence-checker.
;todo: rename?
(defun letify-term-via-dag (term)
  (if (quotep term)
      (mv (erp-nil) term)
    (mv-let (erp dag)
      (dagify-term term)
      (if erp
          (mv erp nil)
        (mv (erp-nil)
            (dag-to-term-with-lets dag))))))

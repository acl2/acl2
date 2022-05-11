; Utilities for dealing with dependencies among community books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)

;; Returns (mv erp book-names state).
(defund all-books (state)
  (declare (xargs :stobjs state))
  (mv-let (erp deps-info state)
    (read-objects-from-file "../../build/Makefile-deps.lsp" state) ; todo: make portable
    (if erp
        (mv :failed-to-read-deps nil state)
      (if (not (alistp deps-info))
          (mv :bad-deps-file nil state)
        (let ((dependency-map (cdr (assoc-eq :dependency-map deps-info))))
          (if (not (alistp dependency-map))
              (mv :bad-deps-info nil state)
            (mv nil ; no error
                (strip-cars dependency-map)
                state)))))))

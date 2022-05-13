; Utilities for dealing with dependencies among community books
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)

;; Returns (mv erp deps-info state).
(defund read-deps-info (state)
  (declare (xargs :stobjs state))
  (mv-let (erp deps-info state)
    (read-object-from-file "../../build/Makefile-deps.lsp" state) ; todo: make portable
    (if erp
        (mv :failed-to-read-deps-info nil state)
      (if (not (alistp deps-info))
          (mv :bad-deps-info nil state)
        ;; (let ((dependency-map (cdr (assoc-eq :dependency-map deps-info))))
        ;;   (if (not (alistp dependency-map))
        ;;       (mv :bad-deps-info nil state)
        (mv nil           ; no error
            deps-info     ;(strip-cars dependency-map)
            state)))))

;; Example usage:
;; (mv-let (erp deps-info state) (read-deps-info state) (declare (ignore erp)) (assign deps-info deps-info))
;; (assoc-eq :CERT_PL_CERTS (@ deps-info))

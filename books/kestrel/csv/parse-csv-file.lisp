; A parser for CSV (comma-separated value) files
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-csv")
(include-book "std/util/bstar" :dir :system) ; todo: reduce
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-character-list" :dir :system)

;; Returns (mv erp parsed-value chars-from-file state).
(defund parse-file-as-csv-aux (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-file-as-csv "CSV file does not exist: ~x0." filename)
                (mv `(:file-does-not-exist ,filename) nil nil state)))
       (chars ; note that state is not returned!
        (read-file-into-character-list filename state))
       ((when (not (consp chars)))
        (prog2$ (er hard? 'parse-file-as-csv "Failed to read any character from file: ~x0." filename)
                (mv `(:failed-to-read-from-file ,filename) nil nil state)))
       ;; Parse the characters read:
       (parsed-csv ; todo: allow errors to be passed back
        (parse-csv chars))
       ;; ((when erp)
       ;;  (prog2$ (er hard? 'parse-file-as-csv "ERROR (~x0) parsing CSV in ~x1" erp filename)
       ;;          (mv `(:error-parsing-csv ,filename) nil chars state)))
       )
    (mv nil ; no error
        parsed-csv chars state)))

;; Returns (mv erp parsed-value state).
;; Example call: (parse-file-as-csv "example.csv" state)
(defund parse-file-as-csv (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv erp parsed-value & state) ; ignore the chars
        (parse-file-as-csv-aux filename state)))
    (mv erp parsed-value state)))

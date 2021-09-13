; A tool to parse a file containing a JSON object
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parse-json")
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-character-list" :dir :system)

;; Returns (mv erp parsed-value state).
;; Example call: (parse-file-as-json "example.json" state)
(defund parse-file-as-json (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-file-as-json "JSON file does not exist: ~x0." filename)
                (mv `(:file-does-not-exist ,filename) nil state)))
       (chars ; note that state is not returned!
        (read-file-into-character-list filename state))
       ((when (not (consp chars)))
        (prog2$ (er hard? 'parse-file-as-json "Failed to read any character from file: ~x0." filename)
                (mv `(:failed-to-read-from-file ,filename) nil state)))
       ;; Parse the characters read:
       ((mv erp parsed-json)
        (parse-json chars))
       ((when erp)
        (prog2$ (er hard? 'parse-file-as-json "ERROR (~x0) parsing JSON in ~x1" erp filename)
                (mv `(:error-parsing-json ,filename) nil state))))
    (mv nil ; no error
        parsed-json state)))

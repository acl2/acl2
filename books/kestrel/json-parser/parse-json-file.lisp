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

;; Returns (mv parsed-value state).
;; Example call: (parse-file-as-json "example.json" state)
(defund parse-file-as-json (filename state)
  (declare (xargs :stobjs state
                  :guard (stringp filename)))
  (b* (((mv existsp state)
        (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-file-as-json "JSON file does not exist: ~x0." filename)
                (mv t state)))
       (chars ; not that state is not returned!
        (read-file-into-character-list filename state))
       ((when (not (consp chars))) ;I've seen this be a string error message
        (prog2$ (er hard? 'parse-file-as-json "Failed to read any character from file: ~x0.  Result: ~x1" filename chars)
                (mv t state)))
       ;; Parse the characters read:
       ((mv erp parsed-json)
        (parse-json chars))
       ((when erp)
        (prog2$ (er hard? 'parse-file-as-json "ERROR (~x0) parsing JSON in ~x1" erp filename)
                (mv t state))))
    (mv parsed-json state)))

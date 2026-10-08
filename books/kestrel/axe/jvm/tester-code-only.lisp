; Using with-supporters to just get the code of the Java/JVM Formal Unit Tester
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: This needs to have all the relevant rules built in below.

(include-book "centaur/misc/tshell" :dir :system) ; needs to be non-local since it has Raw Lisp code
(include-book "tools/with-supporters" :dir :system)

(defttag :tester-jvm-code-only)

; ;(local (include-book "rule-lists-jvm")) ; defines the rule-lists mentioned below
(local (include-book "unroller-common")) ; defines unroll-java-code-rules

;; FIXME: This doesn't seem to pick up the :known-booleans-table. Try
;; (table-alist :known-booleans-table (w state)) after (include-book "tester")
;; vs after (include-book "tester-code-only"):
(make-event
  `(acl2::with-supporters
     (local (include-book "tester"))
     :tables (:known-booleans-table)
     :names (test-file
              test-file-and-exit
              ;; names mentioned in the macro test-file/test-function:
              test-file-fn make-event-quiet ; maybe-remove-temp-dir

              ;; Rules needed by the tester:
              ,@(unroll-java-code-rules))))

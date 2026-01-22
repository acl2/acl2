; Using with-supporters to just get the code of the x86 Formal Unit Tester
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; TODO: This needs to have all the relevant rules built in to it.

(include-book "centaur/misc/tshell" :dir :system) ; needs to be non-local since it has Raw Lisp code
;(include-book "kestrel/jvm/portcullis" :dir :system) ; for things like JVM::*FLOAT-NAN*
(include-book "tools/with-supporters" :dir :system)

(defttag :tester-x86-code-only)

(local (include-book "rule-lists")) ; defines the rule-lists mentioned below

(make-event
  `(acl2::with-supporters
     (local (include-book "tester"))
     :tables (:known-booleans-table)
     :names (test-file
              test-function
              ;; names mentioned in the macro test-file/test-function:
              test-file-fn test-function-fn make-event-quiet maybe-remove-temp-dir

              ;; Rules used during unrolling:
              ,@(unroller-rules32)
              ,@(unroller-rules64)
              ,@(read-and-write-rules-bv)
              ;;  ,@(read-and-write-rules-non-bv)
              ,@(assumption-simplification-rules32)
              ,@(assumption-simplification-rules64)
              ,@(step-opener-rules32)
              ,@(step-opener-rules64)
              ,@(new-normal-form-rules-common)
              ,@(canonical-rules-bv)
              ,@(new-normal-form-rules64)
              ,@(unsigned-canonical-rules)
              ,@(symbolic-execution-rules32)
              ,@(symbolic-execution-rules64)
              ;; Rules used by the tester:
              ,@(extra-tester-rules)
              ,@(extra-tester-lifting-rules)
              ,@(tester-proof-rules))))

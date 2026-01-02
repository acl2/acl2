; Using with-supporters to just get the code of the x86 Unrolling Lifter
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
(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system) ; todo: Raw Lisp code
(include-book "projects/x86isa/machine/other-non-det" :dir :system) ; todo: Raw Lisp code
(include-book "coi/lists/portcullis" :dir :system) ; for the LIST package

(include-book "tools/with-supporters" :dir :system)

(defttag :unroller-x86-code-only)

(local (include-book "rule-lists")) ; defines the rule-lists mentioned below

;; TODO: doesn't seem to handle the :known-booleans-table right
;; Try (table-alist :known-booleans-table (w state)).
(make-event
  `(acl2::with-supporters
     (local (include-book "unroller"))
     :tables (:known-booleans-table)
     :names (def-unrolled
              ;; names mentioned in the macro def-unrolled:
              def-unrolled-fn
              print-level-at-least-tp
              make-event-quiet maybe-remove-temp-dir

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
              ,@(symbolic-execution-rules64))))

; Using with-supporters to just get the code of the x86 Formal Unit Tester
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; TODO: This needs to have all the relevant rules built in to it.

(include-book "centaur/misc/tshell" :dir :system) ; needs to be non-local since it has Raw Lisp code

(include-book "tools/with-supporters" :dir :system)

(defttag :tester-x86-code-only)

(acl2::with-supporters
  (local (include-book "tester"))
  :names (test-file
          ;; names mentioned in the macro test-file:
          test-file-fn make-event-quiet maybe-remove-temp-dir
          ))

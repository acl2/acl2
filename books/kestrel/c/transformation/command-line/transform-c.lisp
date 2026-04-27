; A tool for running C transformations from the command line on JSON arguments
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book supports the shell script transform-c.sh, which the user can call
;; from the Unix command line.  That script invokes ACL2 (actually a saved ACL2
;; image with this book built-in) and calls run-json-command on the JSON file
;; supplied by the user.  See the JSON files in the tests/ directory for
;; examples.

(include-book "wrappers")
(include-book "kestrel/utilities/run-json-command" :dir :system)

; A tool for running C transformations from the command line on JSON arguments
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A tool for running C transformations from the command line, using JSON to
;; specify their arguments.

(include-book "wrappers")
(include-book "kestrel/utilities/run-json-command" :dir :system)

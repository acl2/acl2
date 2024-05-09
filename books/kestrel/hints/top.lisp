; Top book for hints/ directory
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "combine-hints")
(include-book "remove-hints")
(include-book "goal-specs")
(include-book "renaming")

;; Not including these tests in top:
;; (include-book "renaming-tests")

;; Custom hints:
(include-book "casesx")

;; Not including these tests in top:
;; (include-book "casesx-tests")

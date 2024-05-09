; A library for manipulating untranslated terms
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "helpers")

(include-book "untranslated-terms-old")

;; Helpers for let and common macros:
(include-book "let-helpers")
(include-book "mv-let-helpers")
(include-book "cond-helpers")
(include-book "case-helpers")
(include-book "case-match-helpers")
(include-book "bstar-helpers")

;; Exracting information from untranslated terms:
(include-book "free-vars")
(include-book "conjuncts-of-uterm")
(include-book "disjuncts-of-uterm")
(include-book "conjuncts-and-disjuncts")

;; Transformations on untranslated terms:
(include-book "add-conjunct-to-uterm")
(include-book "replace-calls")
(include-book "rename-functions")

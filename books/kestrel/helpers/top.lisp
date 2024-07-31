; Top book for helpers/ directory
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-packages")
(include-book "auto-return-type")
(include-book "books-in-subtree")
(include-book "helper-old")
(include-book "helper")
(include-book "deps")
(include-book "speed-up-implementation")
(include-book "speed-up")
(include-book "improve-book-implementation")
(include-book "improve-book")
(include-book "recommendations")
(include-book "model-enable")
(include-book "model-history")
(include-book "advice-implementation")
(include-book "advice")
(include-book "replay-book-helpers")
(include-book "replay-book")
(include-book "replay-book-with-advice")
(include-book "replay-books-with-advice")
(include-book "repair-book")
(include-book "eval-models")
(include-book "linter")

;; Intentionally omitting test books from this top.lisp file:
;; (include-book "replay-book-tests")

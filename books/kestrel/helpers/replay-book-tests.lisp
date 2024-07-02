; Tests of replay-book
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replay-book")

;; Replay and time the events in ../lists-light/append.lisp"
(replay-book "../lists-light" "append")

;; Make sure we can now replay a second book:
(replay-book "../lists-light" "cons")

; Tests for pack.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO Add tests of the other functions/macros in pack.lisp.

(include-book "pack")
(include-book "kestrel/apt/portcullis" :dir :system) ; a package to work with below
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal
 (pack-in-package "APT" 'foo "BAR" 3 #\c)
 'apt::|FOOBAR3c|)

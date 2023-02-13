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
 (pack-in-package "APT" 'foo "BAR" 3 #\c t nil)
 'apt::|FOOBAR3cTNIL|)

;; Test with a var passed to pack-in-package
(assert-equal
 (let ((x 'sym))
   (pack-in-package "ACL2" 'foo x "BAR" x 3 x #\c))
 '|FOOSYMBARSYM3SYMc|)

;; Test with a non-atom (a term) passed to pack-in-package
(assert-equal
 (let ((x 'XSYM))
   (pack-in-package "ACL2" 'foo (symbol-name x) "BAR"))
 'FOOXSYMBAR)

;; Test with a single item
(assert-equal
 (pack-in-package "APT" 'foo)
 'apt::FOO)

;; Test with a single item
(assert-equal
 (let ((x 'XSYM))
   (pack-in-package "ACL2" (symbol-name x)))
 'XSYM)

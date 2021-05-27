; Tests of the functions in string-utilities.lisp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains tests of the functions in string-utilities.lisp.  It is
;; separate to break the dependency of that book on the testing utilities.

(include-book "string-utilities")
(include-book "kestrel/utilities/deftest" :dir :system)

(assert-equal (substring-before-terminator "abcde" #\c) "ab")

(assert-equal (substring-after-terminator "abcde" #\c) "de")

(assert-equal (drop-string-before-char "abcde" #\c) "cde")

(assert-equal (drop-string-before-char "abcde" #\X) "")

(assert-equal (substring-before-char "abcde" #\c) "ab")

(assert-equal (substring-before-char "abcde" #\X) "abcde") ;is this what we want?

(assert-equal (substring-before-last-occurrence "ab.cd.ef.gh" #\.) "ab.cd.ef")

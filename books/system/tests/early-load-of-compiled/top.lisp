; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.txt.

(in-package "ACL2")

(include-book "defun-fast-alist")

(include-book "fast-alist-hons-copy")
(include-book "fast-alist-hons-copy-local")

(include-book "fast-alist")

(include-book "fast-alist-local")

(include-book "hons")
(include-book "hons-local")

(include-book "hons-acons-bang")
(include-book "hons-acons-bang-local")

(include-book "test1")
(include-book "test1-local")

(include-book "test2")
(include-book "test2-local")

(include-book "big-const")

(include-book "big-const-hons")
(include-book "big-def-hons")

(include-book "ttag")

; Matt K.: Formerly excluded for ACL2 built on CCL on Arm-based Macs (and other
; Arm machines), but no longer after a CCL bug fix
; (see https://github.com/Clozure/ccl/pull/630).
(include-book "eq-test")

; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book isn't normally one to include.  It simply provides a convenient way
; to include all books in this directory into ../top.lisp.

(in-package "ACL2")

; NOTE: We omit below the generated file td-cands.lisp, as well as books that
; are used only for regenerating td-cands.{lisp,acl2} and we also omit testing
; books.

(include-book "defunt")
; (include-book "defunt-tests")
; (include-book "defunt-top") ; depends on td-cands
(include-book "fms-bang-list")
(include-book "injections")
(include-book "strict-merge-sort")
(include-book "subsetp-eq-linear")
; (include-book "td-cands")
; (include-book "termination-database")
; (include-book "termination-database-utilities")

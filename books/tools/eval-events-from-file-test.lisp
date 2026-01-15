; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "eval-events-from-file")

(eval-events-from-file "eval-events-from-file-test-data.lsp")

(set-enforce-redundancy t)

(defun f1 (x)
  (cons x x))

(defconst *c*
  (expt 2 3))

(defthm f1-*c*-val
  (equal (f1 *c*) '(8 . 8)))

; number-list-theory.lisp -- the theory of lists of numbers
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(include-book "number-list-defuns")
(include-book "number-list-defthms")

(deftheory number-list-theory
  (union-theories (theory 'number-list-defuns)
		  (theory 'number-list-defthms)))

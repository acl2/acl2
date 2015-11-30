; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; For dependency scanner, we place below every include-book with :dir :system
; that is in a file toothbrush/tests/*/input.lsp.
#||
(include-book "defexec/dag-unification/dag-unification-st" :dir :system)
||#

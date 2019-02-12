; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann, December, 2014
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This little book is used by defpm.lisp.

(in-package "ACL2")

(include-book "arithmetic/top" :dir :system)

; (depends-on "build/ground-zero-theory.certdep" :dir :system)
(deftheory-static arithmetic-top-theory
  (current-theory :here))

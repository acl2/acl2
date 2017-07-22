; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This small book simply includes the final checker in our development of a
; sequence of checkers.  See README.  Note that it does not include the
; checkers that support the cube-and-conquer paradigm; see cube/README.

(in-package "ACL2") ; but checker is in the "LRAT" package

(include-book "incremental/top")

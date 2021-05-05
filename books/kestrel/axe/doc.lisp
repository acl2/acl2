; Documentation for Axe
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/topics" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(defxdoc axe
  :short "The Axe toolkit"
  :parents (software-verification kestrel-books)
  :long
  (xdoc::topparas
   "The Axe toolkit provides a variety of tools for software verification, including lifters-into-logic, rewriters, theorem provers, and equivalence checkers.

We are currently open sourcing Axe to the ACL2 Community books.

See <a href=\"https://www.kestrel.edu/research/axe/\">the Axe webpage</a> for more information."))

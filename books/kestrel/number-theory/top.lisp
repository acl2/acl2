; Top file for number theory library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "divides")
(include-book "primes")
(include-book "mod")
(include-book "mod-expt-fast")
(include-book "defprime")
(include-book "euler2-support")
(include-book "quadratic-residue")
(include-book "tonelli-shanks")
(include-book "tonelli-shanks-proof")

(defxdoc number-theory
  :parents (arithmetic kestrel-books)
  :short "Some utilities related to number theory")

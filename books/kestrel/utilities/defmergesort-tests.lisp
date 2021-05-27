; Tests for defmergesort
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmergesort")
(include-book "deftest")

(deftest
  (defmergesort merge-< merge-sort-< < real/rationalp))

(deftest
  (in-theory nil) ;make sure the proofs still work with no rules enabled
  ;; TODO: We should probably produce an applicability condition that the guard of <
  ;; is satisfied by items that satisfy real/rationalp.
  (defmergesort merge-< merge-sort-< < real/rationalp))

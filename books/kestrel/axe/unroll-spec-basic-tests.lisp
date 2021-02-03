; Tests of unroll-spec-basic
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unroll-spec-basic")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (unroll-spec-basic *test1* '(car (cons x y)) :extra-rules '(car-cons))

  ;; expected result is a dag that is a single variable:
  (must-be-redundant (defconst *test1* '((0 . x)))))

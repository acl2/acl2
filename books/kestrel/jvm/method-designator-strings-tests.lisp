; Tests of method-designator-strings
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "method-designator-strings")
(include-book "kestrel/utilities/deftest" :dir :system)

(assert-equal (extract-method-descriptor "sumsquares_iter_down.sumSquares(I)I") "(I)I")

(assert-equal (extract-method-class "foo.bar.sumsquares_iter_down.sumSquares(I)I") "foo.bar.sumsquares_iter_down")

(assert-equal (extract-method-name "foo.bar.sumsquares_iter_down.sumSquares(I)I") "sumSquares")

(assert-equal (extract-package-name "foo.bar.sumsquares_iter_down.sumSquares(I)I") "foo.bar")

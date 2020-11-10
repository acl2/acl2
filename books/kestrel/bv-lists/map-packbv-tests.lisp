; Tests of map-packbv
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "map-packbv")
(include-book "std/testing/assert-equal" :dir :system)

;; map packbv over a list of items.  Each item has 4 single bits
(assert-equal (map-packbv 4 1 '((1 1 1 1) (0 0 0 0) (0 1 0 1))) '(15 0 5))

;; map unpackbv over a list of items.  Each item will be split int 4 single bits
(assert-equal (map-unpackbv 4 1 '(15 0 5)) '((1 1 1 1) (0 0 0 0) (0 1 0 1)))

; Tests of dag-size2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/assert" :dir :system)
(include-book "kestrel/axe/dag-size-sparse" :dir :system)

(assert-equal (size-array-for-nodes '(0 1 2 3 4 5) 'dag-array (make-into-array 'dag-array '((5 foo 4 3) (4 foo 3 0) (3 foo 0 2) (2 foo 1 0) (1 quote 17) (0 . x))) 6 'size-array)
              '((5 . 13)
                (4 . 7)
                (3 . 5)
                (2 . 3)
                (1 . 1)
                (0 . 1)
                (:HEADER :DIMENSIONS (6)
                         :MAXIMUM-LENGTH 12
                         :DEFAULT NIL
                         :NAME SIZE-ARRAY)))

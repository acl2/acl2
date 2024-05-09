; Tests of the TEA spec.
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tea")
(include-book "kestrel/utilities/deftest" :dir :system)

(assert-equal (tea-encrypt '(0 0) '(0 0 0 0)) '(#x41EA3A0A #x94BAA940))

(assert-equal (tea-encrypt '(#x01234567 #x89abcdef)
                           '(#x00112233 #x44556677 #x8899aabb #xccddeeff))
              '(#x126c6b92 #xc0653a3e))

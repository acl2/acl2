; Tests of the string-trees utilities
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-trees")
(include-book "deftest")

(assert-equal (string-treep '("foo" nil ("bar" "baz" . "bat")))
              t)

(assert-equal (make-string-tree "foo" nil "bar" nil)
              '("foo" . "bar"))

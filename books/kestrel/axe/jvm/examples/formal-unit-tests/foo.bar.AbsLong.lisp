; Apply the Formal Unit Tester to AbsLong.
;
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book checks that we can handle a class in a package.

; (depends-on "foo/bar/AbsLong.class")

(include-book "kestrel/axe/jvm/tester" :dir :system)

(test-class "foo.bar.AbsLong")

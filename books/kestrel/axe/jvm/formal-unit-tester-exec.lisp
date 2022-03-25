; A book that brings in only the code (defuns, etc.) of the Formal Unit Tester
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: INCOMPLETE (also need to bring in theorems used by the tool)

(include-book "tools/with-supporters" :dir :system)

(with-supporters
 (local (include-book "formal-unit-tester" :ttags :all))
 :names (test-file-and-exit))

; Some tests of defthm
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

;; Simple test with :instructions
(defthm d1
  (equal x x)
  :rule-classes nil
  :instructions (:s))

;; Can't have both :hints and :instructions
(must-fail
 (defthm d2
   (equal x x)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable natp)))
   :instructions (:s)))

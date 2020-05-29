; A lightweight book about the function subsequencep
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subsequencep-equal")

;; The function subsequencep is built into ACL2.  It uses EQL as the
;; test.

(in-theory (disable subsequencep))

;; We turn subsequencep into subsequencep-equal and reason about that instead.
;; (It is common, when several variants of a function exist that use different
;; equality tests, to rewrite all the versions to the version that uses equal.)
(defthm subsequencep-becomes-subsequencep-equal
  (equal (subsequencep lst1 lst2)
         (subsequencep-equal lst1 lst2))
  :hints (("Goal" :in-theory (enable subsequencep subsequencep-equal))))

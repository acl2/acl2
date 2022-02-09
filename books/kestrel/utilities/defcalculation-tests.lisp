; Tests for defcalculation
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defcalculation")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  ;; Prove the usual commutativity-2 rule from comm and asssoc.
  (defcalculation comm2
    (+ x (+ y z))
    (= (+ (+ x y) z))   ;assoc
    (= (+ (+ y x) z))   ;commute
    (= (+ y (+ x z))))  ;re-assoc
  (must-be-redundant
   (defthm comm2
     (implies (and)
              (equal (+ x (+ y z))
                     (+ y (+ x z)))))))

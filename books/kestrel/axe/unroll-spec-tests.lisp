; Tests of unroll-spec
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unroll-spec")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (unroll-spec *foo* '(binary-+ (bvplus '32 '1 '2) z) :produce-theorem t)
  (must-be-redundant
   (defthm foo-unroll-spec-theorem
     (implies (and)
              (equal (binary-+ (bvplus '32 '1 '2) z)
                     (binary-+ '3 z))))))

;; Test :produce-function t
(deftest
  (unroll-spec *foo* '(binary-+ (bvplus '32 '1 '2) z) :produce-function t)
  (must-be-redundant
   (defun foo (z) (binary-+ '3 z))))

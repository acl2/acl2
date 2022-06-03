; A book about the built-in function IFF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bool-fix")

;we may often open up iff, but here are some theorems about it anyway:

(defthm iff-of-t-arg1
  (equal (iff t x)
         (bool-fix x)))

(defthm iff-of-t-arg2
  (equal (iff x t)
         (bool-fix x)))

(defthm iff-of-nil-arg1
  (equal (iff nil x)
         (not x)))

(defthm iff-of-nil-arg2
  (equal (iff x nil)
         (not x)))

(defthm iff-same
  (equal (iff x x)
         t))

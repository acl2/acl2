; Tests of operations in bv-array-conversions2.lisp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-array-conversions2")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; Example showing how we can convert a cons nest into an array by wrapping it
;; in a call to list-to-bv-array2 and the using rewriting.
(defthm test-conversion-to-array
  (equal (list-to-bv-array2 8 (cons x (cons y (cons z nil))))
         (bv-array-write 8 3 0 x
                         (bv-array-write 8 3 1 y
                                         (bv-array-write 8 3 2 z
                                                         '(0 0 0)))))
  :hints (("Goal" :in-theory (enable list-to-bv-array2 list-to-bv-array-aux2-of-cons))))

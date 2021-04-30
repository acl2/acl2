; Documentation for acl2-arrays library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/base" :dir :system)
;(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

(defxdoc acl2-arrays
  :short "A library for acl2-arrays."
  :parents (kestrel-books)
  :long "This library supports reasoning about ACL2 arrays, especially one-dimensional arrays (ones that satisfy @(tsee array1p)).  It disables all of the array-related functions (such as @(tsee aref1), @(tsee aset1), etc.) and provides rules about them.  It adds various functions about arrays, including the function @('alen1') to get the length of a one-dimensional array.  See the individual files for details."
)

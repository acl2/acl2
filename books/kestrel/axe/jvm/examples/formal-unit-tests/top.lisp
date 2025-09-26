; Top file for Axe JVM Formal Unit Tester examples
;
; Copyright (C) 2023-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We want these books to be built, but we don't actually need to include them
;; here, so we put their include-books in a multiline comment to make the
;; dependency scanner think they are actually included:

#|
(include-book "AbsLong")
(include-book "Prefix")
(include-book "BinarySearch")
(include-book "BinarySearchBuggy")
|#

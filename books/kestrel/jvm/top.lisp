; Top level book for JVM model
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The order of these roughly reflects the dependencies:
(include-book "types")
(include-book "floats")
(include-book "descriptors")
(include-book "method-descriptors")
(include-book "fields")
(include-book "instructions")
(include-book "methods")
(include-book "classes")
(include-book "ads")

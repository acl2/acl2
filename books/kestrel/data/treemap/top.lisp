; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "defs")
(include-book "map")
(include-book "to-omap")
(include-book "keys")
(include-book "in")
(include-book "size")
(include-book "lookup")
(include-book "submap")
(include-book "extensionality")
(include-book "min-max")
(include-book "update")
(include-book "delete")
(include-book "update-star")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For ordinary use of treemaps, it is recommend that you include the "defs"
;; books (or some subset of the books it includes), and then this book (or some
;; subset of its includes) *locally*.

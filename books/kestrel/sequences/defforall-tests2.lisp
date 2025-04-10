; More tests of defforall
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Test of defforall inside encapsulate (issue with the include-books it
;; introduces).
(include-book "defforall") ; todo: why is this needed?
(encapsulate ()
  (defforall all-consp (x) (consp x) :suppress-includes t))

; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "SB" = "Schroder-Bernstein"
(defpkg "SB"
  (append *std-pkg-symbols*
          '(define-sk)))

; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; "SB" = "Schroder-Bernstein"
(defpkg "SB"
  (append *std-pkg-symbols*
          '(define-sk)))

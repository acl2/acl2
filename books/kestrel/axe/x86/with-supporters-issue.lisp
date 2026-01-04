(in-package "ACL2")

;; TODO: Move this to be among the tests of with-supporters

(include-book "tools/with-supporters" :dir :system)

; Before a fix at the end of December 2025, the with-supporters call below
; caused a problem.  The problem was that the local include-book causes logapp
; to be defined when with-supporters is called, so with-supporters refrained
; from including logapp in the list of supporters it generated.  When the book
; was subsequently included, the local include-book was skipped and logapp was
; undefined.  Since December, 2025, with-supporters handles this situation.

(local (include-book "ihs/basic-definitions" :dir :system))

(with-supporters
  (local (include-book "kestrel/bv/bvcat" :dir :system)) ; logapp is a supporter
  :names (bvcat))

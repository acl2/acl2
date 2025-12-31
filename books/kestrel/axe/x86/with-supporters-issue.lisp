(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

; Before the fix at the end of December 2025, there was an error, explained as
; follows.

;; This brings in logapp, but only locally.  So the call of with-supporters
;; below thinks that logapp is already defined and does not define it.
;; If we uncomment this line, this book fails to certify:
; [It is now uncommented and the book now does certify.]
(local (include-book "ihs/basic-definitions" :dir :system))

(with-supporters
  (local (include-book "kestrel/bv/bvcat" :dir :system)) ; logapp is a supporter
  :names (bvcat))

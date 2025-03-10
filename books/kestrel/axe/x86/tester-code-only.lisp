(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)
;; defines logapp:
;; if we remove this, or make it non-local, then this whole book can be certified:
(local (include-book "ihs/basic-definitions" :dir :system))

;; (with-supporters ; fails, because it doesn't bring in logapp
;;   (local (include-book "kestrel/bv/bvcat" :dir :system)) ; logapp is a supporter
;;   :names (bvcat))

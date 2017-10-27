;; This just sets up the environment...

;(value :q)
;(setq si::*multiply-stacks* 2)

(include-book "data-structures/portcullis" :dir :system)

; Before ACL2 Version 2.5 we unioned the following additional
; symbols into the imports of the package below.

; (defconst *missing-acl2-exports*
;   '(set-verify-guards-eagerness
;     booleanp
;     acl2-numberp
;     e0-ord-<
;     defequiv
;     defcong
;     binary-+
;     fix
;     realfix
;     ifix
;     true-listp
;     zp))

(defpkg "POWERLISTS"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))

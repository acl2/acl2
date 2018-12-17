;; This just sets up the environment...

;(value :q)
;(setq si::*multiply-stacks* 2)

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

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

(in-package "ACL2")

; If this raw lisp file has already been loaded into the current environment,
; and if it is being reloaded (see acl2/acl2 issue 1507)
; and if the asdf aready-loaded-systems info has been clobbered
; (see acl2/acl2 issue 1508),
; then require-system will cause a reload.
; A reload will not work with the renamed package, so to handle this case
; we undo the rename-package first.
(let ((package (find-package :zippy)))
  (when (and package
             (string= (package-name package) "ZIPPY")
             (equal (package-nicknames package) '("ORG.SHIRAKUMO.ZIPPY")))
    (rename-package package :org.shirakumo.zippy)))

(asdf:require-system "zippy")

;; The Zippy doc suggests using ZIPPY as a package-local nickname (PLN) for ORG.SHIRAKUMO.ZIPPY.
;; However, the ACL2 package interface doesn't let you define nicknames let alone PLNs.
;; (Although they are supported by both CCL and SBCL.)
;; Also, ACL2 packages can't be renamed.
;; Therefore, in order to refer to the package ORG.SHIRAKUMO.ZIPPY in ACL2 code with a shorter name,
;; we rename the package here.
;; We could just add ZIPPY as a nickname, but printing would be a problem, then.
;; Instead we rename the primary name but keep the original name as a nickname.

(rename-package (find-package :org.shirakumo.zippy) :zippy '("ORG.SHIRAKUMO.ZIPPY"))

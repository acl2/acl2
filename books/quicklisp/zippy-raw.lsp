(in-package "ACL2")

(asdf:load-system "zippy")

;; The Zippy doc suggests using ZIPPY as a package-local nickname (PLN) for ORG.SHIRAKUMO.ZIPPY.
;; However, the ACL2 package interface doesn't let you define nicknames let alone PLNs.
;; (Although they are supported by both CCL and SBCL.)
;; Also, ACL2 packages can't be renamed.

;; Therefore, in order to refer to the package ORG.SHIRAKUMO.ZIPPY in ACL2 code with a shorter name,
;; we rename the package right away.
;; We could just add ZIPPY as a nickname, but printing would be a problem, then.
;; Instead we rename the primary name but keep the original name as a nickname.

(rename-package (find-package :org.shirakumo.zippy) :zippy '("ORG.SHIRAKUMO.ZIPPY"))

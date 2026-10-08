; This book, together with accompanying file empty-pkg-nil.acl2 to provide its
; portcullis commands -- except as otherwise noted -- was produced by Claude
; and passed along by Eric Smith.  These illustrate a soundness bug in ACL2
; Version 8.7 fixed before ACL2 Version 8.8 -- see the must-fail form in
; empty-pkg-nil.acl2, which is key.  See also community book
; system/tests/defpkg-ld-skip-proofsp.lisp.

(in-package "ACL2")

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm proof-of-nil
  nil
  :hints (("Goal" :use ((:instance symbol-package-name-of-symbol-is-not-empty-string
                                   (x (pkg-witness ""))))))
  :rule-classes nil)
)

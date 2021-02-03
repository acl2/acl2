; We avoid certifying this book in ACL2(r) because it tests output against
; rewrite-dollar-log.txt, and that output includes specific type-set values
; that differ between ACL2 and ACL2(r).  For example, 3072 is the value of
; *TS-CONS* in ACL2, but in ACL2(r) *TS-CONS* is 24576.
; cert_param: (non-acl2r)

(in-package "ACL2")
(assert-event
(identical-files-p "rewrite-dollar-log.txt" "rewrite-dollar-log.out"))

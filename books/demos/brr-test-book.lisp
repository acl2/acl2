; The output contains a type-set that's different in ACL2(r) than in ACL2:
; cert-param: non-acl2r
(in-package "ACL2")
(assert-event
(identical-files-p "brr-test-log.txt" "brr-test-log.out"))

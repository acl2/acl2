(in-package "ACL2")

(include-book "std/system/non-parallel-book" :dir :system)
(non-parallel-book)
;; cert_param: (non-acl2r)

(assert-event
(identical-files-p "geneqv-test-log.txt" "geneqv-test-log.out"))

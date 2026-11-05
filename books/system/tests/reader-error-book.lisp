; See: https://github.com/acl2/acl2/issues/2099

(in-package "ACL2")

(assert-event (after-run-script))

(assert-event
 (identical-files-p "reader-error-log.txt" "reader-error-log.out"))

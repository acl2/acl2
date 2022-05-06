; Avoid minor discrepancies in log file for ACL2(r) (might not be difficult to
; avoid with suitable output inhibiting):
; cert_param: (non-acl2r)

(in-package "ACL2")
(assert-event
(identical-files-p "ld-history-log.txt" "ld-history-log.out"))

(in-package "ACL2")
(assert-event
 (identical-files-p "vwsim-tests-log.out" "vwsim-tests-log.txt"))

; Matt K addition 2/2/2024 to avoid Allegro CL failure (I've notified the
; book's authors):

; cert_param: (non-allegro)

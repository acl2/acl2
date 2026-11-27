
(ld "cert.acl2")
(in-package "TYPE-SPEC")

(set-match-free-error t)
(set-verify-guards-eagerness 2)
(set-warnings-as-errors t '("double-rewrite" "free") state)
(reset-prehistory)

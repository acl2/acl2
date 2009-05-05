(in-package "ACL2")

(include-book "hacker" :load-compiled-file :comp)

(include-book "defstruct-parsing" :load-compiled-file :comp)
(include-book "rewrite-code" :load-compiled-file :comp)

(include-book "defcode"
              :load-compiled-file :comp
              :ttags ((defcode)))
(include-book "raw" :load-compiled-file :comp)
(include-book "redefun" :load-compiled-file :comp)
(include-book "bridge" :load-compiled-file :comp)
(include-book "subsumption" :load-compiled-file :comp)
(include-book "table-guard"
              :load-compiled-file :comp
              :ttags ((defcode) (table-guard)))

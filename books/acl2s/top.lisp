#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "acl2s/acl2s-size" :dir :system :ttags :all)
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)
(include-book "acl2s/mode-acl2s-dependencies" :dir :system :ttags :all)
(include-book "acl2s/defdata-testing" :dir :system :ttags :all)
;(include-book "projects/smtlink/top" :dir :system :ttags :all)
;(include-book "projects/smtlink/examples/basictypes" :dir :system :ttags :all)
(include-book "acl2s/sorting/sorting" :dir :system :ttags :all)
(include-book "acl2s/match" :dir :system :ttags :all)

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
;(include-book "projects/smtlink/top" :dir :system :ttags :all)
;(include-book "projects/smtlink/examples/basictypes" :dir :system :ttags :all)
(include-book "acl2s/sorting/sorting" :dir :system :ttags :all)
(include-book "acl2s/match" :dir :system :ttags :all)
(include-book "acl2s/installation" :dir :system :ttags :all)
(include-book "acl2s/extra-doc" :dir :system :ttags :all)

#|

; Hack for cert.pl ;

(include-book "acl2s/defdata-testing" :dir :system :ttags :all)
(include-book "acl2s/cgen/cgen-no-thms" :dir :system)
(include-book "acl2s/cgen/defthm-support-for-on-failure" :dir :system)
(include-book "acl2s/cgen/defthm-support-for-on-failure-local" :dir :system)

(include-book "acl2s/interface/top" :dir :system)
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(include-book "acl2s/defunc-testing" :dir :system)
(include-book "acl2s/match-testing" :dir :system)

(include-book "acl2s/distribution/acl2s-hooks/acl2s-book-support" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/acl2s" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/canonical-print" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/categorize-input" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/interaction-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/markup-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/protection-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/super-history" :dir :system)

|#

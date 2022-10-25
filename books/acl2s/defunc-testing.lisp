#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)
(include-book "acl2s/definec" :dir :system :ttags :all)

;(acl2s-defaults :set cgen-single-test-timeout 0)

(definec d-t1 (x :int) :int
  x)

(definec d-t1 (x :int) :int
  x)

(property (x :int)
  (== (d-t1 x) x))

(property d-t1-thm (x :int)
  (== (d-t1 x) x))


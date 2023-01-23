#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "acl2s/cgen/top" :dir :system :ttags :all)

(must-succeed
  (test? (implies (and (equal x y))
                  (and))))

(must-succeed
  (test? (implies (and (equal x y) (equal y x) (equal x y))
                  (and))))

(must-succeed
  (test? (implies (and (equal x y) (equal x (+ z y)))
                  (and))))

(must-succeed
  (test? (implies (and (equal x y))
                  (and (equal x y)))))

(must-succeed
  (test? (implies (and (== x y) (== y x) (== z y))
                  (== x y))))

(must-succeed
  (test? (implies (and (== x y) (== y x) (== z y))
                  (== x z))))

(must-succeed
  (test? (implies (and (== x y) (== y x) (== z y) (== a b) (== c d) (== b x) (== d y))
                  (== x a))))

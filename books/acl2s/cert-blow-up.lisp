#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(set-serialize-character-system nil state)
(set-bad-lisp-consp-memoize nil)
(set-inhibit-output-lst '(proof-tree event))
(set-write-acl2x t state)
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)
(include-book "definec" :ttags :all)
(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)

;; If you comment out the following, then the following cert command works
;; cert.pl ba11
;; But if you leave it in, then it fails.

(definec pos-ind (n :pos) :pos
  (if (= n 1)
      n
    (pos-ind (- n 1))))

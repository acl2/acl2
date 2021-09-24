#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "misc/meta-lemmas" :dir :system)

; Pete 9/14/2018: Useful for must-fail
(include-book "std/testing/eval" :dir :system)

; Pete 9/16/2018: Better range support
(include-book "tau/bounders/elementary-bounders" :dir :system)

; Pete 9/27/2018: Include utilities book
(include-book "utilities")
(include-book "definec" :ttags :all)
(include-book "cons-size")
(include-book "properties")
(include-book "check-equal")

(include-book "std/strings/top" :dir :system)
(include-book "system/doc/developers-guide" :dir :system)

(include-book "acl2s/acl2s-size" :dir :system)
(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)
(include-book "base-arithmetic" :ttags :all)
(include-book "base-lists" :ttags :all)
(include-book "acl2s/cgen/base-cgen-rules" :dir :system)
(include-book "match" :ttags :all)

(set-termination-method :ccg)

(local (set-defunc-timeout 1000))

; inhibit all ccg output.
; comment out to debug termination failures in the book.
(make-event
 (er-progn
  (set-ccg-inhibit-output-lst acl2::*ccg-valid-output-names*)
  (value '(value-triple :invisible))))


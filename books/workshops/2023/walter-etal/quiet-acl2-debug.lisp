;; Code to quiet acl2 output
;; This version isn't as aggressive as quiet-acl2, which makes it more useful for debugging

(set-ignore-ok t)
(set-debugger-enable t)
#|
(defttag redirect-set-proofs-co)
(set-raw-mode t)

;; Adapted from milawa
;; books/projects/milawa/ACL2/acl2-hacks/io.lisp

(let ((channel 'null-stream))
  (setf (get channel acl2::*open-output-channel-type-key*) :character)
  (setf (get channel acl2::*open-output-channel-key*) (make-broadcast-stream))
  (acl2::set-proofs-co 'null-stream state)
  (acl2::set-standard-co 'null-stream state))

(set-raw-mode nil)
|#
(acl2s-defaults :set verbosity-level 0)
(acl2::set-ld-post-eval-print nil state)
(acl2::set-ld-pre-eval-print nil state)

;;(acl2::set-evisc-tuple nil :iprint t :sites :all)

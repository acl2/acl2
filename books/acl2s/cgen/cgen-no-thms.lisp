#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(deflabel pre-cgen)
(set-tau-auto-mode nil)
(include-book "top")
(set-tau-auto-mode t)
(in-theory (current-theory 'pre-cgen))
; This takes too long.
; (regenerate-tau-database)


(in-package "ACL2")

(include-book "build/ifdef" :dir :system)

(ifdef-define "THMS_ONLY")

; (loads "source.lsp")
(make-event (er-let* ((forms (read-file "source.lsp" state)))
                     (value (cons 'progn forms))))


(in-package "ACL2")

(include-book "build/ifdef" :dir :system)

(ifdef-define "DEFS_ONLY")

; (loads "source.lsp")
(make-event (er-let* ((forms (read-file "source.lsp" state)))
                     (value (cons 'progn forms))))

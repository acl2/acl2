(in-package "ACL2")

(set-ld-error-action :return state)

(ld "books/fix-cert/fix-cert.lisp") ; TODO: path might change

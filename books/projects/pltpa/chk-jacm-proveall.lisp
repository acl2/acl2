(in-package "PLTP")

#||
(depends-on "jacm-proveall.lsp")
||#

(make-event
 (er-let* ((temp (proveall :jacm)))
   (value '(value-triple nil))))

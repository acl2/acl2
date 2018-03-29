(in-package "PLTP")

#||
(depends-on "standard-proveall.lsp")
||#

(make-event
 (er-let* ((temp (proveall :standard)))
   (value '(value-triple nil))))

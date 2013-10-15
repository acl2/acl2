(in-package "CUTIL")

; cert_param: (reloc_stub)
(include-book "std/util/defprojection" :dir :system)

(defmacro defprojection (&rest args)
  `(std::defprojection . ,args))

(moved)

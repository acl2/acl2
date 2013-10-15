(in-package "CUTIL")

; cert_param: (reloc_stub)
(include-book "std/util/deflist" :dir :system)

(moved)

(defmacro deflist (&rest args)
  `(std::deflist . ,args))

(in-package "CUTIL")

; cert_param: (reloc_stub)
(include-book "std/util/defaggregate" :dir :system)

(defmacro defaggregate (&rest args)
  `(std::defaggregate . ,args))

(moved)

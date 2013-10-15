(in-package "CUTIL")

; cert_param: (reloc_stub)
(include-book "std/util/defmapappend" :dir :system)

(defmacro defmapappend (&rest args)
  `(std::defmapappend . ,args))

(moved)

(in-package "CUTIL")

; cert_param: (reloc_stub)
(include-book "std/util/top" :dir :system)

(moved)


(defmacro defaggregate (&rest args)
  `(std::defaggregate . ,args))

(defmacro deflist (&rest args)
  `(std::deflist . ,args))

(defmacro defprojection (&rest args)
  `(std::defprojection . ,args))

(defmacro defmapappend (&rest args)
  `(std::defmapappend . ,args))

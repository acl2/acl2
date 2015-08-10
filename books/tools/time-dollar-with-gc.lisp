; This book provides macro time-with-gc$, which times a form and also reports
; information related to garbage collection.  Anyone should feel free to add to
; the information that this macro reports.

; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(defttag :profiling)

; example form to certify this book:

; (certify-book "time-dollar-with-gc" 0 t :ttags :all)

(progn!
 (set-raw-mode t)
 (load (concatenate 'string (cbd) "time-dollar-with-gc-raw.lsp")))

(defmacro-last time$-with-gc1)

(defmacro time$-with-gc (form)
  `(return-last 'time$-with-gc1-raw 'doesntseemtomatter ,form))

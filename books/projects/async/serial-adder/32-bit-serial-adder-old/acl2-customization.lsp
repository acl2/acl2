;; Cuong Chau <ckcuong@cs.utexas.edu>

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(ld "cert.acl2" :ld-missing-input-ok t)
(in-package "ADE")

(defmacro b16 ()
  `(set-print-base-radix 16 state))

(defmacro b10 ()
  `(set-print-base-radix 10 state))

(defmacro b2 ()
  `(set-print-base-radix 2 state))

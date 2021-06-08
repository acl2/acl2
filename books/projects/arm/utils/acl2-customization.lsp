;; Cuong Chau <ckc8687@gmail.com>

;; June 2021

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
;;(ld "cert.acl2" :ld-missing-input-ok t)
(include-book "rtl/rel11/lib/top-alt" :dir :system)

(in-package "RTL")

(defmacro b16 ()
  `(set-print-base-radix 16 state))

(defmacro b10 ()
  `(set-print-base-radix 10 state))

(defmacro b2 ()
  `(set-print-base-radix 2 state))

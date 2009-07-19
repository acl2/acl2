#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "symbol-fns-defpkg.lsp")

(in-package "SYMBOL-FNS")

(defconst symbol-fns::*symbol-fns-exports*
  `(symbol-list-to-string
    join-symbols
    make-numbered-symbol
    number-symbol-list
    enkey
    enkey-list
    ))

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "list-defpkg.lsp")

(in-package "LIST")

;; This list should be considered a rough draft.  We might want to include
;; other things, particularly:
;;
;;   - names of theorems that often should be enabled or disabled?
;;   - names of new functions as we add them?
;;   - names of variables used throughout our theorems?

(defconst *exports*
  '(finalcdr memberp firstn repeat
    cdddddr cddddddr caddddddr cadddddr caddddr
    ))

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "map-defpkg.lsp")

(in-package "MAP")

;; We intend to export only the following symbols.  Most of these are just
;; macro aliases for our functions.  See the file aliases.lisp for more
;; information about this.

(defconst *exports*
  '(;; symbols for our exportable function names and aliases
    mapp emptymap mapfix mapoptimize mapdomain mapget mapset 
    maperase mapin submap mapequiv maphead maptail mapempty
    mapempty-exec mapdefault

    ;; symbols for "common" theorems to enable/disable, use, 
    ;; or functionally instantiate
    submap-by-membership
    equal-of-gets-when-submap
    typed-mapp 
    typed-mapp-hyps 
    typed-mapp-map
    predicate-when-in-typed-mapp
    typed-mapp-by-membership
    typed-mapp-of-set 
    typed-mapp-of-erase
    equiv-implies-equal-typed-mapp-1
    ))
    


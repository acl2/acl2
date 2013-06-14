#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "bag-defpkg.lsp")

(in-package "BAG")
;BZO consider calling the pkg "BAGS"?

;rough draft of this list (should it include the theorem names too?  any missing function names?):
(defconst *exports*
  (list 'memberp
        'disjoint
        'unique
        'subbagp
        'flat
        'remove-1
        'remove-bag
        'perm
        'any-subbagp    ;do we want this one?
        'disjoint-list
        ))

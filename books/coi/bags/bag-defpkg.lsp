#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

; (ld "Makefile.acl2")

(ld "../lists/list-exports.lsp")
(ld "../util/util-exports.lsp")

;(include-book "../syntax/syn-pkg")
(ld "../syntax/syn-defpkg.lsp")

(defpkg "BAG" (append '(list::disjoint
			syn::defirrelevant
			syn::defignore 
			syn::defignored 
			mfc-clause 
			mfc-ancestors 
			let 
			term-order) 
		      *util-exports* *acl2-exports* list::*exports*))


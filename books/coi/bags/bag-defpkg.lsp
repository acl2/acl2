#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

(ld "list-exports.lsp" :dir :lists)
(ld "util-exports.lsp" :dir :util)

;(include-book "syn-pkg" :dir :syntax)
(ld "syn-defpkg.lsp" :dir :syntax)

(defpkg "BAG" (append '(list::disjoint
			syn::defirrelevant
			syn::defignore 
			syn::defignored 
			mfc-clause 
			mfc-ancestors 
			let 
			term-order) 
		      *util-exports* *acl2-exports* list::*exports*))


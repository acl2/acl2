#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

(ld "adviser-defpkg.lsp" :dir :adviser)
(ld "list-exports.lsp" :dir :lists)
(ld "alist-defpkg.lsp" :dir :alists)
(ld "syn-defpkg.lsp" :dir :syntax)
(ld "util-exports.lsp" :dir :util)

(defpkg "PATH" ;(remove-duplicates-eql ;no longer necessary
		`(,@*acl2-exports*
		  ,@*common-lisp-symbols-from-main-lisp-package*
	          ,@LIST::*exports*
	          ,@*util-exports*

		  ;; BZO make an alist exports?
		  ALIST::alistfix
                  ;;ALIST::keys
                  ALIST::vals
                  ALIST::clr-key
                  ALIST::range
                  ALIST::pre-image-aux
                  ALIST::pre-image
		  ALIST::remove-shadowed-pairs
                  firstn
		  ADVISER::defadvice

                  ;; BZO these don't belong here at all, they are just
                  ;; here to make the records/path.lisp happy.
		  tag-location
		  failed-location
                  g s wfkey wfkeys wfr g-of-s-redux s-diff-s
		  SYN::defignore
		  SYN::defignored
		  SYN::defirrelevant
                ;  )
                ))

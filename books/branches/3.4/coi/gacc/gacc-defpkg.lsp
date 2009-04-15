#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(include-book "symbols" :dir :super-ihs)
;BZO what should we do with this?
(ld "symbols.lsp" :dir :super-ihs)

;(include-book "list-exports" :dir :lists)
(ld "list-exports.lsp" :dir :lists)

;(include-book "bag-exports" :dir :bags)
(ld "bag-exports.lsp" :dir :bags)

(ld "util-exports.lsp" :dir :util)

(defpkg "GACC" 
;;  (remove-duplicates-eql   ;no longer necessary due to change in ACL2
   (union-eq 

    ;; added by eric:
    '(acl2::clr loghead logtail logapp logext signed-byte-p unsigned-byte-p the-usb the-sb)
    
    `(,@*util-exports*
      ,@BAG::*exports*
      ,@LIST::*exports*
      ,@SYMBOLS::*base-symbols* ;try without this?
      ))
   ;)
   )
  
  

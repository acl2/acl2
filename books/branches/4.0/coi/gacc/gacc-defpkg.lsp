#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

; (ld "Makefile.acl2")

;(include-book "../super-ihs/symbols")
;BZO what should we do with this?
(ld "../super-ihs/symbols.lsp")

;(include-book "../lists/list-exports")
(ld "../lists/list-exports.lsp")

;(include-book "../bags/bag-exports")
(ld "../bags/bag-exports.lsp")

(ld "../util/util-exports.lsp")

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
  
  

;; Sat Aug  7 15:33:14 2004
;; After jvm-loader is properly guard verified. 
;; this file is not necesary. But it occurs in Makefile. Keep it. 
;; empty file. 


(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-linker")


;------ method Resolution ------

;; (acl2::set-verify-guards-eagerness 0)
;; ; Fri Apr  2 00:51:12 2004 stop here. 
;; ;
;; ; primitives for how to get a method-ptr
;; ; used in invokevirtual <methodCP>

;; ; (skip-proofs (verify-guards WFF-FIELDCP))
;; ; (skip-proofs (verify-guards WFF-FIELD-PTR))
;; ; (skip-proofs (verify-guards FIELD-PTR-CLASSNAME))
;; ; (skip-proofs (verify-guards DEREF-STATIC-FIELD-GUARD))


;; ;(skip-proofs (verify-guards methodCP-classname ))
;; ;(skip-proofs (verify-guards methodCP-methodname ))
;; ;(skip-proofs (verify-guards methodCP-args-type ))
;; (skip-proofs (verify-guards methodCP-returntype ))
;; (skip-proofs (verify-guards methodCP-to-method-ptr ))
;; (skip-proofs (verify-guards wff-method-decls ))
;; (skip-proofs (verify-guards searchMethod ))
;; (skip-proofs (verify-guards deref-method ))
;; (skip-proofs (verify-guards lookupMethod-measure ))
;; (skip-proofs (verify-guards lookupMethod-inv ))
;; (skip-proofs (verify-guards lookupMethod ))
;; (skip-proofs (verify-guards hasAccessToMethod ))
;; (skip-proofs (verify-guards resolveMethodReference ))
;; (skip-proofs (verify-guards getSpecialMethod1 ))
;; (skip-proofs (verify-guards getSpecialMethod ))
;; (skip-proofs (verify-guards static-field-size ))
;; (skip-proofs (verify-guards fieldCP-classname ))
;; (skip-proofs (verify-guards fieldCP-fieldname ))
;; (skip-proofs (verify-guards fieldCP-fieldtype ))
;; (skip-proofs (verify-guards make-field-ptr ))
;; (skip-proofs (verify-guards field-ptr-classname ))
;; (skip-proofs (verify-guards field-ptr-fieldname ))
;; (skip-proofs (verify-guards field-ptr-type ))
;; (skip-proofs (verify-guards fieldCP-to-field-ptr ))
;; (skip-proofs (verify-guards searchStaticFields ))
;; (skip-proofs (verify-guards deref-static-field ))
;; (skip-proofs (verify-guards lookupStaticField-measure ))
;; (skip-proofs (verify-guards lookupStaticField-inv ))
;; (skip-proofs (verify-guards lookupStaticField ))
;; (skip-proofs (verify-guards hasAccessToField ))
;; (skip-proofs (verify-guards resolveStaticFieldReference ))
;; (skip-proofs (verify-guards static-field-class-rep ))
;; (skip-proofs (verify-guards searchFields ))
;; (skip-proofs (verify-guards deref-field ))
;; (skip-proofs (verify-guards lookupField-measure ))
;; (skip-proofs (verify-guards lookupField-inv ))
;; (skip-proofs (verify-guards lookupField ))
;; (skip-proofs (verify-guards resolveFieldReference ))
;; (skip-proofs (verify-guards make-callback-func-ptr ))
;; (skip-proofs (verify-guards callback-funcname ))
;; (skip-proofs (verify-guards callback-func-ptr? ))
;; (skip-proofs (verify-guards clinitMethod-ptr ))
;; (skip-proofs (verify-guards initMethod-ptr ))
;; (skip-proofs (verify-guards RunCustomCode-method-ptr ))












(acl2::in-package "ACL2")

(ld "data-structures/define-u-package.lsp" :dir :system)
(ld "coi/symbol-fns/symbol-fns-defpkg.lsp" :dir :system)

(defpkg "DEFDATA"
  (append 
   '(value legal-constantp er-let* b* legal-variablep
     macroexpand1 trans-eval simple-translate-and-eval
      f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d unsigned-byte-p
     fquotep ffn-symb flambdap fargs
     dumb-negate-lit template-subst

     ;more acl2 exports
     aconsp
     
     mget mset wf-keyp good-map
     => ;sig
     _ ;range
     defdata-subtype defdata-disjoint defdata defdata-attach ;long names -- just put them as ACL2 symbols.

     ;community books
     u::defloop def-ruleset
     )
   
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

#!DEFDATA
(defconst *defdata-exports* 
  '(is-subtype 
    is-disjoint 
    
    
    ;; misc exports: (n-x and finxlst-x added by harshrc)
    oneof anyof
    split switch
    
    listof alistof enum range record map
    _ ;for range
 
    ;; function/macro exports:
    register-data-constructor 
    register-combinator
    register-type
    defdata-subtype defdata-disjoint defdata defdata-attach
    sig =>
    
    defdata-defaults-table
    ))


(defpkg "CGEN"
  (union-eq
   '(value legal-constantp er-let* b* 
     macroexpand1 trans-eval simple-translate-and-eval
     assert-event legal-variable-or-constant-namep
     f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d 
     unsigned-byte-p
     defrec 
     variablep fquotep ffn-symb flambdap fargs
     dumb-negate-lit 

     test? ;for acl2s-hooks query categorization
     
     acl2s-defaults acl2s-defaults-table
     
     
     ; from community books
     u::defloop template-subst
     mget mset

;; ;verbosity control 
;;      system-debug-flag inhibit-output-flag normal-output-flag
;;      verbose-flag verbose-stats-flag debug-flag

     )
   (union-eq
    defdata::*defdata-exports*
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*))))


#!CGEN
(defconst *cgen-exports*
  '(cgen
     ;API export
     test? prove/cgen
     stopping-condition
     ))

(defconst *ccg-exports*
  '(set-termination-method 
    get-termination-method
    set-ccg-time-limit get-ccg-time-limit
    set-ccg-print-proofs get-ccg-print-proofs
    set-ccg-inhibit-output-lst get-ccg-inhibit-output-lst
    set-ccg-hierarchy))


(defpkg "ACL2S"
  (union-eq
   '(defxdoc e/d er-let* b* value
      aconsp 
      mget mset wf-keyp good-map
      

      => ;sig
      _  ;range

      test? ;for acl2s-hooks query categorization
      acl2s-defaults acl2s-defaults-table
    
      begin-book
      rev ;why do we need to add this??

;community books
      u::defloop def-ruleset
      must-fail ;from misc/eval


      )
   (union-eq
    (union-eq 
     *ccg-exports*
     ;;*ccg-valid-output-names*
     '(query basics performance build/refine size-change counter-example))
    (union-eq
     defdata::*defdata-exports*
     (union-eq
      cgen::*cgen-exports*
      (union-eq *acl2-exports*
                *common-lisp-symbols-from-main-lisp-package*))))))

#!ACL2S
(defconst *acl2s-exports*
  (union-eq
   defdata::*defdata-exports*
   (union-eq
    cgen::*cgen-exports*
    '(acl2s-defaults
      acl2s-defaults-table
     
     ;defunc defaults
      defunc
      set-defunc-termination-strictp set-defunc-function-contract-strictp set-defunc-body-contracts-strictp set-defunc-timeout
      get-defunc-timeout get-defunc-termination-strictp get-defunc-function-contract-strictp get-defunc-body-contracts-strictp
       ))))

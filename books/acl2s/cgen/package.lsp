
(defpkg "CGEN"
  (append 
   '(value legal-constantp er-let* b* 
     macroexpand1 trans-eval simple-translate-and-eval
     assert-event legal-variable-or-constant-namep
     f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d 
     unsigned-byte-p
     defrec 
     variablep fquotep ffn-symb flambdap fargs
     dumb-negate-lit template-subst
     

     ;;added by harshrc
      mget mset
     
     ;API export
     test? prove/cgen acl2s-defaults 
   
     ;acl2s-defaults parameters
     num-trials verbosity-level 
     num-witnesses num-counterexamples
     sampling-method search-strategy
     backtrack-limit  
     cgen-timeout 
     stopping-condition testing-enabled 
     print-cgen-summary

     ;verbosity control 
     system-debug-flag inhibit-output-flag normal-output-flag
     verbose-flag verbose-stats-flag debug-flag

     ;data-structures/utilities
     u::defloop

     )
   
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))#|ACL2s-ToDo-Line|#



(defpkg "DEFDATA"
  (append 
   '(getprop key val formals macro-args const
     decode-logical-name value legal-constantp er-let* b* 
     macroexpand1 trans-eval simple-translate-and-eval
     assert-event legal-variable-or-constant-namep
     f-boundp-global f-get-global f-put-global
     proof-checker expansion equivalence-relationp
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d unsigned-byte-p
     defrec 
     variablep fquotep ffn-symb flambdap fargs
     lambda-body lambda-formals subcor-var
     dumb-negate-lit
     
     ;from graph.lisp
     is-subtype is-disjoint 
     
     ;utlities.lisp
     nat-listp allp acl2-number-listp naturals-listp pos-listp
     
     ;; num-lists.lisp
     ;acl2-number-listp naturals-listp pos-listp 2+-listp
     ;sum-list product-list max-nat-list <=-lists all-<=
     ;shift scale *-lists +-lists make-list-logic pow list-expt
     ;pfix pos-list-fix
     
     ;; misc exports: (n-x and finxlst-x added by harshrc)
     oneof anyof data-constructors 
     x n v infxlst finxlst _

     ;;added by harshrc
      listof enum range record map set nfixg
      set-acl2s-defdata-verbose
      get-acl2s-defdata-verbose
      mget mset c
     
     ;; function/macro exports:
     register-data-constructor
     define-enumeration-type
     defdata-subtype defdata-disjoint 
     register-custom-type register-type
     defdata defdata-attach
     
     ;acl2-check
     test? top-level-test? acl2s-defaults
     set-acl2s-random-testing-enabled
     get-acl2s-random-testing-enabled
     dont-print-thanks-message-override-hint
   
     ;acl2s-defaults parameters
     num-trials verbosity-level show-testing-output 
     num-witnesses num-counterexamples

     show-top-level-counterexample sampling-method
     backtrack-limit  subgoal-timeout search-strategy
     stopping-condition testing-enabled

     ;verbosity control 
     system-debug-flag inhibit-output-flag normal-output-flag
     verbose-flag debug-flag

     )
   
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))#|ACL2s-ToDo-Line|#


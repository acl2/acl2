
(defpkg "DEFDATA"
  (append 
   '(value legal-constantp er-let* b* 
     macroexpand1 trans-eval simple-translate-and-eval
      f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d unsigned-byte-p
     fquotep ffn-symb flambdap fargs
     dumb-negate-lit template-subst
     
     ;from graph.lisp
     is-subtype is-disjoint 
     
     
     ;; misc exports: (n-x and finxlst-x added by harshrc)
     oneof anyof
     x n i v  _
     split switch

     ;;added by harshrc
      listof alistof enum range record map set
      mget mset
     
     ;; function/macro exports:
     register-data-constructor register-combinator
     defdata-subtype defdata-disjoint 
     register-type
     defdata defdata-attach
     
     ;table
     defdata-defaults-table

     ;community books
     u::defloop def-ruleset

     ;polymorphic sig
     sig

     )
   
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))#|ACL2s-ToDo-Line|#


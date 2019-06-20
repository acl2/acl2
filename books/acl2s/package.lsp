(acl2::in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(include-book "data-structures/portcullis" :dir :system)
(include-book "coi/symbol-fns/portcullis" :dir :system)

(defpkg "DEFDATA"
  (append 
   '(value legal-constantp er-let* b* legal-variablep
     macroexpand1 trans-eval simple-translate-and-eval
      f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d unsigned-byte-p
     fquotep ffn-symb flambdap fargs
     template-subst

     error warning warning! observation prove
     proof-builder event history summary proof-tree

     ;more acl2 exports
     aconsp
     
     mget mset wf-keyp good-map
     => ;sig
     _ ;range

     defdata-subtype defdata-disjoint
     defdatas-subtype defdatas-disjoint

     defdata-subtype-strict defdata-disjoint-strict
     defdatas-subtype-strict defdatas-disjoint-strict

     defdata-alias
     defdata defdata-attach ;long names -- just put them as ACL2 symbols.

     stage
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

    defdata-subtype defdata-disjoint
    defdatas-subtype defdatas-disjoint

    defdata-subtype-strict defdata-disjoint-strict
    defdatas-subtype-strict defdatas-disjoint-strict

    defdata
    defdata-attach
    sig =>
    
    defdata-alias
    stage
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

     error warning warning! observation prove
     proof-builder event history summary proof-tree

     test? ;for acl2s-hooks query categorization
     
     acl2s-defaults acl2s-defaults-table
     
     
     ; from community books
     u::defloop template-subst
     mget mset

     stage

;; ;verbosity control 
;;      system-debug-flag inhibit-output-flag normal-output-flag
;;      verbose-flag verbose-stats-flag debug-flag

     )
   (union-eq
    defdata::*defdata-exports*
    (union-eq (set-difference-eq
               *acl2-exports*
; Matt K. mod 12/20/2015: Avoid name conflict with macros defined in
; cgen/utilities.lisp.
               '(acl2::access acl2::change))
              *common-lisp-symbols-from-main-lisp-package*))))


#!CGEN
(defconst *cgen-exports*
  '(cgen
     ;API export
     test? prove/cgen
     stopping-condition
     define-rule
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
      must-succeed
      must-prove
      must-not-prove
      symbol-package-name-safe

      error warning warning! observation prove
      proof-builder event history summary proof-tree
      stage
      
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

      stage
      
     ;defunc defaults
      defunc
      definec
      defintrange
      defnatrange
      set-defunc-termination-strictp set-defunc-function-contract-strictp set-defunc-body-contracts-strictp set-defunc-timeout
      get-defunc-timeout get-defunc-termination-strictp get-defunc-function-contract-strictp get-defunc-body-contracts-strictp
       ))))


(defpkg "ACL2S B" ; beginner
  (union-eq '(t nil 
              ;if ; see macro below
              equal

              ; + * unary-- unary-/ < ; see definitions below
              numerator denominator
              rationalp integerp

              consp cons ; car cdr

              cond ; macro: explain
              list ; macro: explain

              lambda
              let let* ; macro: explain

              quote

              symbolp symbol-name symbol-package-name
              ;stringp
              ;charp

              acl2s::check=

              and or iff implies not booleanp 
              ;+ * 
              / posp negp natp <= > >= zp - atom 
              ; true-listp 
              endp 
              ;caar cadr cdar cddr 
              ;caaar caadr cadar caddr cdaar cdadr cddar cdddr
              ;caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
              ;cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr
              
              must-fail ;from misc/eval
              must-succeed
              must-prove
              must-not-prove
              symbol-package-name-safe

              stage
              
              trace* trace$

              defthm thm defconst in-package defun table


              error warning warning! observation prove
              proof-builder event history summary proof-tree
              )
            (union-eq
             #!ACL2S
             '(nat string pos rational integer boolean all neg
                   acl2-number true-list char symbol)
             acl2s::*acl2s-exports*)
             ))


(defpkg "ACL2S BB" ; bare bones
  (union-eq '(t nil 
              ;if ; see macro below
              equal

              defun acl2s::defunc acl2s::definec;for function definitions
              acl2s::defintrange acl2s::defnatrange
              
              ; + * unary-- unary-/ < ;see definitions below
              numerator denominator
              rationalp integerp
              
              consp cons  

              cond ; macro: explain
              list ; harshrc [21st Aug 2012] commented out to allow (defdata list ...) below

              lambda
              let let* ; macro: explain

              quote

              symbolp symbol-name symbol-package-name
              ;stringp
              ;charp

              error warning warning! observation prove
              proof-builder event history summary proof-tree

              acl2s::check=
              
              stage
              trace*
              )
            '()))


(defpkg "ACL2S T" ; Theorem Proving Beginner 
  (union-eq '(t nil 
              ;if ; see macro below
              equal

              
              ; + * unary-- unary-/ < ; see definitions below
              numerator denominator
              rationalp integerp

              cons car cdr consp 
              ;first  rest
              ;second third fourth fifth

              cond ; macro: explain
              list ; macro: explain

              lambda
              let let* ; macro: explain

              quote

              symbolp symbol-name symbol-package-name
              stringp
              charp

              error warning warning! observation prove
              proof-builder event history summary proof-tree

              acl2s::check=

              and or iff implies not booleanp 
              ; + * 
              / posp natp <= > >= zp - atom 
              true-listp endp 
              caar cadr cdar cddr 
              caaar caadr cadar caddr cdaar cdadr cddar cdddr
              caaaar caaadr caadar caaddr cadaar cadadr caddar cadddr
              cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr
              
              stage
              trace* trace$

              defthm thm defconst in-package defun table
              
              )
            (union-eq
             #!ACL2S
             '(nat string pos rational integer boolean all neg
                   acl2-number true-list char symbol)
             acl2s::*acl2s-exports*)
            ))

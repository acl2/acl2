(acl2::in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(include-book "data-structures/portcullis" :dir :system)
(include-book "coi/symbol-fns/portcullis" :dir :system)

; Put any symbols we want exported to other packages here. This allows
; us to export symbols in the ACL2S package, such as functions defined
; in utilities.lisp to DEFDATA, CGEN, etc.
(defpkg "ACL2S-SHARED"
  (append
   '(pkgp
     fix-sym
     gen-sym-pkg
     eqlable-2-alistp
     make-symbl
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

#!ACL2S-SHARED
(defconst *acl2s-shared-exports* 
  (append
   '(pkgp
     fix-sym
     gen-sym-pkg
     eqlable-2-alistp
     make-symbl
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))

(defpkg "DEFDATA"
  (append 
   '(value legal-constantp er-let* b* legal-variablep
     legal-variable-or-constant-namep
     macroexpand1 trans-eval simple-translate-and-eval
     f-boundp-global f-get-global f-put-global
     |1+F| |1-F| +f -f
     defxdoc current-acl2-world e/d unsigned-byte-p
     fquotep ffn-symb flambdap fargs
     template-subst
     with-time-limit

     error warning warning! observation prove
     proof-builder event history summary proof-tree
     form

     ;more acl2 exports
     aconsp
     
     mget mset wf-keyp good-map
     => ;sig
     _ ;range


     fix-pkg
     fix-sym
     fix-intern$
     fix-intern-in-pkg-of-sym
     pack-to-string
     gen-sym-sym-fn
     gen-sym-sym
     packn1
     
     defdata-subtype defdata-disjoint defdata-equal
     defdatas-subtype defdatas-disjoint defdatas-equal

     defdata-subtype-strict defdata-disjoint-strict defdata-equal-strict
     defdatas-subtype-strict defdatas-disjoint-strict defdatas-equal-strict

     defdata-alias
     defdata defdata-attach ;long names -- just put them as ACL2 symbols.

     stage
     ;community books
     u::defloop def-ruleset
     )
   
   acl2s-shared::*acl2s-shared-exports*))

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

    defdata-subtype defdata-disjoint defdata-equal
    defdatas-subtype defdatas-disjoint defdatas-equal

    defdata-subtype-strict defdata-disjoint-strict defdata-equal-strict
    defdatas-subtype-strict defdatas-disjoint-strict defdatas-equal-strict
    
    defdata
    defdata-attach
    sig =>
    
    defdata-alias
    stage
    defdata-defaults-table
    ))


(defpkg "CGEN"
  (union-eq
   '(value legal-constantp legal-variablep er-let* b* 
     legal-variable-or-constant-namep
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
     form

     test? ;for acl2s-hooks query categorization
     
     acl2s-defaults acl2s-defaults-table
     with-time-limit     
     
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
    (set-difference-eq
     acl2s-shared::*acl2s-shared-exports*
; Matt K. mod 12/20/2015: Avoid name conflict with macros defined in
; cgen/utilities.lisp.
     '(acl2::access acl2::change)))))

#!CGEN
(defconst *cgen-exports*
  '(;cgen
     ;API export
     test? prove/cgen
     stopping-condition
     define-rule
     set-cgen-guard-checking
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
      legal-variable-or-constant-namep
      legal-constantp
      legal-variablep
      legal-variable-or-constant-namep
      xdoc
      get-tau-runes
      arglist
      bash
      simp
      bash-term-to-dnf
      ?
      simp-pairs
      term
      dumb-negate-lit
      dumb-negate-lit-lst
      untranslate-lst
      all-vars-in-untranslated-term
      *nil*
      *t*
      variablep
      fn-symb
      fcons-term*
      fquotep
      ffn-symb
      fargn
      fcons-term*
      lambda$
      apply$
      collect$
      hints
      lemmas
      flatten
      impliez
      v
      
      => ;sig
      _  ;range

      d<
      l<
      <<
      lexp

      enable*
      disable*
      e/d*
      add-to-ruleset
      def-ruleset 
      def-ruleset!
      expand-ruleset
      get-ruleset
      ruleset
    
      test? ;for acl2s-hooks query categorization
      acl2s-defaults acl2s-defaults-table

      def-pattern-match-constructor
      pattern-match
      
      clear-memo-table

      induction-machine
      
      begin-book
      rev ;why do we need to add this??
      with-time-limit
      
;community books
      u::defloop def-ruleset
      must-fail ;from std/testing/eval
      must-succeed
      must-prove
      must-not-prove
      symbol-package-name-safe

      cons-size
      acl2s-size
      
      error warning warning! observation prove
      proof-builder event history summary proof-tree
      stage
      form
      formals

      defdata::get1
      defdata::cw?
      defdata::extract-keywords
      defdata::type-metadata-table 
      defdata::type-alias-table 
      defdata::pred-alias-table 
      defdata::deffilter
      defdata::remove1-assoc-eq-lst
      defdata::sym-aalistp
      defdata::sym-aalist
      
      read-run-time
      trans-eval
      cgen
      tests-and-calls

      fix-pkg
      fix-sym
      fix-intern$
      fix-intern-in-pkg-of-sym
      pack-to-string
      gen-sym-sym-fn
      gen-sym-sym
      packn1
      
      flg
      sort
      guard-checking-on
      current-flg
      raw-mode-p
      )
   (union-eq
    (union-eq 
     *ccg-exports*
     ;;*ccg-valid-output-names*
     '(query basics performance build/refine size-change
      counter-example ccg ccg-xargs 
      *ccg-valid-output-names*))
    (union-eq
     defdata::*defdata-exports*
     (union-eq
      cgen::*cgen-exports*
      acl2s-shared::*acl2s-shared-exports*)))))

#!ACL2S
(defconst *acl2s-exports*
  (union-eq
   defdata::*defdata-exports*
   (union-eq
    cgen::*cgen-exports*
    (union-eq
     acl2s-shared::*acl2s-shared-exports*
     '(acl2s-defaults
       acl2s-defaults-table
       ccg
       cgen
       stage
      
;defunc defaults
       defunc
       definec
       defintrange
       defnatrange
       set-defunc-termination-strictp set-defunc-function-contract-strictp set-defunc-body-contracts-strictp set-defunc-timeout
       get-defunc-timeout get-defunc-termination-strictp get-defunc-function-contract-strictp get-defunc-body-contracts-strictp
       )))))


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
              
              must-fail ;from std/testing/eval
              must-succeed
              must-prove
              must-not-prove
              symbol-package-name-safe
              with-time-limit
              
              stage
              form
     
              trace* trace$

              defthm thm defconst in-package defun table

              declare
              xargs
              acl2s::allp
              error warning warning! observation prove
              proof-builder event history summary proof-tree
              )
            (set-difference-eq
             (union-eq
              #!ACL2S
              '(nat string pos rational integer boolean all neg
                    acl2-number true-list char symbol)
              acl2s::*acl2s-exports*)
             #!ACL2'(if first rest second third fourth unary-- unary-/
              < + * len append app rev in remove-dups nth nthrest listp)
             )))


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
              
              with-time-limit
              stage
              form
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
              form
              trace* trace$
              with-time-limit

              defthm thm defconst in-package defun table
              
              )
            (set-difference-eq
             (union-eq
              #!ACL2S
              '(nat string pos rational integer boolean all neg
                    acl2-number true-list char symbol)
              acl2s::*acl2s-exports*)
             #!ACL2'(if first rest second third fourth fifth unary-- unary-/
              < + * len append app rev in remove-dups nth nthcdr
              string-len)
             )))

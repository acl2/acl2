#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
core defdata language
author: harshrc
file name: defdata-core.lisp
date created: [2014-04-20 Sun]
data last modified: [2014-07-2]
|#

(in-package "DEFDATA")

; There are some design notes and other pieces of documentation at the
; end of this file.



; We are going to reuse code/design from Sol Sword's FTY and Bishop Brock's
; defstructure. Sol Sword's FTY in turn builds on Jared Davis's std/util books.

(include-book "data-structures/utilities" :dir :system)
(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "defdata-util")
(include-book "builtin-combinators") ;defines defdata-defaults table and the behavior of builtin combinators



(program) ; we are not going to prove anything about these functions
(set-state-ok t)

;; (defun filter-fn (lst fn rest wrld)
;;   (if (endp lst)
;;       '()
;;     (b* (((mv erp ans) (acl2::ev-fncall-w fn (cons (car lst) rest) wrld nil nil t nil nil)))
;;     (if (and (not erp) ans)
;;         (cons (car lst)
;;               (filter-fn (cdr lst) fn rest wrld))
;;       (filter-fn (cdr lst) fn rest wrld)))))

;; (defmacro filter (lst fn w &rest rest-args)
;;   `(filter-fn ,lst ,fn ,rest-args ,w))




;; Generate predicate defun bodies

(defun apply-mget-to-var-lst (fields xvar)
  (if (endp fields)
    nil
    (let ((d-keyword-name (intern (symbol-name (car fields)) "KEYWORD")))
      (cons (list 'acl2::mget d-keyword-name xvar)
            (apply-mget-to-var-lst (cdr fields) xvar)))))

(defmacro acl2::tag= (x tag)
  `(and (consp ,x)
        (equal (acl2::mget :0tag ,x) ,tag)))
  



; for readability of functions with long parameter list
(defmacro make-pred-I... (s x)
  `(make-pred-I ,s ,x kwd-alist M C B wrld))
(defmacro make-pred-Is... (ss xs)
  `(make-pred-Is ,ss ,xs kwd-alist M C B wrld))


(mutual-recursion
(defun make-pred-I (s x   kwd-alist M C B wrld)
  "predicate interpretation for core defdata exp s.
x is the name of the expr that currently names the argument under question/predication
kwd-alist gives some defaults.
M is type metadata table + some basic info for the clique of types being defined.
C is the constructor table + some basic info for new constructors.
B is the builtin combinator table."
  (cond ((possible-constant-value-p s) `(EQUAL ,x ,s))

        ((proper-symbolp s) (if (assoc-eq s M) ;this is fine, since names and typenames are disjoint
                                `(,(predicate-name s M) ,x)
                              `(EQUAL ,x ,s)))

        ((not (true-listp s)) (make-pred-I... (cdr s) x)) ;name decl

        ((assoc-eq (car s) B) ;builtin combinator
         (b* ((pred-I-fn (get2 (car s) :pred-I B)))
           (if pred-I-fn
               ;special cases like range, member
               (funcall-w pred-I-fn (list x s) 'make-pred-I wrld)
             `(,(car s) . ,(make-pred-Is... (cdr s) (make-list (len (cdr s)) :initial-element x))))))

        ((assoc-eq (car s) C) ;constructor
         (b* ((conx (car s))
              ((mv recog dest-pred-alist) (mv (get2 conx :recog C) (get2 conx :dest-pred-alist C)))
              (dest-calls (list-up-lists (strip-cars dest-pred-alist) (make-list (len (cdr s)) :initial-element x)))
              (field-pred-alist (get2 conx :field-pred-alist C)) ;non-empty only for new-constructor (record)
              (mget-dex-calls (and field-pred-alist (apply-mget-to-var-lst (strip-cars field-pred-alist) x)))
              (dest-calls (or (and (get1 :recp kwd-alist) mget-dex-calls) dest-calls)) ;recursive new-constructors take precedence!
              (binding (bind-names-vals (cdr s) dest-calls))
              (satisfies-exprs (get-all :satisfies kwd-alist))
              (call-exprs (replace-calls-with-names dest-calls (cdr s)))
              (rst (append (make-pred-Is... (cdr s) call-exprs)
                           satisfies-exprs))
              (recog-calls (list (list recog x))))
           `(AND ,@recog-calls
                 (LET ,binding
                      (AND . ,rst)))))
                                  
        (t
;TODO: maybe dependent expr...
         `(,(car s) . ,(make-pred-Is... (cdr s) (make-list (len (cdr s)) :initial-element x))))))
         
(defun make-pred-Is (texps xs   kwd-alist M C B wrld)
  (if (endp texps)
      '()
    (cons (make-pred-I... (car texps) (car xs))
          (make-pred-Is... (cdr texps) (cdr xs)))))
)
         
  

(defun make-pred-declare-forms (xvar kwd-alist)
  (b* ((guard-lambda (get1 :pred-guard kwd-alist)) ;its a lambda
       (actuals (list xvar)))
    (if guard-lambda
        `((DECLARE (XARGS :GUARD ,(expand-lambda (cons guard-lambda actuals)))))
      '())))



(defloop funcalls-append (fs args wrld)
  (for ((f in fs)) (append (funcall-w f args 'defdata-events wrld))))


;Generate predicate events

(defun pred-event (p top-kwd-alist wrld)
  "make a predicate defun event."
  (b* (((cons name A) p)
       (curr-pkg (get1 :current-package top-kwd-alist))
       (pred-name (make-predicate-symbol name curr-pkg))
       ((when (allows-arity pred-name 1 wrld)) nil) ;already defined
       
       ((acl2::assocs ndef ?N new-constructors new-types kwd-alist) A)
       (recp (get1 :recp kwd-alist))
       ;non-recursive record predicate is defined elsewhere
       ((when (and new-constructors (not recp))) nil)
       
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (C (append new-constructors (table-alist 'data-constructor-table wrld)))
       (B (table-alist 'builtin-combinator-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))

       (avoid-lst (append (forbidden-names) (strip-cars N)))
       (xvar (if (member-eq 'v avoid-lst) 'v (acl2::generate-variable 'v avoid-lst nil nil wrld)))
       (pred-body (make-pred-I ndef xvar kwd-alist M C B wrld))
       (pred-decls (make-pred-declare-forms xvar kwd-alist))
       (pred-name (predicate-name name M))
       (def (if (and (not recp) (get1 :disable-non-recursive-p kwd-alist))
                'defund 
              'defun))
       )
    
    `((,def ,pred-name (,xvar) ,@pred-decls ,pred-body))))


(defloop pred-events (ps kwd-alist wrld)
  (for ((p in ps)) (append (pred-event p kwd-alist wrld))))

(defun already-defined-pred-defthm-event (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       (curr-pkg (get1 :current-package top-kwd-alist))
       (pred-name (make-predicate-symbol name curr-pkg))
       ((unless (allows-arity pred-name 1 wrld)) nil)
       ((acl2::assocs ndef ?N new-types kwd-alist) A)
       (C (table-alist 'data-constructor-table wrld))
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (B (table-alist 'builtin-combinator-table wrld))
       (kwd-alist (append kwd-alist top-kwd-alist))
       (avoid-lst (append (forbidden-names) (strip-cars N)))
       (xvar (if (member-eq 'v avoid-lst) 'v (acl2::generate-variable 'v avoid-lst nil nil wrld)))
       (pred-body (make-pred-I ndef xvar kwd-alist M C B wrld)))
    `((defthm ,(s+ name "P-TESTTHM")
        (equal (,pred-name ,xvar)
               ,pred-body)
        :rule-classes nil
        :hints ,(get1 :hints kwd-alist)))))

(defloop already-defined-pred-defthm-events (ps kwd-alist wrld)
  (for ((p in ps)) (append (already-defined-pred-defthm-event p kwd-alist wrld))))

(defun predicate-events1 (D kwd-alist wrld)
  (b* ((already-defined-pred-defthm-events (already-defined-pred-defthm-events D kwd-alist wrld))
       (pred-events (append (pred-events D kwd-alist wrld)
                            ;;clique
                            (funcalls-append (get1 :in-pred-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)))
       )
    
    (if (and (consp pred-events) (consp (cdr pred-events))) ;len = 2
        `((mutual-recursion ,@pred-events))
      (append already-defined-pred-defthm-events pred-events))))


(defun collect-keyword-ev (p key)
  (b* (((cons & A) p)
       ((acl2::assocs kwd-alist) A)
       (all-ev (get1 key kwd-alist)))
    all-ev))
   
(defloop collect-events1 (ps key)
  (for ((p in ps)) (append (collect-keyword-ev p key))))

(defun collect-events (key D kwd-alist)
  (append (get1 key kwd-alist)
          (collect-events1 D key)))
  

;foll 3 functions copied from FTY/deftypes.lisp 
(defun pred-rule-disablep (rule)
  ;; disable backchain rules, rules that target (pred x), i.e. where the
  ;; argument to pred doesn't have a function symbol, and rules that rewrite
  ;; pred to something other than t
  (b* (((unless (eq (acl2::access acl2::rewrite-rule rule :subclass)
                    'acl2::abbreviation))
        t)
       ((when (symbolp (cadr (acl2::access acl2::rewrite-rule rule :lhs)))) t)
       ((unless (equal (acl2::access acl2::rewrite-rule rule :rhs) ''t)) t))
    nil))

(defun collect-pred-runes-to-disable (rules)
  (if (atom rules)
      nil
    (if (pred-rule-disablep (car rules))
        (cons (acl2::access acl2::rewrite-rule (car rules) :rune)
              (collect-pred-runes-to-disable (cdr rules)))
      (collect-pred-runes-to-disable (cdr rules)))))

(defloop collect-disable-runes-preds (preds wrld)
  (for ((pred in preds)) 
       (append (collect-pred-runes-to-disable (acl2-getprop pred 'acl2::lemmas wrld)))))


(defun collect-keyword-ev (p key)
  (b* (((cons & A) p)
       ((acl2::assocs kwd-alist) A)
       (all-ev (get1 key kwd-alist)))
    all-ev))
   


(defun predicate-events (D kwd-alist wrld)
  (b* ((disable-rules (collect-disable-runes-preds (predicate-names (constituent-types D wrld)) wrld)))

  `(,@(collect-events :pre-pred-events D kwd-alist)
    ,@(funcalls-append (get1 :pre-pred-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)



    (commentary ,(get1 :print-commentary kwd-alist) "~| Predicate events...~%")
    ,@(predicate-events1 D kwd-alist wrld)

    (local (in-theory (acl2::disable* . ,disable-rules))) ;TODO.Note: we can shift this above to make CCG faster
    (local (in-theory (enable ,@(make-predicate-symbol-lst (strip-cars D) (get1 :current-package kwd-alist)))))
      
    ;; ,@(new-conx/record-events D kwd-alist) ;constructor/destructor defs and related
    ,@(funcalls-append (get1 :post-pred-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)
    ,@(collect-events :post-pred-events D kwd-alist)
    )))
    



;; USER COMBINATOR THEORY EVENTS 


;; (defun user-combinator-theory-ev (p top-kwd-alist wrld)
;;   (b* (((cons name A) p)
;;        ((acl2::assocs odef new-constructors kwd-alist) A) ;what about pdef?
;;        (kwd-alist (append kwd-alist top-kwd-alist)))
       
;;     (case-match odef
;;       (('LISTOF cbody) (listof-theory-events name cbody kwd-alist wrld))
;;       (('ALISTOF key-body val-body) (alistof-theory-events name key-body val-body kwd-alist wrld))
;;       (('MAP key-body val-body) (map-theory-events name key-body val-body kwd-alist wrld))
;;       (('RECORD . fname-tname-alist) (b* ((tnames (strip-cdrs fname-tname-alist))
;;                                           ;(- (assert$ (proper-symbol-listp tnames) nil))
;;                                           (dprex (predicate-names tnames))
;;                                           (field-pred-alist (pairlis$ (strip-cars fname-tname-alist) dprex)))
;;                                        (record-theory-events name field-pred-alist kwd-alist wrld)))
;;       (& (if new-constructors
;;              (record-theory-events-lst new-constructors kwd-alist wrld)
;;            '())))))
             

;; (defloop user-combinator-theory-events (ps kwd-alist wrld)
;;   (for ((p in ps)) (append (user-combinator-theory-ev p kwd-alist wrld))))


(defun print-summary-events ( D kwd-alist wrld)
  (declare (ignorable D kwd-alist wrld))
  '())
 





; REGISTER-TYPE EVENT GENERATION

(defun register-type-event (p top-kwd-alist wrld)
  (declare (ignorable top-kwd-alist))
  (b* (((cons name A) p)
       ((acl2::assocs ndef odef pdef new-types kwd-alist) A)
       (M (append new-types (table-alist 'type-metadata-table wrld)))
       (?kwd-alist (append kwd-alist top-kwd-alist)))
    `(register-type ,name
                    :predicate  ,(predicate-name name M)
                    :enumerator ,(enumerator-name name M)
                    :enum/acc ,(get2 name :enum/acc M)
                    :clique ,(strip-cars new-types)
                    :theory-name ,(get1 :theory-name kwd-alist)
                    :def ,odef
                    :normalized-def  ,ndef
                    :prettyified-def ,pdef)))

(defloop register-type-events1 (ps kwd-alist wrld)
  (for ((p in ps)) (collect (register-type-event p kwd-alist wrld))))

(defun register-type-events (ps kwd-alist wrld)
  (cons
   `(commentary ,(get1 :print-commentary kwd-alist) "~| Registering type...~%")
   (register-type-events1 ps kwd-alist wrld)))

       

; TOP-LEVEL EVENT GENERATION

(defun defdata-events (a1 wrld)
  (b* (((list D kwd-alist) a1)) ;a1 is the result of parse-defdata

    `(with-output :on (summary) :off (prove event observation)
       :summary (acl2::form acl2::time)
       (encapsulate nil
         (logic)
         (with-output :summary (acl2::form) :on (error)
           (progn
             ,@(collect-events :pre-events D kwd-alist)
             ,@(funcalls-append (get1 :pre-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)
;             (acl2::acl2s-defaults :set acl2::testing-enabled ,(get1 :testing-enabled kwd-alist))
             (set-bogus-defun-hints-ok t)
             (set-ignore-ok t)
             (set-irrelevant-formals-ok t)
             ;(local (in-theory (disable . ,disable-rules)))
             ;(local (in-theory (enable . ,enable-rules)))

             ,@(predicate-events D kwd-alist wrld)

             
;             ,@(tau-characterization-events D kwd-alist wrld)
;             ,@(polymorphic-inst-defdata-events D kwd-alist wrld)

; Run the above commented out generation functions as post-hooks
             ,@(funcalls-append (get1 :post-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)
             ,@(collect-events :post-events D kwd-alist)


             ;; ,@(enumerator-events D kwd-alist wrld)
             ;; ,@(enumerator/acc-events D kwd-alist wrld)
             ;; ,@(fixer-events D kwd-alist wrld)
             ,@(funcalls-append (get1 :cgen-hook-fns kwd-alist) (list D kwd-alist wrld) wrld)


             ,@(register-type-events D kwd-alist wrld)
             
             . ,(print-summary-events D kwd-alist wrld)))))))
       

; PARSING

; some routines for checking syntax of defdata type expressions


(defloop deref-combinator-alias (comb table)
  (for ((entry in table)) 
       (when (member-eq comb (get1 :aliases (cdr entry)))
         (return (car entry)))))



; some type expressions can be named
; e.g. (x . (cons nat pos)), (left-child . tree)
; we will collect all such names and their binding and do some preliminary syntax checks
; we forbid nested names and all naming should be unique
(mutual-recursion
(defun collect-names-texp (texp ctx B)
  (cond ((possible-constant-value-p texp) '())
        ((atom texp) '())
        ((not (true-listp texp)) (b* (((cons name u) texp)
                                      ((unless (proper-symbolp name))
                                       (er hard? ctx "~| Expecting ~x0 to be a name symbol.~%" name))
                                      (N1 (collect-names-texp u ctx B))
                                      ((unless (null N1))
                                       (er hard? ctx "~| Nested naming currently disallowed! ~
Please use intermediate definitions. If you think you cannot avoid nested naming, please send this example to the implementors.~%")))
                                   (acons name u '())))
        (t (b* ((comb (car texp))
                ((unless (proper-symbolp comb))
                 (er hard? ctx "~| Expecting ~x0 to be a symbol.~%" comb))
                (ccomb (deref-combinator-alias comb B))
                ((when (member-eq ccomb '(acl2s::range acl2s::member))) '()))
                                   
             (collect-names-texps (cdr texp) ctx B)))))


(defun collect-names-texps (texps ctx B)
  (if (atom texps)
      (if (null texps)
          '()
        (er hard? ctx "~| ~x0 is not null. Arguments of a combinator/constructor is expected to be a true-list.~%" texps))
    (b* ((N1 (collect-names-texp (car texps) ctx B))
         (N2 (collect-names-texps (cdr texps) ctx B))
         (non-unique-names (intersection-eq (strip-cars N1) (strip-cars N2)))
         ((when (consp non-unique-names))
          (er hard? ctx "~| Names ~x0 being used more than once.~%" non-unique-names)))
      (append N1 N2))))
    
)

(defun get-arity (comb wrld)
  (or (let ((B (table-alist 'builtin-combinator-table wrld))) 
        (get2 (deref-combinator-alias comb B) :arity B))
      (let ((U (table-alist 'user-combinator-table wrld))) 
        (get2 (deref-combinator-alias comb U) :arity U))
      (get2 comb :arity (table-alist 'data-constructor-table wrld))))




; basic syntax check for defdata type expressions.
; scope is the name scope, in form of an alist/bindings 
;BUGFIX: Earlier I had scope was named it N, but that was overwritten by (n (len (cdr texp)) Woaaa HORRIBLE BUG
; tnames is the type name clique being defined
(mutual-recursion
(defun check-syntax-texp (texp scope tnames ctx wrld)
  (cond ((possible-constant-value-p texp) t)
        ((proper-symbolp texp)
         (or (member-eq texp tnames)
             (assoc-eq texp (table-alist 'type-metadata-table wrld))
             (assoc-eq texp scope) ;in scope
             (er hard? ctx "~| ~x0 should be a recognized name.~%" texp)))
        ((atom texp)
         (er hard? ctx "~| ~x0 should be a constant or a name symbol.~%" texp))

        ((not (true-listp texp)) ;name decl
         (check-syntax-texp (cdr texp) scope tnames ctx wrld))

; combinator or constructor or macro (or dependent functional expression of names)
        (t (b* (((unless (true-listp texp))
                 (er hard? ctx "~| ~x0 should be a true-list.~%" texp))
                (comb (car texp))

                (arity (get-arity comb wrld))
                ((unless (or (not (natp arity))
                             (equal (len (cdr texp)) arity)))
                 (er hard? ctx "~| Arity mismatch! ~x0 expects ~x1 arguments but got ~x2.~%" comb arity (len (cdr texp))))
                
                (B (table-alist 'builtin-combinator-table wrld))
                (bcomb (deref-combinator-alias comb B))
                ((when bcomb)
                 (case bcomb ;range and member are exceptional
                   (acl2s::range (or (member-eq (cadr texp) '(acl2s::integer acl2s::rational))
                              (er hard? ctx "~| Range domain ~x0 should be one of integer or rational.~%" (cadr texp))))
                   (acl2s::member t)
                   (or (if (> (len (remove-duplicates-equal (cdr texp))) 1) ;arity of OR
                           (check-syntax-texps (cdr texp) scope tnames ctx wrld)
                         (er hard? ctx "~| ~x0 expects atleast 2 (distinct) arguments.~%" comb)))
                   (otherwise (check-syntax-texps (cdr texp) scope tnames ctx wrld))))
                ((when (assoc-eq (car texp) (table-alist 'data-constructor-table wrld)))
                 (check-syntax-texps (cdr texp) ;extend scope
                                     (append (collect-names-texps (cdr texp) ctx B) scope) 
                                     tnames ctx wrld)))
             (check-syntax-texps (cdr texp) scope tnames ctx wrld)))))

(defun check-syntax-texps (texps scope tnames ctx wrld)
  (if (endp texps)
      t
    (and (check-syntax-texp (car texps) scope tnames ctx wrld)
         (check-syntax-texps (cdr texps) scope tnames ctx wrld))))
)


(defun is-recursive-type-exp (texp tnames wrld)
  (intersection-eq tnames (texp-constituent-types texp tnames wrld :include-recursive-references-p t)))

(defloop find-recursive-texps (texps tnames wrld)
  (for ((texp in texps)) 
       (append (and (is-recursive-type-exp texp tnames wrld) (list texp)))))
  
(defun normalize-union-texps (texps tnames wrld)
 "remove duplicates and put base cases before recursive texps"
 (b* ((texps (remove-duplicates-equal texps))
      (recursive-texps (find-recursive-texps texps tnames wrld))
      (base-texps (acl2::set-difference-equal texps recursive-texps)))
   (append base-texps recursive-texps)))

(mutual-recursion                 
(defun parse-texp (texp tnames ctx wrld)
  (cond ((possible-constant-value-p texp) (if (quotep texp) texp (kwote texp)))
        ((proper-symbolp texp) texp)
        ((not (true-listp texp)) ;name decl
         (cons (car texp) (parse-texp (cdr texp) tnames ctx wrld)))
; combinator or constructor or macro
        (t (b* ((B (table-alist 'builtin-combinator-table wrld))
                (comb (car texp))
                (bcomb (deref-combinator-alias comb B))
                (C (table-alist 'data-constructor-table wrld)))
             (cond (bcomb ;builtin combinator
                    (case bcomb
                      (acl2s::range (parse-range-exp (third texp) (cadr texp) ctx wrld))
                      (acl2s::member (parse-enum-exp (cadr texp) ctx wrld))
                      (or (b* ((rest (normalize-union-texps (parse-texps (cdr texp) tnames ctx wrld) tnames wrld)))
                            (if (consp (cdr rest))
                                (cons 'or  rest)
                              (car rest)))) ;remove dups and remove the or operator for single constituent
                      (t (cons bcomb (parse-texps (cdr texp) tnames ctx wrld)))))
                   ((assoc-eq comb C) ;data constructor
                    (cons comb (parse-texps (cdr texp) tnames ctx wrld)))
                   ((true-listp (acl2-getprop (car texp) 'acl2::macro-args wrld :default :undefined)) ;a macro
                    (b* (((mv erp ans) ;TODO replace this with pseudo-translate
                          (acl2::macroexpand1-cmp (cons (car texp) (parse-texps (cdr texp) tnames ctx wrld)) ctx wrld (acl2::make acl2::state-vars)))
                         ((when erp) (er hard? ctx "~| Macroexpanding ~x0 failed!~%" texp)))
                      ans))
                         
; either undefined comb/cons, a dependent expression or a new constructor
; (record) to be registered. we will take the benefit of doubt and assume it is
; a new constructor. if it is not, then we will raise error in the
; undefined-product-exps function.
                   (t (cons (car texp) (parse-texps (cdr texp) tnames ctx wrld))))))))

(defun parse-texps (texps tnames ctx wrld)
  (if (endp texps)
      '()
    (cons (parse-texp (car texps) tnames ctx wrld)
          (parse-texps (cdr texps) tnames ctx wrld))))
)


(defun parse-top-texp (name texp tnames ctx wrld)
  (cond ((atom texp) (parse-texp texp tnames ctx wrld))
        ((not (true-listp texp)) ;name decl
         (cons (car texp) (parse-texp (cdr texp) tnames ctx wrld)))
; expand top-level user-defined combinators
        (t (b* ((U (table-alist 'user-combinator-table wrld))
                (ucomb (deref-combinator-alias (car texp) U))
                ((when ucomb) ;user-defined combinator
                 (b* ((f (get2 ucomb :syntax-restriction-fn U))
                      (exp-l (get2 ucomb :expansion U))
                      (parsed-args (parse-texps (cdr texp) tnames ctx wrld)))
                   (if (or (not f) (funcall-w f (list (cdr texp)) ctx wrld))
                       (b* ((eexp (expand-lambda (cons exp-l (list (kwote name) (kwote parsed-args)))))
                            ((mv erp result) (trans-my-ev-w eexp ctx wrld nil))
                            ((when erp)
                             (er hard? ctx "~| Eval failed in user-combinator expansion of ~x0.~%" texp)))
                         result)
                         
                     (b* ((x0-str (get2 ucomb :syntax-restriction-msg U))
                          (msg (to-string1 x0-str (acons #\0 (cdr texp) '()))))
                       (er hard? ctx "~| ~s0 ~%" msg))))))
             (parse-texp texp tnames ctx wrld)))))



(defun valid-record-field-p (x N)
  (and (assoc-eq x N)
       (let ((texp (cdr (assoc-eq x N))))
;texp should be a typename:
         (and (proper-symbolp texp) 
              (not (assoc-eq texp N))))))

(defloop valid-record-fields-p (xs N)
  (for ((x in xs)) (always (and (consp x) (valid-record-field-p (car x) N)))))

(mutual-recursion
(defun undefined-product-texp (texp ctx N wrld)
  (cond ((possible-constant-value-p texp) nil)
        ((proper-symbolp texp) nil)
        ((not (true-listp texp)) nil)
; combinator or constructor or new
        (t (b* ((comb (car texp))
                (B (table-alist 'builtin-combinator-table wrld))
                (C (table-alist 'data-constructor-table wrld)))
             (cond ((assoc-eq comb B) ;builtin combinator
                    (case comb
                      (acl2s::range nil)
                      (acl2s::member nil)
                      (t (undefined-product-texps (cdr texp) ctx N wrld))))
                   ((assoc-eq comb C) ;data constructor -- extend scope
                    (undefined-product-texps (cdr texp) ctx (append (collect-names-texps (cdr texp) ctx B) N) wrld))
                   (t ;possible new  constructor -- extend scope
;TODO: add dependent expression support here.
                    (if (not (acl2::new-namep (car texp) wrld))
                        (er hard? ctx "~| ~x0 should be a fresh logical name.~%"  (car texp))
; lets not allow nested new constructors/records -- too much flexibility.
                      (if (valid-record-fields-p (cdr texp) (append (collect-names-texps (cdr texp) ctx B) N))
                        (list texp)
                        (er hard? ctx "~| Bad Syntax! Did you want to define a new record? Each record argument should be of form (field-name . type-name). There should be no name overlap among fields and types.~%" )))))))))

(defun undefined-product-texps (texps ctx N wrld)
  (if (endp texps)
      '()
    (append (undefined-product-texp (car texps) ctx N wrld)
            (undefined-product-texps (cdr texps) ctx N wrld))))
)


; this is hacking. to be consistent we need to drive this from tables.
(defun untrans-top-texp (name nbody conx-entries)
  "prettyify a normalized/core defdata top texp"
  (let ((acl2::tname name)) ;REPORT to Matt!
  (case-match nbody
    (('OR 'NIL ('ACONS key val !tname)) (list 'alistof key val))
    (('OR 'NIL ('CONS ('CONS key val) !tname)) (list 'alistof key val))
    (('OR 'NIL ('MSET key val !tname)) (list 'map key val))
    (('LISTOF ('CONS key val)) (list 'alistof key val))
    (('OR 'NIL ('CONS x !tname)) (list 'listof x))
    ((!tname . args) (if (assoc-eq name conx-entries) ;new record being constructed
                         (cons 'record args)
                      (cons name args)))
    (('RANGE dom range-exp) (list 'range dom (kwote range-exp)))
    (& nbody))))



(defun data-constructor-basis (prod curr-pkg M)
  (b* ((conx-name (car prod))
       (fname-tname-alist (cdr prod))
       (fnames (strip-cars fname-tname-alist))
       (preds (predicate-names (strip-cdrs fname-tname-alist) M))
       (recog (make-predicate-symbol conx-name curr-pkg))
       (fname-pred-alist (pairlis$ fnames preds))
       (prefix (get-dest-prefix conx-name))
       (selector-fn-names (modify-symbol-lst prefix fnames "" curr-pkg))
       (dest-pred-alist (pairlis$ selector-fn-names preds)))
    (cons conx-name (acons :arity (len (cdr prod)) (acons :recog recog 
                                                          (acons :dest-pred-alist dest-pred-alist 
                                                                 (acons :field-pred-alist fname-pred-alist '())))))))
       
(defloop data-constructor-bases (prods curr-pkg M)
  (for ((prod in prods)) (collect (data-constructor-basis prod curr-pkg M))))


(defun type-metadata-basis (tname curr-pkg)
  (declare (xargs :guard (symbolp tname)))
  (b* ((minimal-vals (list (make-predicate-symbol tname curr-pkg) 
                           (make-enumerator-symbol tname curr-pkg) 
                           (make-uniform-enumerator-symbol tname curr-pkg)))
       (minimal-keys '(:predicate :enumerator :enum/acc)))
    (cons tname (pairlis$ minimal-keys minimal-vals))))

(defloop type-metadata-bases (tnames curr-pkg)
    (declare (xargs :guard (symbol-listp tnames)))
  (for ((tname in tnames)) (collect (type-metadata-basis tname curr-pkg))))




(defconst *per-def-keywords* '(:satisfies :satisfies-fixer :equiv :equiv-fixer))





(defun parse-data-def (def tnames args curr-pkg ctx wrld)
  (declare (ignorable args))
  (b* (
       ((unless (consp def))
        (er hard? ctx "~| def ~x0 is empty.~%" def))
       ((list* tname body kwd-val-list) def)
       ((unless (symbolp tname))
        (er hard? ctx "~| name ~x0 should be a symbol.~%" tname))
       
;       (kwd-val-list (append kwd-val-list args))
       ((mv kwd-alist ?rest) (extract-keywords ctx *per-def-keywords* kwd-val-list '()))
      

; check if names are not nested and are unique
       (N (collect-names-texp body ctx (table-alist 'builtin-combinator-table wrld)))
       (M (table-alist 'type-metadata-table wrld))
       (cmn-nms (intersection-eq (strip-cars N) (strip-cars M)))
       ((when cmn-nms)
        (er hard? ctx "~| Naming of defdata expressions should be disjoint from the type namespace (~x0 are types).~%" cmn-nms))
       (fbd-nms (intersection-eq (strip-cars N) (forbidden-names)))
       ((when fbd-nms)
        (er hard? ctx "~| These names (~x0) are not allowed. Please choose anew and try again.~%" fbd-nms))

;simple syntax checks (Note that at this point macros have not been expanded away) TODO
       (- (check-syntax-texp body '() tnames ctx wrld))

;todo: check if the generated pred/enum/acc names are new in wrld or not

;normalizing type expressions
       (nbody (parse-top-texp tname body tnames ctx wrld))


;collect new constructors (records) being defined
       (prods (undefined-product-texp nbody ctx '() wrld))

;new types and constructors are new entries in M and C respectively that we assume!
       (new-types (type-metadata-bases tnames curr-pkg))
       (new-constructors (data-constructor-bases prods curr-pkg (append new-types M)))

; notify downstream code of recursive records and recursive types
       (new-preds (predicate-names tnames (append new-types M)))
       (recp (or (consp (find-recursive-records new-preds new-constructors))
                 (intersection-eq (texp-constituent-types nbody tnames wrld :include-recursive-references-p t) tnames)))
       (kwd-alist (put-assoc-eq :recp recp kwd-alist))

; specially handle allp aliases
       (allp-alias-events (and (proper-symbolp nbody) (is-allp-alias nbody wrld)
                               `((table allp-aliases ',(predicate-name tname new-types) ',tname :put))))
       (kwd-alist (put-assoc-eq :post-pred-events 
                                (append (get1 :post-pred-events kwd-alist) allp-alias-events)
                                kwd-alist))


;prettyify
       (pbody (untrans-top-texp tname nbody new-constructors))
       (new-types (put2-fn tname :prettyified-def pbody new-types))

       ;; (reg-conx-ev (register-record-constructor-events new-constructors kwd-alist))
       ;; (kwd-alist (put-assoc-eq :post-events 
       ;;                          (append (get1 :post-events kwd-alist) reg-conx-ev) 
       ;;                          kwd-alist))

       )

    (cons tname (list (cons 'name tname)
                      (cons 'ndef nbody) ;normalized
                      (cons 'N N) ;name binding
                      (cons 'pdef pbody) ;pretty
                      (cons 'odef body) ;orig
                      (cons 'new-constructors new-constructors)
                      (cons 'new-types new-types)
                      (cons 'kwd-alist kwd-alist)))))
    

(defloop parse-data-defs (ds tnames kwd-args curr-pkg ctx wrld)
  (for ((d in ds)) 
       (collect (parse-data-def d tnames kwd-args curr-pkg ctx wrld))))


#||
(:conc-name      . nil)  
(:tag            . :0_conc_name_)
(:dest-prefix    . "_conc-name_-")  
(:modifier-prefix . "SET-_conc-name_-")
(:inline          . nil)))
||#



(defconst *defdata-keywords* 
  (append '(:pred-prefix 
            ;:pred-suffix :enum-prefix :enum-suffix :enum/acc-prefix :enum/acc-suffix
            ;:pred-guard :enum-guard :enum/acc-guard
            :theory-name
            :debug :print-commentary :print-summary :time-track
            ;; :pre-pred-hook-fns :post-pred-hook-fns
            ;; :pre-hook-fns :post-hook-fns
            :testing-enabled)
          '(:hints :verbose)
          ))

(defun delete-assoc-eq-lst (keys alst)
  (if (endp keys)
      alst
    (delete-assoc-eq-lst (cdr keys) (delete-assoc-eq (car keys) alst))))

(defun parse-defdata (args curr-pkg wrld)
  (b* (((mv ds kwd-val-list) (separate-kwd-args args '()))
       (ctx 'parse)

      (defaults-alst (table-alist 'defdata-defaults-table wrld)) ;TODO chek
      (defaults-alst (delete-assoc-eq-lst (evens kwd-val-list) defaults-alst))
      ((mv kwd-alist rest-args) (extract-keywords ctx *defdata-keywords* kwd-val-list defaults-alst))
      (acl2-defaults-tbl (table-alist 'acl2::acl2-defaults-table wrld))
      (current-termination-method-entry (assoc :termination-method acl2-defaults-tbl))
      (kwd-alist (put-assoc-eq :termination-method current-termination-method-entry kwd-alist))

      (tnames (if (symbolp (car ds)) (list (car ds)) (strip-cars ds)))
      (theory-name (s+ (car tnames) "-THEORY" :pkg curr-pkg))
      (kwd-alist (put-assoc-eq :theory-name theory-name kwd-alist))
      (kwd-alist (put-assoc-eq :clique tnames kwd-alist))
      (preds (make-predicate-symbol-lst tnames curr-pkg)) ;these are not yet defined, so we choose the predicate naming convention
      (kwd-alist (put-assoc-eq :post-pred-events 
                               `((acl2::def-ruleset! ,theory-name ',preds)) ;definitions
                                 kwd-alist))
      (kwd-alist (put-assoc-eq :current-package curr-pkg kwd-alist))

      ((unless (and (consp ds) 
                     (true-listp ds)))
       (er hard? ctx "~| Empty form not allowed.~%"))

      ((when (and (not (symbolp (car ds)))
                  (consp (cdr ds)))) ;atleast 2 types
       (list (parse-data-defs ds tnames rest-args curr-pkg ctx wrld) kwd-alist))


       (d (if (symbolp (car ds)) ds (car ds))) 
;rename ds to d to avoid confusion, d is the single definition
       ((unless (> (len d) 1))
        (er hard? ctx "~| Empty definition.~%" ))

       ((unless (null (cddr d)))
         (er hard? ctx "~| Definitions that are not mutually-recursive should be ~
                      of form (defdata <id> <type-exp> [:hints <hints>
                     ...]).~%" )))

    (list (parse-data-defs (list d) tnames args curr-pkg ctx wrld) kwd-alist)))

    
(defmacro defdata (&rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all))
                  :gag-mode t
                  :stack :push
       (make-event
        (defdata-events (parse-defdata ',args (current-package state) (w state)) (w state))))))








(defun make-subsumes-relation-name (T1 T2)
  (let* ((str1 (symbol-name T1))
        (str2 (symbol-name T2))
        (str11 (string-append str1 "-IS-SUBTYPE-OF-"))
        (str (string-append str11 str2)))
    (intern$ str "DEFDATA")))

(defun make-disjoint-relation-name (T1 T2)
  (let* ((str1 (symbol-name T1))
         (str2 (symbol-name T2))
         (str11 (string-append str1 "-IS-DISJOINT-WITH-"))
         (str (string-append str11 str2)))
    (intern$ str "DEFDATA")))


;COPIED FROM DEFDATA ----- to be deprecated and deleted
(defun compute-defdata-relation (T1 T2 hints rule-classes otf-flg doc ctx wrld)
    (b* ((T1p (predicate-name T1))
         (T2p (predicate-name T2))
         (M (table-alist 'type-metadata-table wrld))
         ((unless (and (assoc-eq T1 M)
                       (assoc-eq T2 M)))
;if not existing typenames raise error
        (er hard ctx  "~|One of ~x0 and ~x1 is not a defined type!~%" T1 T2))
       
;; ((when (and rule-classes
;;                    (or (eq T1 'ACL2::ALL)
;;                        (eq T2 'ACL2::ALL))))
;; ;if not existing typenames raise error
;;         (er hard ctx  "~|Subtype/disjoint relation not allowed on predicate ALL with non-empty rule-classes~%"))
       (rule-classes (if (or (is-allp-alias T1p wrld)
                             (is-allp-alias T2p wrld))
                         '()
; force not to be a tau-rule bcos tau complains
                          rule-classes))
       ((when (or (and (eq ctx 'defdata-disjoint)
                       (disjoint-p T1p T2p wrld))
                  (and (eq ctx 'defdata-subtype)
                       (subtype-p T1p T2p wrld))))
          '(value-triple :redundant))
       (form (if (eq ctx 'defdata-disjoint)
                 `(implies (,T1p x) (not (,T2p x)))
               `(implies (,T1p x) (,T2p x))))
       (nm (if (eq ctx 'defdata-disjoint)
               (make-disjoint-relation-name T1 T2)
             (make-subsumes-relation-name T1 T2)))

       (event-form `((defthm ,nm
                       ,form
                       :hints ,hints
                       :rule-classes ,rule-classes
                       :otf-flg ,otf-flg
                       :doc ,doc)))
       (ev-form-to-print `(defthm ,nm
                            ,form 
                            ,@(and hints
                                   `((:hints ,hints)))
                            ,@(and rule-classes
                                  `((:rule-classes ,rule-classes)))))

       (- (cw "~|Submitting ~x0~|" ev-form-to-print)))
           
             `(progn
;macros call so dont need quotes
                ,@event-form
                (value-triple :success))))



 
(defmacro defdata-subtype (T1 T2 
                               &key (rule-classes '(:tau-system))
                               verbose
                               hints otf-flg doc)
  (declare (xargs :guard (and (proper-symbolp T1)
                              (proper-symbolp T2)
                              )))
  `(with-output ,@(and (not verbose) '(:off :all)) :stack :push

       (make-event 
        (compute-defdata-relation ',T1 ',T2  
                                  ',hints ',rule-classes ',otf-flg ',doc
                                  'defdata::defdata-subtype (w state)))))

(defmacro defdata-disjoint (T1 T2 
                               &key (rule-classes '(:tau-system))
                               verbose
                               hints otf-flg doc)
  (declare (xargs :guard (and (proper-symbolp T1)
                              (proper-symbolp T2)
                              )))
  `(with-output ,@(and (not verbose) '(:off :all)) :stack :push

       (make-event 
        (compute-defdata-relation ',T1 ',T2  
                                  ',hints ',rule-classes ',otf-flg ',doc
                                  'defdata::defdata-disjoint (w state)))))
       

(logic)
; misc functions needed by other files in cgen

;;is a predicate explicitly recognized in the defdata framework? 
;;if true then returns the corresponding type
;; BUG here, with every change of type table, you might have to change this function
(defun is-datadef-type-predicate (fn-name M)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp fn-name)
                              (symbol-alistp M))))
  (if (endp M)
    nil
    (b* (((cons typ al) (car M)))
      (if (eq fn-name (cdr (assoc-eq :predicate al))) ;TODO: here for multiple pred aliases
          typ
        (is-datadef-type-predicate fn-name (cdr M))))))


;is a possible type (ASK:should we also pick compound recognizers?)
;is either custom type pred or datadef pred
;if true then returns the type name (not the predicate)
;Sig: Sym * World -> Sym
(defun is-type-predicate-current (fn-name wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp fn-name)
                              (plist-worldp wrld))))
  (is-datadef-type-predicate fn-name (table-alist 'type-metadata-table wrld)));is in types table
  
(defun is-type-predicate-gv (fn w)
  (declare (xargs :guard t))
  (ec-call (is-type-predicate-current fn w)))

(defattach is-type-predicate is-type-predicate-gv)


(defun is-a-typeName-current (type wrld)
  (declare (xargs :verify-guards nil))
  (predicate-name type wrld))
  

(defun is-a-typeName-gv (type wrld)
  (declare (xargs :guard t))
  (ec-call (is-a-typeName-current type wrld)))

(defattach is-a-typeName is-a-typeName-gv)






;;; Block Comments with headlines (line starting with a *) are meant
;;; be read in org-mode.

#||
* Initial Essay on Design
<2014-04-20 Sun 08:01>

Read this in org-mode.

This is a rewrite of [[file:defdata.lisp]] whose original author is Peter
Dillinger. 

The design of defdata library revolves around two data structures; the
[[Combinators and Constructors][first]] contains information that describes the syntax of the defdata
language and facilitates automatic generation of various events
(defun, defthm etc), the [[Type Metadata][second]] records metadata for each type name
registered and introduced (by defdata). Both the data structures are
designed to be extensible. Both are implemented as ACL2 tables. This
might not be very efficient, but it is important for this metadata to
be stored in the logical world, for undoing precludes the use of
stobjs, and renders other design choices such as global/array
inconvenient. The user-level insert access to first table is provided
by register-data-constructor and register-combinator macros.  The
user-level insert access to the second table is provided by
register-type macro. The defdata form itself is a "user" of these two
tables. There is also a third table used by defdata which stores the
defaults for various top-level parameters/keyword-arguments to defdata
form.

* Combinators and Constructors
[2014-04-22 Tue 23:37]

The main data structure to maintain and extend is the primitive
combinator, data constructor and user-defined combinator tables, which
describes the syntax of core defdata language (type expressions). The
keys of the tables are respectively: builtin type combinators like
oneof, enum, range, data constructors (for product types), and
user-defined combinators that expand to builtin combinators and
product constructors. The "value" data in these tables is used in
mechanically generating the predicate, enumerator functions,
accessor/constructor functions, defthm events, such as those rules
that characterize the type (inclusion/exclusion) relations and finally
events that comprise a theory of the type being defined. In a sense,
the "value" data encodes the computation that defdata needs to do.

We will store this data as an keyword-value-alist; the following ASCII
tables capture their form:

** Builtin combinators
[2014-04-23 Wed 14:09]
| property name   | kind of value        | default  |
|-----------------+----------------------+----------|
| :aliases        | listof names         | '(_key_) |
|-----------------+----------------------+----------|
| :arity          | pos or t (variadic)  |          |
|-----------------+----------------------+----------|
| :pred-I         | \x s. pred-expr or nil       |          |
|-----------------+----------------------+----------|
| :pred-inverse-I | \e. core-defdata exp or nil |          |
|-----------------+----------------------+----------|
| :enum-I         | \n s. enum-expr        |          |
|-----------------+----------------------+----------|
| :enum/acc-I     | \m seed s. enum2-expr       |          |
|-----------------+----------------------+----------|
| :gen-I          | \s. generator-expr   |          |
|-----------------+----------------------+----------|
| :fixer-I        | \s dom. fixer-expr   |          |
|-----------------+----------------------+----------|
| :type-class     | type-class           |          |
|-----------------+----------------------+----------|

Notes: meta-variable s ranges over core defdata expressions.
meta-variable e ranges over ACL2 expressions I above is short for
interpretation. The idea is that given a core-defdata expression, it
can be interpreted to give a predicate expression, enumerator
expression(s), fixer expression(s), generator expression etc.
The pred/enum-I can be null, in which case the generating functions
have the responsibility of handling these.

** Data constructors
[2014-04-23 Wed 23:32] 

The following accomodates both primitive and user-defined
constructors.
| property name          | kind of value       | default         | notes                           |
|------------------------+---------------------+-----------------+---------------------------------|
| :proper                | boolean             | t               | uniquely decomposable           |
|------------------------+---------------------+-----------------+---------------------------------|
| :arity                 | natp                |                 |                                 |
|------------------------+---------------------+-----------------+---------------------------------|
| :recog                 | fn name             | '_key_p         |                                 |
|------------------------+---------------------+-----------------+---------------------------------|
| :dest-pred-alist     | symbol-alist        |                 | pred is a pred fn name
|------------------------+---------------------+-----------------+---------------------------------|
| :local-events          | listof events       | '()             | supporting events               |
|------------------------+---------------------+-----------------+---------------------------------|
| :export-defthms        | listof events       | '()             |                                 |
|------------------------+---------------------+-----------------+---------------------------------|
| :polymorphic-events    | listof template     | '()             | poly func inst                  |
|------------------------+---------------------+-----------------+---------------------------------|
| :polymorphic-type-form | texp with type vars | nil             | e.g. (cons :a :b)               |
|------------------------+---------------------+-----------------+---------------------------------|
| :theory-name           | symbol              | '_key_-THEORY   | name of deftheory               |
|------------------------+---------------------+-----------------+---------------------------------|

Notes: 

** User-defined combinators
[2014-04-24 Thu 00:17]

User-defined (defdata also uses this) combinators like listof,
alistof, map, expand to core defdata type expressions. Usually these
have stricter syntax restriction, generate a lot more defthm events are
to install appropriate theories and to support polymorphism.

| property name          | kind of value          | default  | notes                  |
|------------------------+------------------------+----------+------------------------|
| :arity                 | posp                   |          |                        |
|------------------------+------------------------+----------+------------------------|
| :aliases               | listof names           | '(_key_) | user can add aliases   |
|------------------------+------------------------+----------+------------------------|
| :type-class            | type-class             |          |                        |
|------------------------+------------------------+----------+------------------------|
| :expansion             | core defdata type expr |          | * is type name         |
|------------------------+------------------------+----------+------------------------|
| :syntax-restriction    | lambda form            |          | arg is unexpanded body |
|------------------------+------------------------+----------+------------------------|
| :local-events          | listof events          | '()      | supporting events      |
|------------------------+------------------------+----------+------------------------|
| :export-defthms        | listof events          | '()      |                        |
|------------------------+------------------------+----------+------------------------|
| :polymorphic-events    | listof template        | '()      | poly func inst         |
|------------------------+------------------------+----------+------------------------|
| :polymorphic-type-form | texp with type vars    | nil      | e.g. (listof :a)       |
|------------------------+------------------------+----------+------------------------|
| :theory-name           | symbol                 |          | name of deftheory      |





* Global defdata defaults
[2014-04-23 Wed 12:09]

| name              | kind of value | default               |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :pred-suffix      | string        | "p"                   |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :enum-prefix      | string        | "nth-"                |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :pred-guard       | lambda expr   | (lambda (x) t)        |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :enum-guard       | lambda expr   | (lambda (x) (natp x)) |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :enum/acc-guard   | "       "     |                       |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :verbose          | boolean       | nil                   |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :debug            | boolean       | nil                   |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :print-commentary | boolean       | t                     |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :print-summary    | boolean       | t                     |                              |
|-------------------+---------------+-----------------------+------------------------------|
| :time-track       | boolean       | t                     |                              |
|-------------------+---------------+-----------------------+------------------------------|


* Type Metadata
[2014-04-20 Sun 22:22] 

The keys of this table are type names and values, satisfying
keyword-value-alistp, capture/record important information about the
type. The keys of the keyword-value-alist itself will be called
properties (of the type). Each property name is given as a keyword;
the properties that are not external (internal) are computed by the
insert/update function; external properties that have no defaults are
mandatory and provided by user.


The following ASCII table shows the form of keyword-value-alist
capturing the metadata associated with each typename.

| property name    | kind of value    | default | internal | additional notes                |
|------------------+------------------+---------+----------+---------------------------------|
| :tau-recog-id    | nat              |         | yes      | from tau-database               |
|------------------+------------------+---------+----------+---------------------------------|
| :predicate       | 1-arity fn       |         | no       |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :size            | oneof pos t      | 't      | no       |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :enumerator      | 1-arity fn       |         | no       |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :enum/acc        | 2-arity fn       |         | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :enum/test       | 1-arity fn       |         | no       |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :enum/test/acc   | 2-arity fn       |         | yes      | acc version of enum/test        |
|------------------+------------------+---------+----------+---------------------------------|
| :equiv           | 2-arity fn       | 'equal  | no       | equivalence rel                 |
|------------------+------------------+---------+----------+---------------------------------|
| :equiv-fixer     | 1-arity fn       | n/i     | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :fixers          | alistof dom fn   | '()     | yes      | fn is 1-arity                   |
|------------------+------------------+---------+----------+---------------------------------|
| :base            | acl2 object      |         | yes      | base/default val                |
|------------------+------------------+---------+----------+---------------------------------|
| :generator       | generator%       | n/i     | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :sampling        | listof quot objs | '()     | no/yes   | an assorted sampling for cgen   |
|------------------+------------------+---------+----------+---------------------------------|
| :closed-under    | fn names         | '()     | yes      | polymorphism support?           |
|------------------+------------------+---------+----------+---------------------------------|
| :clique          | type names       | '()     | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :lub             | type name        | n/i     | no/yes   | smallest supertype in lattice   |
|------------------+------------------+---------+----------+---------------------------------|
| :glb             | type name        | n/i     | no/yes   | biggest subtype in type lattice |
|------------------+------------------+---------+----------+---------------------------------|
| :type-class      | type-class       | :undef  | yes      | is this needed?                 |
|------------------+------------------+---------+----------+---------------------------------|
| :def             | defdata body     | 'key    | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :prettyified-def | "         "      | 'key    | yes      | untrans/prettyified             |
|------------------+------------------+---------+----------+---------------------------------|
| :normalized-def  | core " "         | 'key    | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|
| :consistent-p    | boolean          | nil     | yes      |                                 |
|------------------+------------------+---------+----------+---------------------------------|

** Invariants:
- <<Tau predicate>> :: predicate should be recognized by Tau.
-  :: 
      
      
** Examples of future extensions:
- improper constructors :: non-uniquely decomposable functions
  1. (defdata enum-string (string-append "nth-" string))
  2. 
- dependent types :: (leave this for now... TAU characterization an obstacle)
  1. x (defdata graph (record (vertices . vertex-list) (edges . (map vertices (listof vertices)))))
  2. 
  3. (defdata a-kind-of-list (cons (len x) (x as true-list))) ;A list implementation, whose len is in car
- quotient types :: equivalence relation (other than equal)
  1. (defdata vertices-set (set (listof vertex)))
  2. 
  3. (defdata vertices-set (listof vertex) :equiv set-equal)

- x (defdata edge-list (alistof vertex pos-rational) :no-duplicatesp t)
- (defdata graph (alistof vertex edge-list))

- predicate subtypes :: refinement types, arbitrary constraints
  1. (defdata no-dup-list (oneof nil (cons (x as all) (y as no-dup-list))) :satisfies (not (member x y)))
  2. (defdata no-dup-list (oneof nil (cons (and all (not (member y))) (y as no-dup-list))))
  3. (defdata 
  4. (defdata same-length-lists (l) (listof (x as (listof pos))) :satisfies (= (len x) l))
     

* general plan of action
top down

defdata macro
- syntax check (use main table)
- normalize (use main table)
- pre
- main generation of events
  + prepwork events
  + pred
  + enum(s)
  + fixer(s)
  + tau characterization events
  + postwork events
  + post computation
  + record in metadata table
- post
- print summary

register-type macro
- syntax check
- semantics check (type consistency etc)
- generate enumerator and fixers if possible
- post computation
- record in metadata table
- print summary

register-data-constructor macro
- syntax check
- semantics check
- prepwork events
- constructor axiomatization - dest elim, generalize, type lemmas (tau characterizing) etc
- post computation
- record in constructor table
- print summary

register-user-combinator macro
- syntax check
- post computation
- record in combinator table

||#

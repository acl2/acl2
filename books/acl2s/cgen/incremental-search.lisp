#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")
(include-book "simple-search")
(include-book "select")




;[2015-08-29 Sat] Extend to support symbolic assignments.  The idea is
; to expand recursive types lazily (symbolically) by starting from its
; lower bound shape and then expanding (unrolling) its recursive cases.


(defloop contains-var (x terms)
  "filter terms that contain variable x"
  (for ((term in terms)) (append (and (member-eq x (all-vars term))
                                      (list term)))))

; This function only gives a preciser symbolic value/shape for x; no
; decisions.
(def implied-symbolic-value (x type H vl state)
  (decl :sig ((symbol defdata-type pseudo-term-listp fixnum state) -> (mv erp pseudo-term state))
        :mode :program
        :doc "Assign to x: From type get the (recursive) type for
x. then look into additional constraints from H, to infer any lower-bounds or
narrower shape. return (mv exp new-hyps), where new-hyps are
new constraints on the introduced variables")
  (b* ((additional-constraints (contains-var x H)))
    (refine-enum-shape x type additional-constraints vl state)))
       


(defun remove-non-constant-value-entries (A)
  (declare (xargs :verify-guards nil ;v7.1 rewrite-loop
                  :guard (alistp A)))
  (if (endp A)
      '()
    (b* (((cons & val) (car A))
         ((unless (defdata::possible-constant-value-p val)) (remove-non-constant-value-entries (cdr A))))
      (cons (car A) (remove-non-constant-value-entries (cdr A))))))


(def get-concrete-value (cs% partial-A sm vl ctx wrld state)
  (decl :sig ((fixnum cs% symbol-doublet-listp
                      sampling-method fixnum symbol plist-world state )
              -> (mv erp (list pseudo-term keyword nil) state))
        :mode :program
        :doc "How: From cs% get the enumcall. trans-eval enumcall to
get value to be assigned. quote it to obtain a term. return (mv
val :decision nil), if size of type attributed to x is greater than 1,
otherwise return (mv val :implied nil) -- nil stands for empty
additional hyps")
  (f* ((_eval-single-value (call)
                           (b* ((vexp (if partial-A 
                                          `(let ,partial-A 
                                             (declare (ignorable ,@bound-vars))
                                               ,call) 
                                        call))
                                (- (cw? (debug-flag vl) 
                                        "~|CEgen/Debug/incremental:  ASSIGN x to eval[~x0]~|"  vexp)))
                             (trans-eval-single-value vexp ctx state))))

    (b* ((- (assert$ (cs%-p cs%) 'get-concrete-value))
         ;;hack [2015-09-19 Sat] TODO
         (partial-A (remove-non-constant-value-entries partial-A))
         
         (bound-vars (strip-cars partial-A))
         ((mv size min max calls) (cs%-enumcalls cs% ctx wrld bound-vars))
         
         (seed. (defdata::getseed state))
         ((mv erp seed. ans state)
          (case sm
            (:uniform-random 
             (b* (((mv m seed.) (defdata::choose-size min max seed.))
                  (call `(acl2::mv-list 2 ;arity -- pete caught this missing arity on 17 July '13
                                        (let ((seed. ,seed.))
                                          ,(subst m 'm (second calls)))))
                  ((mv erp ans2 state) (_eval-single-value call)))
               (mv erp (cadr ans2) (car ans2) state)))
            
            (otherwise
             (b* (((mv r seed.) (defdata::random-natural-seed seed.))
                  (call (subst r 'r (first calls)))
                  ((mv erp ans state) (_eval-single-value call)))
               (mv erp seed. ans state)))))
         ((when (or erp (equal size 0))) (mv t nil state)) ;signal error
         
         (state (defdata::putseed seed. state))
         (val-term       (kwote ans)))
      (if (equal size 1) ;size=0 is not possible, also size can be T (inf)
          (value (list val-term :implied))
        (value (list val-term :decision))))))



(defloop get-corr-type-hyp (fn H)
  (for ((hyp in H)) (if (and (consp hyp)
                             (eq fn (car hyp))
                             (proper-symbolp (cadr hyp)))
                        (return hyp))))

;; [2016-10-29 Sat] remove the hyp responsible for symbolic expansion
;; and return the updated hyps as a whole! API change

(def assign-value (x cs% H partial-A sm vl ctx state)
  (decl :sig ((fixnum cs% pseudo-term-listp symbol-doublet-listp symbol-doublet-listp
                      sampling-method fixnum symbol plist-world state )
              -> (mv erp (list pseudo-term keyword pseudo-term-listp) state))
        :mode :program
        :doc "assign a value (expression) to variable x under given constraints")
  
  (b* ((type (access cs% defdata-type))
       (wrld (w state))
       (M (table-alist 'defdata::type-metadata-table wrld))
       (A (table-alist 'defdata::type-alias-table wrld))
       ((when  (and (not (defdata::recursive-type-p type wrld))
                    (record-p type wrld)))
        (b* (((mv rec-expansion field-type-hyps)
              (expand-record x type wrld))
             (type-hyp (get-corr-type-hyp
                        (defdata::predicate-name type A M)
                        H))
             (updated-H (remove-equal type-hyp
                                      (union-equal field-type-hyps H))))
              (value (list rec-expansion :expand updated-H))))
              
       ((er ans) (implied-symbolic-value x type H vl state))
       ((list refined-term additional-hyps) ans))
    (if (or (null additional-hyps) (equal refined-term x))
        (b* (((er (list cval kind))
              (get-concrete-value cs% partial-A sm vl ctx wrld state)))
          (value (list cval kind H)))
      (b* ((type-hyp (get-corr-type-hyp
                      (defdata::predicate-name type A M)
                      H)))
        (value (list refined-term
                     :expand
                     (remove-equal type-hyp
                                   (union-equal additional-hyps H))))))))

(defun put-val-A (name val dlist) ;use mset instead?
  "put list binding name->val in the front"
  (declare (xargs :guard (symbol-doublet-listp dlist)))
  (if (assoc-equal name dlist)
      (put-assoc-equal name (list val) dlist)
    (acons name (list val) dlist)))
  



; a% represents the snapshot of the beginning of the dpll do-while loop
(defrec a% ((hyps concl vars partial-A elim-bindings type-alist tau-interval-alist) ;args to simple search
            ((var . cs) val kind i . inconsistent?) ;result of assign and propagate
            ) 
  NIL)

(defun a%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('a% (hyps concl vars partial-A elim-bindings type-alist tau-interval-alist) 
          ((var . cs) val kind i . inconsistent?))

     ;==>
     (and (symbol-listp vars)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-doublet-listp partial-A)
          (symbol-doublet-listp elim-bindings)
          (symbol-alistp type-alist)
          (symbol-alistp tau-interval-alist)
          (symbolp var)
          (pseudo-termp val)
          (member-eq kind (list :na :expand :implied :decision)) ;added [2015-08-29 Sat]
          (natp i)
          (booleanp inconsistent?)
          (or (null cs) (cs%-p cs))
          ))))
                                   
(defun a%-listp (v) ;STACK
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (a%-p (car v))
         (a%-listp (cdr v)))))




; defabbrev was a BAD idea. I should make this a defun, to avoid variable
; capture bugs. For example I was assigning .. :var x ... instead of :var x1
; below, where x would have been the previously selected variable and unless I
; tested carefully I would not have gotten hold of this simple programming err.
; May 24th '12: making this into a defun
; 18 July '13 -- modified to a simplified signature
(def assign-propagate (a% name sm top-vt-alist vl ctx state)
  (decl :sig ((a% string sampling-method symbol-doublet-list
                  fixnum symbol state)
              -> (mv erp (list pseudo-term-list pseudo-term symbol-list 
                               symbol-doublet-list symbol-alist symbol-alist a%) state))
        :mode :program
        :doc "assign a value to a%.x and propagate this new info to obtain the updated a%")
  (b* ((`(a% ,LV . &) a%)
;ACHTUNG: a% defrec exposed
        ((list H C vars partial-A elim-bindings type-alist tau-interval-alist) LV)
        ((mv x i) (mv (access a% var) (access a% i)))
        (wrld (w state))
        (acl2-vt-dlist (var-types-alist-from-acl2-type-alist type-alist vars '()))
       ((mv erp top+-vt-dlist) (meet-type-alist acl2-vt-dlist top-vt-alist vl (w state)))
       (top+-vt-dlist (if erp (make-weakest-type-alist vars) top+-vt-dlist))
; infer enum shape
        (cs% (or (access a% cs) ;already computed
                 (assert$ (member-eq x vars)
                          (cdr (assoc-eq x (collect-constraints% 
                                            (cons (cgen-dumb-negate-lit C) H) vars
                                            top+-vt-dlist
                                            type-alist tau-interval-alist
                                             vl wrld))))))
       
        ((mv erp ans state) (assign-value x cs% (cons (cgen-dumb-negate-lit C) H)
                                          partial-A sm vl ctx state)) ;TODO
       ((when erp)
        (progn$
         (cw? (normal-output-flag vl)
              "~|CEGen/Error/incremental: assign-value failed (in ~s0).~|" name)
         (cw? (verbose-stats-flag vl)
              "~|CEGen/Stats: Call was (assign-value ~x0 ~x1 ...)~|" x cs%)
         (mv erp nil state)))
        
       ((list a kind updated-H) ans)
       (i (if (eq kind :decision) (1+ i) i))

       (a% (acl2::change a% a% :cs cs% :val a :kind kind :i i))
       
       ((mv erp res state) (propagate x a updated-H C vl state))

       (str (if erp "inconsistent" "consistent"))
       (- (cw? (verbose-stats-flag vl)
               "~%CEgen/Stats/incremental: Propagate ~x0 := ~x1 (i:~x3) was ~s2.~|" x a str i)))

; But do update i in a% always, and partial-A when consistent
   (if erp 
       (value (list  '() ''t '() '() '() '() '() ;is it ok to give back empty alists?
                 (acl2::change a% a% :inconsistent? T)))
     ;else 
     (b* (((list vars~ H~ C~) res)
          (cl~ (clausify-hyps-concl H~ C~))
          ;(name~ (acl2::concatenate 'acl2::string name " incremental " (to-string x) " i=" (to-string i)))
          (type-alist~ (get-acl2-type-alist cl~))
          (tau-interval-alist~ (tau-interval-alist-clause cl~ vars~))
          (- (cw? nil "~% new ta = ~x0 and old ta = ~x1~%" type-alist~ type-alist))
          (- (cw? nil "~% new tau-int-alist = ~x0 and old tau-int-alist = ~x1~%" tau-interval-alist~ tau-interval-alist))
          ((mv partial-A~ elim-bindings~) (if (eq kind :expand)
                                              (mv partial-A (put-val-A x a elim-bindings))
                                            (mv (put-val-A x a partial-A) elim-bindings)))
          )
       

       (value (list H~ C~ vars~ partial-A~ elim-bindings~ type-alist~ tau-interval-alist~
                     (acl2::change a% a%
                                   :inconsistent? NIL)))))))


;mutually tail-recursive incremental (dpll) search prodecure
(defs 
  (incremental-search (a% A. 
                          name  mv-sig-alist ;subgoal params
                          test-outcomes% gcs%
                          vl cgen-state
                          programp
                          ctx state)

; INVARIANTS: 
; - vars has at least 1 variable
; - A. is a stack of consistent a% whose test-outcomes,gcs fields
;   contain the sigma whose values agree with partial-A for
;   the common variables
;   

; - a% is a snapshot. its occurs in 2 stages/forms. in the first stage
;   it stores H,C,vars,partial-A, type-alist,tau-interval-alist
;   and x just after a SELECT.
;   It then gets updated by a consistent assign_propagate call.
;   updated fields: a,kind,i,cs% and inconsistent? flag
;   Finally the test-outcomes and gcs fields simply threaded through and through

; - vars is disjoint with vars of partial-A stored in top of stack A.
    (decl :sig ((a% a%-listp 
                 string  symbol-alist
                 test-outcomes%-p gcs%-p
                 fixnum cgen-state
                 booleanp
                 symbolp state) -> 
                (mv erp (list boolean test-outcomes% gcs%) state))
        :mode :program
        :doc "DPLL like algorithm that searches for a non-vacuous assignment to
the form P (hyps /\ nconcl => nil).  This form returns (mv erp (list stop?
test-outcomes% gcs%) state).  The search consists of a Select, Assign, Propagate
loop.  Any inconsistency in P results in non-chronological backtracking to the
last decision made in Assign. For more details refer to the FMCAD paper.")

; here are abbreviations for functions with looooong arg lists
; dont read them, go directly to the body of the function, refer to these
; abbreviations while reading the main code.
; NOTE: f* names have defun local scope and not across defuns/clique :(

    (f* ((simple-search... () (simple-search name 
                                             H C vars partial-A elim-bindings type-alist tau-interval-alist
                                             mv-sig-alist
                                             test-outcomes% gcs%
                                             vl cgen-state
                                             programp t
                                             ctx state))
         (backtrack... () (backtrack a% A.
                                     name mv-sig-alist
                                     test-outcomes% gcs%
                                     vl cgen-state
                                     programp
                                     ctx state))
         
         (recurse... () (incremental-search a% A.
                                            name mv-sig-alist
                                            test-outcomes% gcs%
                                            vl cgen-state
                                            programp
                                            ctx state)))

      (b* (((mv erp ap-res state) ;snapshot a% moves to second stage/form
            (trans-eval `(assign-propagate ',a% ',name ',(cget sampling-method) ',(cget top-vt-alist) ',vl ',ctx state)
                        ctx state t))
           ((when erp) ;error in assign value
            (prog2$
             (cw? (normal-output-flag vl)
                  "~|CEGen/Error: Aborting incremental search!~|")
             (mv T (list NIL test-outcomes% gcs%) state)))
           ((list H C vars partial-A elim-bindings type-alist tau-interval-alist a%) (cadr (cdr ap-res)))
           
           )
      

;       in
        (if (not (access a% inconsistent?))
           (b* (((mv erp ss-result state) (simple-search...))
                ((when erp) (mv T nil state)) ;give up on error.

                ((list stop? test-outcomes% gcs%) ss-result)
                ((when stop?)
; if we reach stopping condition, simply give up search
                 (mv erp (list stop? test-outcomes% gcs%) state))

                ((when (or (endp vars)
                           (endp (cdr vars)))) 
                 (backtrack...));no luck with :simple, lets backtrack and try again
                 
                (A. (cons a% A.))
; ok lets set up a% for the next iteration
                (x1 (select (cons (cgen-dumb-negate-lit C) H) vl (w state)))

                (a% (acl2::make a% 
                                :vars vars :hyps H :concl C 
                                :partial-A partial-A
                                :elim-bindings elim-bindings
                                :type-alist type-alist
                                :tau-interval-alist tau-interval-alist
                                :inconsistent? nil :cs nil
                                :var x1 :val ''? :kind :na :i 0)))
;           in
            (recurse...))


;      ELSE inconsistent (i.e oops a contradiction found in hyps)
         
         (backtrack...)))))
           
 
; sibling procedure in clique
  (backtrack (a% A. 
                 name mv-sig-alist
                 test-outcomes% gcs%
                 vl cgen-state
                 programp
                 ctx state)
; when called from incremental, either contradiction in hyps[x=a] or simple-search failed on P of zero/one variable
    (decl :sig (( a%-p a%-listp 
                 string variable-alist
                 test-outcomes%-p gcs%-p
                 fixnump cgen-state-p
                 boolean
                 symbol state) 
                -> (mv erp (list boolean test-outcomes% gcs%) state))
         :mode :program
         :doc "backtrack in dpll like search")
   
    (if (or (not (eq (access a% kind) :decision)) ;implied or expand
            (> (access a% i) (cget backtrack-limit)))
        (if (null A.)
;       THEN - error out if x0 exceeds blimit
            (prog2$
             (cw? (verbose-stats-flag vl)
"~|CEGen/Note: Incremental search failed to even satisfy the hypotheses.~|")
            (value (list NIL test-outcomes% gcs%)))
;       ELSE throw away this a%
          (b* ((a% (car A.))
               (x (access a% var))
               (- (cw? (verbose-stats-flag vl)
"~|CEGen/Stats/incremental:  Backtrack to var : ~x0 -- i = ~x1~|" x (access a% i)))) 
           (backtrack a% (cdr A.) ;pop stack
                      name mv-sig-alist
                      test-outcomes% gcs%
                      vl cgen-state
                      programp
                      ctx state)))

;     ELSE a% has a decision which has not reached its backtrack limit
      (incremental-search a% A. 
                          name mv-sig-alist
                          test-outcomes% gcs%
                          vl cgen-state
                          programp
                          ctx state))))



#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

;; Fixer Rules Metadata Table
;; Atomic-Lit -> [{:fixer fixer-name :rule rule}]
;; Ic(F) => (mv-let Out(F) F(In) Lit)

;; Preservation Rules Metadata Table
;; Atomic-Lit -> [{:preserved-by fixer-name :rule rule}]
;; Ic(F) /\ Hyps => L => (mv-let Out(F) F(In) L)


(in-package "CGEN")

(include-book "utilities")
(include-book "misc/bash" :dir :system)
(include-book "data-structures/utilities" :dir :system)
(include-book "cgen-state")

(program)
(set-state-ok t)

(defmacro s+ (&rest args)
  "string/symbol(s) concat to return a symbol.
  :pkg and :separator keyword args recognized."
  `(defdata::s+ ,@args :pkg "CGEN"))

(defmacro g1 (a x)
  `(defdata::get1 ,a ,x))

(defun collect-vars (term)
  (reverse (acl2::all-vars term)))
(defloop collect-vars-lst (terms)
  (for ((term in terms)) (append (collect-vars term))))
  
(defun assoc-equal-lst (keys alist)
  "give back the subset of the alist that correspond to these keys. the order
of the entries is same as of the alist"
  (declare (xargs :guard (and (true-listp keys)
                              (alistp alist))))
  (if (endp alist)
      nil
    (b* (((cons k &) (car alist)))
      (if (member-equal k keys)
          (cons (car alist)
                (assoc-equal-lst keys (cdr alist)))
        (assoc-equal-lst keys (cdr alist))))))

(defun to-string (x)
  (declare (xargs :mode :program))
  (coerce (cdr (coerce (fms-to-string "~x0" (list (cons #\0 x))) 'list)) 'string))

(defun term-name (term)
  (declare (xargs :mode :program))
  (acl2s::fix-intern-in-pkg-of-sym (to-string term) 'cgen::x))

(defun flatten-output-fterm (x term output-vars)
  (cond ((proper-symbolp term) nil)
        ((quotep term) nil)
        ((atom term) nil) ;unreachable?
        (t (and (member-eq x output-vars) ;only flatten if corresponding x is an output
                (list (cons (term-name term) term))))))

(u::defloop flatten-output-fterms (sigma output-vars)
;"abstract away function-applications, corresponding to outputs, with new
;internal variable names. return the a-list"
  (for ((pair in sigma)) (append (flatten-output-fterm (car pair) (cdr pair) output-vars))))
  
(defloop invert-alist (alist)
  (declare (xargs :guard (alistp alist)))
  (for ((x.y in alist)) (collect (cons (cdr x.y) (car x.y)))))

(defun equalitize (cons-pair)
;"convert (s . t) to (equal s t)"
  `(EQUAL ,(car cons-pair) ,(cdr cons-pair)))

(u::defloop equalitize-lst (alst)
  (for ((cons-pair in alst)) (collect (equalitize cons-pair))))

(defun make-dummy-equality-frule-instance (x equal-to-term)
  (b* ((out-vars (list x))
       (in-vars (acl2::all-vars equal-to-term))
       (fixer-term equal-to-term)
       (constraint-term (list 'EQUAL x equal-to-term))
       (nm (s+ "EQ-" (term-name fixer-term) "/" (to-string x)))
       (rule (list (cons :hyps '())
                   (cons :In in-vars)
                   (cons :Out out-vars)
                   (cons :fixer-vars in-vars)
                   (cons :fixer-term fixer-term)
                   (cons :name nm)
                   (cons :constraint-vars (union-eq out-vars in-vars))
                   (cons :constraint-term constraint-term)
                   (cons :fixer-let-binding `((,x ,equal-to-term)))
                   (cons :fixes (list constraint-term `(EQUAL ,equal-to-term ,x)))
                   )))
    (cons nm rule)))

(defloop make-dummy-equality-frule-instances (x-equal-to-term-lst)
  (for ((x-equal-to-term in x-equal-to-term-lst))
       (collect (make-dummy-equality-frule-instance (second x-equal-to-term)
                                                    (third x-equal-to-term)))))


#|

; instantiate-fixer-rules frules{} terms state -> term->f-lits fxri{}
fxri{} is an alist, each entry of which associates a fixer-term to its instance-metadata

Algorithm:

instantiate-fixer-rule/term frule cterm all-terms state _w->term fxri{}
-> (mv hitp f-lits _w->term fxri{} state)
0. cterm1 = reverse subst _w->term on cterm
1. yesp,s-alist=match(Lit(frule),cterm1). if not yesp, return. 
2. For each xi->fterm_i in s-alist, introduce fresh internal vars wi, to make s-alist
a renaming r-alist (modulo xi=constant).
3. collect interval variable equations in E.
4. Instantiate frule with r-alist to get frulei. Carefully update In, Out etc
5. (opt) If E & OutI=fixer-termI are impossible to simultaneously satisfy, return.
6. (bash/test? (implies all-terms hypsI)) does not pass --> return
7. flits = constraint-termI \union E. Also update _w->term
8. for each f-lit in f-lits, put its fixer-termI and its metadata in fxri{}.
9. return (mv t f-lits _w->term fxri{})
|#


(defloop filter-terms-with-vars (terms vars)
  (for ((term in terms))
       (append (and (intersectp-eq (acl2::all-vars term) vars)
                    (list term)))))


(defun fixer-rule-instance (frule alist)
  (b* ((fixer-termI (acl2::sublis-expr alist (get1 :fixer-term frule)))
       (InI         (collect-vars-lst (acl2::sublis-expr-lst alist (get1 :In frule))))
       (OutI        (acl2::sublis-expr-lst alist (get1 :Out frule)))
       (fixer-varsI (union-eq InI OutI))

       (fixer-let-binding (get1 :fixer-let-binding frule))
       (bvalues (strip-cadrs fixer-let-binding))
       (bvars   (strip-cars  fixer-let-binding))
       (bvaluesI (acl2::sublis-expr-lst alist bvalues))
       (bvarsI   (acl2::sublis-expr-lst alist bvars))
       (fixer-let-bindingI (list-up-lists bvarsI bvaluesI))

       ;; (tmp-term (acl2::sublis-expr alist (cons 'dummy-fn (get1 :fixer-let-binding frule))))
       ;; (fixer-let-bindingI (cdr tmp-term))

       (hypsI       (acl2::sublis-expr-lst alist (get1 :hyps frule)))
              
       (constraint-termI (acl2::sublis-expr alist (get1 :constraint-term frule)))
       (constraint-varsI (acl2::all-vars constraint-termI))
       
       ;; now put together the frule instance
       (fruleI frule)
       (fruleI (put-assoc :fixer-term fixer-termI fruleI))
       (fruleI (put-assoc :In InI fruleI))
       (fruleI (put-assoc :Out OutI fruleI))
       (fruleI (put-assoc :fixer-vars fixer-varsI fruleI))
       (fruleI (put-assoc :fixer-let-binding fixer-let-bindingI fruleI))

       (fruleI (put-assoc :hyps hypsI fruleI))
       ;; what about meta-precondition??
       
       (fruleI (put-assoc :constraint-term constraint-termI fruleI))
       (fruleI (put-assoc :constraint-vars constraint-varsI fruleI))

       (fname (s+ (term-name fixer-termI) "/" (to-string OutI)))
       (fruleI (put-assoc :name  fname  fruleI))
       (fruleI (put-assoc :fixes (list constraint-termI) fruleI))
       (fruleI (put-assoc :preserves (filter-terms-with-vars hypsI OutI) fruleI))
       ;;Perhaps also add frule and alist
       
       )
    fruleI))



(defun update-dynamic-fixer-instance-alist/frule (frule1I fxri{}) ; --> fxri{}
  (b* ((ctx 'update-dynamic-fixer-instance-alist/frule)
       (nm (get1 :name frule1I))
       (existing-entry (assoc-equal nm fxri{}))
       ((unless existing-entry) (put-assoc-equal nm frule1I fxri{}))
       (fxri-data (cdr existing-entry))
       ((unless (and (equal (get1 :In fxri-data) (get1 :In frule1I))
                     (equal (get1 :Out fxri-data) (get1 :Out frule1I))
                     (equal (get1 :fixer-term fxri-data) (get1 :fixer-term frule1I))
                     (equal (get1 :fixer-let-binding fxri-data) (get1 :fixer-let-binding frule1I))))
        (er hard? ctx "~| Incompatible fixer rule instances have same key; cannot be merged! ~ 
existing: ~x0 new: ~x1~%" fxri-data frule1I))
       (hyps  (union-equal (get1 :hyps fxri-data) (get1 :hyps frule1I)))
       (fixes (union-equal (get1 :fixes fxri-data) (get1 :fixes frule1I)))
       ;;update hyps and fixes
       (fxri-data (put-assoc-equal :hyps hyps (put-assoc-equal :fixes fixes fxri-data))))
    (put-assoc-equal nm fxri-data fxri{})))

(u::defloop var-term-alistp (xs)
  (for ((x in xs)) (always (and (proper-symbolp (car x))
                                (pseudo-termp   (cdr x))))))

;TODO
(defun dumb-unsolvable-equations-p (equalities mod-vars) ;-> boolean
  (declare (ignorable equalities mod-vars))
  nil)

(defun bash-fn (query hints verbosep ctx state)
  (b* ((ohints (acl2::override-hints (w state)))
       ((er ?ign) (acl2::table-fn 'ACL2::DEFAULT-HINTS-TABLE
                                  (list :OVERRIDE 'nil) state nil))
       ((mv erp res state) (acl2::bash-fn query hints verbosep ctx state))
       ((er ?ign) (acl2::table-fn 'ACL2::DEFAULT-HINTS-TABLE
                                  (list :OVERRIDE (kwote ohints)) state nil)))
    (mv erp res state)))

(defun equation-p (term)
  (and (consp term)
       (= (len term) 3)
       (equal (car term) 'EQUAL)
       (or (variablep (second term))
           (variablep (third term)))))

(defun valid-output-symbols (xs)
  (and (proper-symbol-listp xs)
       (no-duplicatesp xs)))

(defun instantiate-fixer-rule/term (frule cterm all-terms allvars vl state W{} fxri{})
  (declare (xargs :guard (and ;(fixer-rule-p frule)
                              (pseudo-termp cterm) ;constraint term
                              (pseudo-term-listp all-terms)
                              (proper-symbol-listp allvars)
                              (var-term-alistp W{}) ;W{internal variable} -> term
                              (alistp fxri{}) ;fxri{fixer-term-name} -> fixer-metadata
                              )))
  ;returns (mv erp (list hitp f-lits W{} fxri{}) state)
  (b* ((ctx 'instantiate-fixer-rule/term)
       (cterm1 (acl2::sublis-expr (invert-alist W{}) cterm))
       ((mv yesp s-alist) (acl2::one-way-unify (get1 :constraint-term frule) cterm1))
       ((unless yesp) (value (list nil '() W{} fxri{})))
       

       ;; check that meta-precondition is satisfied
       (meta-precondition (get1 :meta-precondition frule))
       (letb (acl2::listlis (strip-cars s-alist) (acl2::kwote-lst (strip-cdrs s-alist))))
       ((mv erp okp) (if (equal meta-precondition 't)
                         (mv nil t)
                       (trans-my-ev-w `(LET ,letb
                                            (declare (ignorable ,@(strip-cars s-alist)))
                                            ,meta-precondition)
                                    ctx (w state) nil)))
       ((unless (and (not erp) okp)) (value (list nil '() W{} fxri{})))


       
       (W1{} (flatten-output-fterms s-alist (get1 :Out frule)))
       ;; ((when (intersectp-eq (strip-cars W1{}) (acl2::all-vars1-lst all-terms '())))
       ;;  (er soft ctx "~| New internal variables name collision!"))

;r-alist is a renaming subst, except perhaps for equality terms
       (r-alist (pairlis$ (strip-cars s-alist)
                          (acl2::sublis-expr-lst (invert-alist W1{})
                                                 (strip-cdrs s-alist))))
       ((unless (valid-output-symbols (acl2::sublis-expr-lst r-alist (get1 :Out frule))))
        (value (list nil '() W{} fxri{})))
       
       (fruleI (fixer-rule-instance frule r-alist))

       ;;get equations for all internal variables
       (E (equalitize-lst (append W1{} (assoc-equal-lst (acl2::all-vars cterm1) W{}))))
       (unlikely-p (dumb-unsolvable-equations-p E (get1 :Out fruleI)))
       ((when unlikely-p)
        (prog2$
         (cw? (verbose-flag vl) "~| Cgen/Note: ~x0 with fixed ~x1 is unlikely to be simultaneously satisfied!~%" E (get1 :Out fruleI))
         (value (list nil '() W{} fxri{}))))

       (curr-vars (union-eq (strip-cars W1{})
                            (union-eq (strip-cars W{})
                                      allvars)))
       (rule-hyps (filter-terms-with-vars (get1 :hyps fruleI)
                                          ;;major bugfix [2016-09-09 Fri]
                                          curr-vars))

       ;TODO: rename to avoid variable capture
       (backchain-lits (set-difference-equal (get1 :hyps fruleI) rule-hyps))
       ;;major bugfix [2016-09-09 Fri] add E to the assumption context
       (relieve-hyps-query `(IMPLIES (AND ,@all-terms ,@E) (AND . ,rule-hyps)))
       ;; (cgen-state (cgen::make-cgen-state-fn test-form
       ;;                                       '(:testing-enabled :naive)
       ;;                                       (w state)))
       ;; NOT POSSIBLE -- since it is circular usage
       ;; ((mv res ?cgen-state state) 
       ;;  (with-time-limit (cget cgen-timeout)
       ;;                    (prove/cgen test-form nil cgen-state state)))
       (hints '())
       ((mv erp res state) (cgen::bash-fn relieve-hyps-query hints (debug-flag vl) ctx state))
       ((unless (and (not erp) (eq res nil)))
        (prog2$
         (cw? (verbose-flag vl) "~| Cgen/Note: Unable to relieve query ~x0! Skipping fixer rule ..~%" relieve-hyps-query)
         (value (list nil '() W{} fxri{}))))
       (f-lits (cons (get1 :constraint-term fruleI) (union-equal backchain-lits E)))
       (W{} (union-equal W{} W1{}))
       (fxri{} (update-dynamic-fixer-instance-alist/frule fruleI fxri{}))
       ;; The following is already taken care of in instantiate-fixer-rules/terms-iter
       ;;(fxri{} (union-equal (make-dummy-equality-frule-instances E) fxri{}))
       )
    (value (list t f-lits W{} fxri{}))))
        
                      

(defun instantiate-fixer-rules/term (frules cterm all-terms allvars vl state flits{} W{} fxri{})
  (declare (xargs :guard (and ;(fixer-rules-p frules)
                              (pseudo-termp cterm) ;constraint term
                              (pseudo-term-listp all-terms)
                              (alistp flits{})
                              (var-term-alistp W{}) ;W{internal variable} -> term
                              (alistp fxri{})
                              )))
;returns (mv erp (list flits{} W{} fxri{}) state)
  (b* (((when (endp frules)) (value (list flits{} W{} fxri{})))
       (frule (car frules))
       ((mv erp (list hitp flits W{} fxri{}) state)
        (instantiate-fixer-rule/term frule cterm all-terms allvars vl state W{} fxri{}))
       ((when (or erp (not hitp)))
        (instantiate-fixer-rules/term (cdr frules) cterm all-terms allvars vl state flits{} W{} fxri{}))
       (fname hitp) ;;overload: hitp stores the name of the "hit" fixer rule instance.
       (flits{} (put-assoc-equal fname flits flits{})))
    (instantiate-fixer-rules/term (cdr frules) cterm all-terms allvars vl state flits{} W{} fxri{})))

#|
1. Flatten: R(g x)y matches with Rx1x2 of fixer rule to get s-alist x1->gx, x2->y
   3 cases: x1->fterm, x1->var, x1->constant
2. add gx=w1, to obtain Rw1y and w1=gx and then the s-alist is x1->w1, x2->y and furthur
bring in fixer-rule variant for w1=gx literal. So F1 fixes Rw1y and G1 fixes w1=gx
and both together fix R(g x)y. So now there is a conjunction too when determining
satisfiability of a term, in addition to a disjunction.
say term
i.e.
SAT(f-lit) == \/ F_i**f-lit
SAT(f-lits) == /\ SAT(f-lit_i)
SAT(term) == \/ SAT(f-lits_i)
|#


(defun instantiate-fixer-rules/terms (cterms frules all-terms allvars vl state term->flits{} new-lits W{} fxri{})
;return (mv erp (list term->flits{} W{} fxri{}) state)
; term->flits{} is an alist from each cterm to a list of f-lits
; this list structure corresponds to DNF form, i.e., a sum of products
  (b* (((when (endp cterms)) (value (list term->flits{} new-lits W{} fxri{})))
       (cterm (car cterms))
       ((mv erp (list flits{} W{} fxri{}) state)
        (instantiate-fixer-rules/term frules cterm all-terms allvars vl state '() W{} fxri{}))
       ((when (or erp (null flits{})))
        (prog2$
         (cw? (verbose-stats-flag vl) "~| Cgen/Note: No applicable fixer-rule found for ~x0.~%" cterm)
         (instantiate-fixer-rules/terms (cdr cterms) frules all-terms allvars vl state
                                        (put-assoc-equal cterm nil term->flits{})
                                        new-lits W{} fxri{})))
       (new-lits1 (set-difference-equal (union-lsts (strip-cdrs flits{})) all-terms))
       (new-lits  (union-equal new-lits new-lits1))
       (term->flits{} (put-assoc-equal cterm flits{} term->flits{})))
    (instantiate-fixer-rules/terms (cdr cterms) frules all-terms allvars vl state
                                   term->flits{} new-lits W{} fxri{})))


(include-book "infer-enum-shape")
(defloop access-cs%-alst (x-cs%-alst)
  (for ((x-cs% in x-cs%-alst))
       (collect (acl2::access cs% (cdr x-cs%) :defdata-type))))


(defun make-type-and-eq-hyp (x defdata-type eq-constraint defdata::wrld)
  (b* ((P (defdata::predicate-name defdata-type))
       ((when (eq eq-constraint 'defdata::empty-eq-constraint))
        (list P x)))
    (list 'EQUAL x eq-constraint)))

(defloop make-type-and-eq-hyps (v-cs%-alst defdata::wrld)
  (for ((v--cs% in v-cs%-alst))
       (collect (make-type-and-eq-hyp (car v--cs%)
                                      (acl2::access cs% (cdr v--cs%) :defdata-type)
                                      (acl2::access cs% (cdr v--cs%) :eq-constraint)
                                      defdata::wrld))))

(defun make-dummy-defdata-type-frule-instance (x P defdata::wrld)
  (b* ((defdata-type (or (defdata::is-type-predicate P defdata::wrld)
                         'ACL2S::ALL))
       (E (defdata::enumerator-name defdata-type))
       (vars (list x))
       (fixer-term (list E))
       (constraint-term (cons P vars))
       (nm (s+  (term-name fixer-term) "/" (to-string x)))
       (rule (list (cons :hyps '())
                   (cons :In '())
                   (cons :Out vars)
                   (cons :fixer-vars vars)
                   (cons :fixer-term fixer-term)
                   (cons :name nm)
                   (cons :constraint-vars vars)
                   (cons :constraint-term constraint-term)
                   (cons :fixer-let-binding `((,x (,E))))
                   (cons :fixes (list constraint-term))
                   )))
    (cons nm rule)))



;; (defun make-dummy-cgen-builtin-fxri-entry (v--cs% defdata::wrld)
;;   (b* (((cons x cs%) v--cs%)
;;        (equal-to-term (acl2::access cs% cs% :eq-constraint))
;;        ((when (not (equal 'defdata::empty-eq-constraint equal-to-term)))
;;         (make-dummy-equality-frule-instance x equal-to-term))
;;        (defdata-type (acl2::access cs% cs% :defdata-type)))
;;     (make-dummy-defdata-type-frule-instance x defdata-type defdata::wrld)))
  

(defun destruct-equality-hyp (hyp)
  (case-match hyp
    (('EQUAL x (f . args)) (list x (acl2::cons-term f args)))
    (('EQUAL (f . args) x) (list x (acl2::cons-term f args)))
    (('EQUAL x y) (list x y))))

(defun make-dummy-cgen-builtin-fxri-entry (type-hyp defdata::wrld)
  (if (equal (len type-hyp) 2) ;type predicate
      (make-dummy-defdata-type-frule-instance (cadr type-hyp) (car type-hyp) defdata::wrld)
    (b* (((list x equal-to-term) (destruct-equality-hyp type-hyp)))
      (make-dummy-equality-frule-instance x equal-to-term))))



(defloop make-dummy-cgen-builtin-frule-instances (type-hyps defdata::wrld)
  (for ((type-hyp in type-hyps))
       (collect (make-dummy-cgen-builtin-fxri-entry type-hyp defdata::wrld))))

(defloop two-level-flatten1 (lits-lst-list)
  (for ((lits-lst in lits-lst-list))
       (append (union-lsts lits-lst))))

(defun two-level-flatten (lits-lst-list)
  (remove-duplicates-equal (two-level-flatten1 lits-lst-list)))

(defloop singletonize (xs)
  ;"convert (x1 x2 ... xn) to ((x1) (x2) (x3) ... (xn))"
  (for ((x in xs)) (collect (list x))))

(defloop make-allp-hyps (xs)
  (for ((x in xs)) (collect (list 'ACL2S::ALLP x))))

(defun is-type-hyp (term wrld)
  (or (defdata::is-type-predicate (car term) wrld)
      (and (equal (len term) 3)
           (equal (car term) 'EQUAL)
           (or (proper-symbolp (second term))
               (proper-symbolp (third term))))))

(defloop filter-type-hyps (terms wrld)
  (for ((term in terms))
       (append (and (consp term) (is-type-hyp term wrld)
                    (list term)))))


(defloop make-dummy-term-flits-alist (terms fnames)
  (for ((term in terms) (fname in fnames))
       (collect (cons term (acons fname (list term) nil)))))

(defun instantiate-fixer-rules/terms-iter (hyps frules vl state term->flits{} W{} all-hyps fxri{})
;fixed-point iteration of above function
  (b* ((wrld (w state))
       ;; (v-cs%-alst (collect-constraints% hyps (acl2::all-vars1-lst hyps '())
       ;;                                   type-alist '() vl wrld))
       ;; (type-hyps  (remove-duplicates-equal (make-type-and-eq-hyps v-cs%-alst wrld)))
       (type-hyps (filter-type-hyps hyps wrld))
       (type-vars (acl2::all-vars1-lst type-hyps '()))
       (notype-vars (set-difference-equal (acl2::all-vars1-lst hyps '()) type-vars))
       (allp-hyps (make-allp-hyps notype-vars))
       (type-hyps (append type-hyps allp-hyps))

       (fxri0{} (make-dummy-cgen-builtin-frule-instances type-hyps wrld))
       (term->flits0{} (make-dummy-term-flits-alist type-hyps (strip-cars fxri0{})))
       (term->flits{} (union-equal term->flits0{} term->flits{}))
       (fxri{} (union-equal fxri0{} fxri{}))
       
       (other-hyps (set-difference-equal hyps type-hyps))
       ((when (null other-hyps))
        (value (list term->flits{} W{} all-hyps fxri{})))

       (- (cw? (debug-flag vl) "~| type-hyps: ~x0 and hyps: ~x1~%" type-hyps hyps))

       (allvars (acl2::all-vars1-lst all-hyps '()))

       ((mv ?erp (list term->flits1{} new-lits W1{} fxri1{}) state) ;drop erp TODO
        (instantiate-fixer-rules/terms other-hyps frules all-hyps allvars vl state '() '() '() '()))

       (term->flits{} (append term->flits1{} term->flits{}))
       (W{} (union-equal W1{} W{}))
       (fxri{} (union-equal fxri1{} fxri{}))

       ;;(E (equalitize-lst W1{}))
       (all-hyps (union-equal new-lits all-hyps))
       
       ((when (null new-lits)) ;no new internal equations or new hyps (backchaining)
        (value (list term->flits{} W{} all-hyps fxri{})))

       )
       
    (instantiate-fixer-rules/terms-iter new-lits frules vl state term->flits{} W{} all-hyps fxri{})))







#|
In the second pass, we dont worry about cterms, we only look at f-lits .
Note that a prule has a single f-lit to match, but multiple fixer-terms to complete
the matching.




[2016-03-25 Fri]
Algo:
instantiate-pres-rule prule f-lit fxri{} state -> fxri{}
1. (yesp s-alist) = match(Lit(prule),f-lit). if not yesp, return
2. fterms-partially-I = (sublis-var-lst s-alist fixer-terms(prule))
3. S-list-lst = get all possible matches for each fterms-pI
4. Take cross-product to get S-list-lst, i.e get all possible substitutions
5. For each possible prule-instance, check if hyps are relieved. update fxri{}
6. return fxri{}
|#

(defun match-pat/terms (pat terms)
  (if (endp terms)
      '()
    (b* (((mv yesp sigma) (acl2::one-way-unify pat (car terms)))
         ((unless yesp) (match-pat/terms pat (cdr terms))))
      (cons sigma (match-pat/terms pat (cdr terms))))))
         
(defun match-pats/terms-alst (pats terms ans)
  (if (endp pats)
      ans
    (match-pats/terms-alst (cdr pats) terms
                           (cons (match-pat/terms (car pats) terms) ans))))
    


(defun binary-merge-sigma (sigma1 sigma2)
  (if (endp sigma1)
      (mv nil sigma2)
    (b* (((cons x val) (car sigma1))
         ((unless (equal (assoc-eq x sigma2) (car sigma1)))
          (mv t nil)) ;return error if x has diff val under sigma1 and sigma2
         )
      (binary-merge-sigma (cdr sigma1) (put-assoc-eq x val sigma2)))))

(defun merge-sigmas1 (sigmas ans)
  (if (endp sigmas)
      (mv nil ans)
    (b* ((sigma (car sigmas))
         ((mv erp ans) (binary-merge-sigma sigma ans))
         ((when erp) (mv t nil))
         )
      (merge-sigmas1 (cdr sigmas) ans))))

(defun preservation-rule-instance (prule alist)
  (b* ((fixer-termsI (acl2::sublis-expr-lst alist (get1 :fixer-terms prule)))
       (OutI         (acl2::sublis-expr-lst alist (get1 :Out prule)))

       (fixer-let-binding (get1 :fixer-let-binding prule))
       (bvalues (strip-cadrs fixer-let-binding))
       (bvars   (strip-cars  fixer-let-binding))
       (bvaluesI (acl2::sublis-expr-lst alist bvalues))
       (bvarsI   (acl2::sublis-expr-lst alist bvars))
       (fixer-let-bindingI (list-up-lists bvarsI bvaluesI))
       ;; (tmp-term (acl2::sublis-expr alist (cons 'dummy-fn (get1 :fixer-let-binding prule))))
       ;; (fixer-let-bindingI (cdr tmp-term))

       (hypsI       (acl2::sublis-expr-lst alist (get1 :hyps prule)))
              
       (constraint-termI (acl2::sublis-expr alist (get1 :constraint-term prule)))
       (constraint-varsI (acl2::all-vars constraint-termI))
       
       ;; now put together the prule instance
       (pruleI prule)
       ;; note: there is a 1:1 corr between Out and fixer-terms; fixer-let-binding is that.
       (pruleI (put-assoc :fixer-terms fixer-termsI pruleI))
       (pruleI (put-assoc :Out OutI pruleI))
       (pruleI (put-assoc :fixer-let-binding fixer-let-bindingI pruleI))

       (pruleI (put-assoc :hyps hypsI pruleI))
       ;; what about meta-precondition??
       
       (pruleI (put-assoc :constraint-term constraint-termI pruleI))
       (pruleI (put-assoc :constraint-vars constraint-varsI pruleI))

       
       (pruleI (put-assoc :preserves (list constraint-termI) pruleI))
       ;;Perhaps also add prule and alist
       
       )
    pruleI))


(defun find-fxri-rule1 (fxr-term entry)
  (b* (((cons & rulei) entry))
    (and (or (equal fxr-term (get1 :fixer-term rulei))
             (member-equal fxr-term (strip-cadrs (get1 :fixer-let-binding rulei))))
         entry)))

(defloop find-fxri-rule (fxr-term fxri{})
  (for ((entry in fxri{}))
       (thereis (find-fxri-rule1 fxr-term entry))))


(defun update-dynamic-fixer-instance-alist/prule/fxr-term (fxr-term pruleI vl fxri{})
  (b* ((ctx 'update-dynamic-fixer-instance-alist/prule/fxr-term)
       ((cons nm fxri-data) (find-fxri-rule fxr-term fxri{}))
       ((unless fxri-data)
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Verbose: ~x0 not in fxri{}, skip prule update.~%" fxr-term ctx)
         fxri{}))
       ;;preserves is a list of constraint-terms
       (preserves (union-equal (get1 :preserves fxri-data) (get1 :preserves pruleI)))
       ;;prule-alist is an alist associating a preserved constraint term with its prule instance
       (prule-alist (put-assoc-equal (get1 :constraint-term pruleI) pruleI
                                     (get1 :prule-alist fxri-data)))
       
       (fxri-data (put-assoc-equal :preserves preserves
                                   (put-assoc-equal :prule-alist prule-alist fxri-data))))
    (put-assoc-equal nm fxri-data fxri{})))

(defun update-dynamic-fixer-instance-alist/prule/fxr-terms (fxr-terms pruleI vl fxri{})
  (if (endp fxr-terms)
      fxri{}
    (b* ((fxr-term (car fxr-terms))
         (fxri{} (update-dynamic-fixer-instance-alist/prule/fxr-term fxr-term pruleI vl fxri{})))
      (update-dynamic-fixer-instance-alist/prule/fxr-terms (cdr fxr-terms) pruleI vl fxri{}))))
    

(defun update-dynamic-fixer-instance-alist/prule (pruleI vl fxri{}) ; --> fxri{}
  (update-dynamic-fixer-instance-alist/prule/fxr-terms (get1 :fixer-terms pruleI) pruleI vl fxri{}))
  

(defun instantiate-prule/multiple-subst (sigmas-lst partial-S prule all-terms vl ctx state fxri{})
  ;iterate over fxterm{sigma} list
  (b* (((when (endp sigmas-lst)) (value fxri{}))
       (sigmas (car sigmas-lst))
       ((mv erp S1) (merge-sigmas1 (cdr sigmas) (car sigmas)))
       ((when erp)
        ;;sigmas could not be merged, ignore this prule instance
        (prog2$
         (cw? (verbose-flag vl) "~| Cgen/Error: ~x0 cannot be merged into one substitution. ~ Skipping this preservation rule instance ..~%" sigmas)
         (value fxri{})))
       (S (append partial-S S1)) ;partial-S and S1 are "disjoint", so append is fine!!
       ((unless (valid-output-symbols (acl2::sublis-expr-lst S (get1 :Out prule))))
        (value fxri{}))
       (pruleI (preservation-rule-instance prule S))
       (query `(IMPLIES (AND ,@all-terms) (AND . ,(get1 :hyps pruleI))))
       (hints '())
       ((mv erp res state) (cgen::bash-fn query hints (debug-flag vl) ctx state))
       ((unless (and (not erp) (eq res nil)))
        (prog2$
         (cw? (verbose-flag vl) "~| Cgen/Note: Unable to relieve query ~x0! Skipping preservation rule ..~%" query)
         (value fxri{})))
       (fxri{} (update-dynamic-fixer-instance-alist/prule pruleI vl fxri{})))
    (instantiate-prule/multiple-subst (cdr sigmas-lst) partial-S prule all-terms vl ctx state fxri{})))

(defloop singletonize (xs)
  ;"convert (x1 x2 ... xn) to ((x1) (x2) (x3) ... (xn))"
  (for ((x in xs)) (collect (list x))))

(defloop cross-product/binary1 (a A2)
  (for ((b in A2)) 
       (collect (list a b))))

(defloop cross-product/binary (A1 A2)
  (for ((a in A1))
       (append (cross-product/binary1 a A2))))
  
; (cross-product/binary A1 '()) == (cross-product/binary '() A1) == NULL != (singletonize A1)
  
(defun generate-all-tuples (A-list)
  "Given Lists A1,A2,...,An generate all n-tuples (a1,...,an) where ai \in Ai"
  (if (endp A-list)
      '()
    (if (endp (cdr A-list))
        (singletonize (car A-list))
        (if (endp (cddr A-list))
          (cross-product/binary (car A-list) (cadr A-list))
          (cross-product/binary (car A-list)
                                (generate-all-tuples (cdr A-list)))))))

(defloop assoc-alists (key alists)
  (for ((alist in alists))
       (append (and (assoc-equal key alist)
                    (list (cdr (assoc-equal key alist)))))))


(defun instantiate-pres-rule/lit (prule f-lit all-terms all-fxr-term-instances vl state fxri{})
  (declare (xargs :guard (and ;(preservation-rule-p prule)
                              (pseudo-termp f-lit)
                              (alistp fxri{}) ;fxri{fixer-term-name} -> fixer-metadata
                              )))
;return (mv erp fxri{} state)
  (b* ((ctx 'instantiate-pres-rule)
       ((mv yesp partial-S) (acl2::one-way-unify (get1 :constraint-term prule) f-lit))
       ((unless yesp) (value fxri{})) ;no hit
       ;;get partially instantiated fixer-terms for this prule
       (fxr-terms-pI (acl2::sublis-var-lst partial-S (get1 :fixer-terms prule)))
;       (- (cw "prule : ~x0~%" prule))
;       (- (cw "partial-S : ~x0  fxr-terms-pI : ~x1~%" partial-S fxr-terms-pI))
       ;;Now lets get all possible matching substitution lists
       (sigma-list-lst (match-pats/terms-alst fxr-terms-pI all-fxr-term-instances '()))
       
       (sigmas-lst (generate-all-tuples sigma-list-lst))
;       (- (cw "S-lst-lst : ~x0 and S-lst : ~x1~%" sigma-list-lst sigmas-lst))
       )
    (instantiate-prule/multiple-subst sigmas-lst partial-S prule all-terms vl ctx state fxri{})))
       


(defun instantiate-pres-rule/lits (prule f-lits all-terms all-fxr-term-instances vl state fxri{}); -> fxri{}
;loop over f-lits
  (declare (xargs :guard (and ;(preservation-rule-p prule)
                              (pseudo-term-listp f-lits)
                              (pseudo-term-listp all-terms)
                              (alistp fxri{})
                              )))
  (if (endp f-lits)
      (value fxri{})
    (b* ((f-lit (car f-lits))
         ((er fxri{}) (instantiate-pres-rule/lit prule f-lit all-terms all-fxr-term-instances vl state fxri{}))
         )
      (instantiate-pres-rule/lits prule (cdr f-lits) all-terms all-fxr-term-instances vl state fxri{}))))


;; (defun strip-mv-nth (term)
;;   (case-match term
;;     (('MV-NTH & exp) exp)
;;     (& term)))

;; (defloop strip-mv-nth-lst (terms)
;;   (for ((term in terms)) (collect (strip-mv-nth term))))

;; [2016-09-10 Sat] Bugfix Take fixers as they were introduced in fixer
;; rules. Do not treat multi-output fixers as multiple single-output fixers

;; (defun get-all-fixer-terms1 (fxri{} ans)
;;   (if (endp fxri{})
;;       ans
;;     (b* ((rulei{} (cdr (car fxri{})))
;;          (fixer-letb (get1 :fixer-let-binding rulei{}))
;;          (fixer-terms1 (strip-cadrs fixer-letb)))
;;       (get-all-fixer-terms1 (cdr fxri{}) (union-equal ans fixer-terms1)))))

(defun get-all-fixer-terms1 (fxri{} ans)
  (if (endp fxri{})
      ans
    (b* ((rulei{} (cdr (car fxri{})))
         (fxr (get1 :fixer-term rulei{})))
      (get-all-fixer-terms1 (cdr fxri{}) (add-to-set-equal fxr ans)))))




(defun instantiate-pres-rules (prules f-lits all-terms vl state fxri{}); -> fxri{}
;  loop over prules
  (if (endp prules)
      (value fxri{})
    (b* ((prule (car prules))
         (all-fxr-term-instances (get-all-fixer-terms1 fxri{} '()))
         ((er fxri{}) (instantiate-pres-rule/lits prule f-lits
                                                  all-terms all-fxr-term-instances
                                                  vl state fxri{}))
         )
      (instantiate-pres-rules (cdr prules) f-lits all-terms vl state fxri{}))))
  


#|
Issues to consider: [2016-03-24 Thu]
1. Is this local? i.e if i take care of one term with its matching
frules and prules, will it not affect other term matches.
1.1 If two terms having a common subterm are flattened differently
1.2 If one term with two fixer rule matches that have a different flattening.

2. If one term breaks into multiple f-lits, how to count #sat?

3. If we see clearly that (R (g x) (f x)) cannot be "fixed" then just
say no, or go on to generate (R w1 w2), w1=gx, w2=fx and let the
backend decide its unsolvability.

4. How to think of correctness?? what is a spec for this function?
fixer-rule-instances are instances of fixer-rules
terms \equivalent \E w_i f-lits
prule-instances are instances of prules


5. Should we do degrees of freedom propagation and then for the
remaining clique call the SAT backend?

6. How then to instantiate prules? Will it affect the previous frule instantiation?

7. Need to natively support equalities and type-hyps (enums), or
should we completely be general?
|#

(defun remove-internal-vars/equations (D W{}) ;D is a doubleton-listp
  (declare (xargs :guard (alistp D)))
  (if (endp D)
      '()
    (if (member-equal (cons (caar D) (cadr (car D))) W{})
        (remove-internal-vars/equations (cdr D) W{})
      (b* (((list var e) (car D))
           (e~ (acl2::sublis-var W{} e)))
        (if (equal var e~)
            (remove-internal-vars/equations (cdr D) W{})
          (cons (list var e~)
                (remove-internal-vars/equations (cdr D) W{})))))))



(defun remove-intersecting-members-lst (flits{} remove-list)
  (if (endp flits{})
      '()
    (if (intersectp (cdr (car flits{})) remove-list)
        (remove-intersecting-members-lst (cdr flits{}) remove-list)
      (cons (car flits{})
            (remove-intersecting-members-lst (cdr flits{}) remove-list)))))

(defun remove-unfixable-lits (term->flits{} u-lits)
  (if (endp term->flits{})
      '()
    (b* (((cons term flits{}) (car term->flits{}))
         (flits1{} (remove-intersecting-members-lst flits{} u-lits)))
      (cons (cons term flits1{})
            (remove-unfixable-lits (cdr term->flits{}) u-lits)))))


(defun remove-unfixable-constraints (term->flits{} vl)
  (declare (xargs :mode :program))
  (b* ((unfixble-terms (get-all-keys nil term->flits{}))
       ((when (null unfixble-terms)) term->flits{})
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Note: Unfixable constraints: ~x0~%" unfixble-terms))
       (all-terms (strip-cars term->flits{}))
       (fixble-terms (set-difference-equal all-terms unfixble-terms))
       (term->flits{} (assoc-equal-lst fixble-terms term->flits{}))
       (term->flits{} (remove-unfixable-lits term->flits{} unfixble-terms)))
    (remove-unfixable-constraints term->flits{} vl)))

(defun fixer-rules-table (wrld)
  (table-alist 'FIXER-RULES-TABLE wrld))

(defun preservation-rules-table (wrld)
  (table-alist 'PRESERVATION-RULES-TABLE wrld))

         

(defloop collect-flits0 (flits{})
  (for ((fname--flits in flits{}))
       (append (cdr fname--flits))))

(defloop collect-flits (term->flits{})
  (for ((term--flits{} in term->flits{}))
       (append (collect-flits0 (cdr term--flits{})))))
  

(defun fixer-arrangement1 (terms all-terms vl ctx state)
; returns (mv erp (cons let*-soln-binding unsat-terms) state)
; unsat-terms are a subset of terms. they exclude type-hyps and
; those terms that have no applicable fixer rules.
; these terms were unsat, because the preservation rules did not work out
         
  (b* ((wrld (w state))
       (frules (strip-cdrs (fixer-rules-table wrld)))
       (prules (strip-cdrs (preservation-rules-table wrld)))
       ((mv ?erp1 (list term->flits{} ?W{} all-terms~ fxri{}) state)
        (instantiate-fixer-rules/terms-iter terms frules vl state
                                            '() '() all-terms '()))

       (term->flits{} (remove-unfixable-constraints term->flits{} vl))

       (flits (collect-flits term->flits{}))

       ((mv ?erp2 fxri{} state)
        (instantiate-pres-rules prules flits all-terms~ vl state fxri{}))
       ((when (or erp1 erp2))
        (er soft ctx "~| Cgen/Error in instantiation of fixer or preservation rules!~%"))
       ;; (?litWt{} (pairlis$ flits
       ;;                    (make-list (length flits) :initial-element 1)))

       (type-hyps  (filter-type-hyps terms wrld))
       (non-type-hyps (set-difference-equal terms type-hyps))
; [2016-05-04 Wed] Only count the SAT of non-type-hyps
; But discard those hyps that have no entry in the term->flits-lst
       (fixable-terms (strip-cars term->flits{}))
       (relevant-terms (intersection-equal non-type-hyps fixable-terms))

       ((er (list let*-soln0 rterms/true))
        (fxri-let*-soln flits term->flits{} relevant-terms fxri{} vl state))
       
       (rterms/false (set-difference-equal relevant-terms rterms/true))
       (let*-soln (remove-internal-vars/equations let*-soln0 W{}))
       ;(b*-soln (to-b*-mv-binding let*-soln))
       ;(let*-soln (assoc-equal-lst vars let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixer-bindings: ~x0~%" let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixed terms: ~x0~%" rterms/true))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Unsat fixable terms: ~x0~%" rterms/false))
       ;; TODO check that this let* binding is sound/correct, i.e., it
       ;; satisfies all the hyps under fixer and pres rules.

; [2016-09-05 Mon]
; Add code to extract backchaining hypotheses
       (new-hyps0 (set-difference-equal all-terms~ (equalitize-lst W{})))
       (new-hyps1 (remove-duplicates-equal (acl2::sublis-var-lst W{} new-hyps0)))
       (new-hyps  (set-difference-equal new-hyps1 all-terms))
       )
    (value (list let*-soln new-hyps rterms/false))))



; Added [2016-08-12]
(defun fixer-arrangement1-lst (terms-lst all-terms vl ctx state)
  ; iterative version of fixer-arrangement1. Ignores error
  (if (endp terms-lst)
      (value (list nil nil nil))
    (b* (((mv erp res1 state) (fixer-arrangement1 (car terms-lst) all-terms vl ctx state))
         ((when erp) (fixer-arrangement1-lst (cdr terms-lst) all-terms vl ctx state)) ;ignore error
         ((list B1 new-hyps1 unsat-hyps1) res1)
         ((mv ?erp (list B2 new-hyps2 unsat-hyps2) state)
          (fixer-arrangement1-lst (cdr terms-lst) all-terms vl ctx state)))
      (value (list (append B1 B2)
                   (union-equal new-hyps1 new-hyps2)
                   (union-equal unsat-hyps1 unsat-hyps2))))))

(logic)

(defun rassoc-dlist (v dlist)
  (if (endp dlist)
      nil
    (if (equal (cadr (car dlist)) v)
        (car dlist)
      (rassoc-dlist v (cdr dlist)))))

(defun put-rassoc-dlist (v key dlist)
;update key -> v entry in doubleton list by value; if v not found, put at end
  (if (endp dlist)
      (list (list key v))
    (if (equal (cadr (car dlist)) v)
        (cons (list key v) (cdr dlist))
      (cons (car dlist) (put-rassoc-dlist v key (cdr dlist))))))
            
(defun update-mv-binding (x i arity mv-term B)
  (b* ((entry (rassoc-dlist mv-term B))
       ((unless (consp entry))
        (cons (list (cons 'MV (update-nth i x (make-list arity :initial-element '&))) mv-term) B))
       ((list mv-vars &) entry)
       (mv-vars~ (update-nth (1+ i) x mv-vars))
       (B (put-rassoc-dlist mv-term mv-vars~ B))
       (x-val `(MV-NTH (QUOTE ,i) (MV-LIST (QUOTE ,arity) ,mv-term)))
       (B (list-up-lists (strip-cars B)
                         (acl2::sublis-var-lst (list (cons x-val x)) (strip-cadrs B)))))
    B))
    
  
(defun to-b*-mv-binding1 (letB ans)
  (if (endp letB)
      (reverse ans) ;keep original order
    (b* (((list var e) (car letB))
         ((unless (and (consp e) (equal (car e) 'MV-NTH)))
          (to-b*-mv-binding1 (cdr letB) (cons (car letB) ans)))
         (`(MV-NTH (QUOTE ,index) (MV-LIST (QUOTE ,arity) ,mv-term)) e))
      (to-b*-mv-binding1 (cdr letB) (update-mv-binding var index arity mv-term ans)))))
         
(defun to-b*-mv-binding (letB)
  (to-b*-mv-binding1 letB '()))

(defun inverse-subst/b*-mv-entry (vars i arity exp)
  (if (endp vars)
      '()
    (if (not (equal (car vars) '&))
        (cons (cons `(MV-NTH (QUOTE ,i) (MV-LIST (QUOTE ,arity) ,exp)) (car vars))
              (inverse-subst/b*-mv-entry (cdr vars) (1+ i) arity exp))
      (inverse-subst/b*-mv-entry (cdr vars) (1+ i) arity exp))))

(defun inverse-subst/b*-entry (key exp)
  (if (atom key)
      (list (cons exp key))
    (if (eq (car key) 'MV)
        (inverse-subst/b*-mv-entry (cdr key) 0 (len (cdr key)) exp)
      ;; only MV supported
      nil)))
(defun alist-suffix-starting-with (key B)
  (declare (xargs :guard (alistp B)))
  (if (endp B)
      '()
    (if (equal (caar B) key)
        B
      (alist-suffix-starting-with key (cdr B)))))

(program)                               
(defun subst-b*-entry (key exp B)
  (b* ((dup-key-start-block (alist-suffix-starting-with key B))
       (prior-block (take (- (len B) (len dup-key-start-block)) B))
       (prior-block (list-up-lists (strip-cars prior-block)
                                   (acl2::sublis-expr-lst (inverse-subst/b*-entry key exp)
                                                          (strip-cadrs prior-block)))))
    (append prior-block dup-key-start-block)))
         
                       

(defun collapse-b*-binding (B1 B2)
; subst values with their keys from earlier entries, but be careful
; only to touch values before the next duplicate var binding
  (if (endp B1)
      B2
    (cons (car B1)
          (subst-b*-entry (caar B1) (cadr (car B1))
                          (collapse-b*-binding (cdr B1) B2)))))



; Putting together the middle and back ends! [2016-04-01 Fri]

; [2016-08-12 Fri] Modification to incorporate Pete's hint that unsat but
; fixable hyps should nonetheless be fixed and this should be prefixed to the
; actual b*-soln.
(defun fixer-arrangement1/repeat (C i all-terms vl ctx state B new-hyps)
  (if (endp C)
      (value (list B new-hyps '()))
    (b* ((- (cw? (verbose-stats-flag vl)
                 "~| Cgen/Note: Recursively fix (loop iteration: ~x0) ~x1~%" i C))
         ((mv erp res state) (fixer-arrangement1 C all-terms vl ctx state))
         ((when erp) (value (list B new-hyps C))) ;return current
         ((list B1 new-hyps1 C_unsat) res)
         ((unless (< (len C_unsat) (len C))) (value (list B new-hyps C))) ;return current
         (B (append B1 B))
         (new-hyps (union-equal new-hyps1 new-hyps)))
      (fixer-arrangement1/repeat C_unsat (1+ i) all-terms vl ctx state B new-hyps))))
         
(defun fixer-arrangement-builtin (hyps concl vl ctx state)
  (b* ((terms (append hyps  (if (not (acl2::logic-termp concl (w state)))
                                '()
                              (list (cgen-dumb-negate-lit concl)))))
       ((mv erp res state)
        (fixer-arrangement1 terms terms vl ctx state))
       ((when erp) (value (list nil nil)))
       ((list B new-hyps C_unsat) res)

       (rec-fixp (acl2s-defaults :get :recursively-fix))
       ((mv ?erp (list B new-hyps C_unsat) state) ;does not return an error
        ;;(fixer-arrangement1-lst (singletonize fixable-hyps/unsat) terms vl ctx state))
        (if (and rec-fixp 
                 (< (len C_unsat) (len terms)))
            (fixer-arrangement1/repeat C_unsat 1 terms vl ctx state B new-hyps)
          (value (list B new-hyps C_unsat)))) ;o.w return current values

       (- (cw? (and (verbose-stats-flag vl) rec-fixp (consp C_unsat))
               "~| Cgen/Verbose: ~x0 still not fixed! ~%" C_unsat))
        
       (b*-binding (to-b*-mv-binding B))
       (b*-binding (collapse-b*-binding b*-binding nil))
       )
    (value (list b*-binding new-hyps))))

         
(defttag t)
(defattach (fixer-arrangement fixer-arrangement-builtin) :skip-checks t)
(defttag nil)



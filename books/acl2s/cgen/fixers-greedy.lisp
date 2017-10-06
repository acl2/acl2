#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "utilities")
(include-book "misc/bash" :dir :system)
(include-book "data-structures/utilities" :dir :system)
(include-book "cgen-state")

(defloop get1-lst (a xs)
  (for ((x in xs))
       (collect (get1 a x))))
       

(defun cweight (c Cwt{})
  (or (get1 c Cwt{})
      0))

(defun cweight-lst (cs Cwt{})
  (if (endp cs)
      0
    (+ (cweight (car cs) Cwt{})
       (cweight-lst (cdr cs) Cwt{}))))

(defloop filter-terms-without-vars (terms vars)
  (for ((term in terms))
       (when (not (intersectp-eq (acl2::all-vars term) vars))
         (collect term))))

(defun pval (fname fxri{} flits term->flits{} Cwt{} vl)
  (declare (ignorable vl term->flits{}))
  (b* ((fruleI (get1 fname fxri{}))
       (cterm (get1 :constraint-term fruleI))
       (pterms (get1 :preserves fruleI))
       (trivially-preserved-terms (filter-terms-without-vars flits (get1 :Out fruleI))))
    (list (+ (cweight cterm Cwt{}) (cweight-lst pterms Cwt{}))
          (cweight-lst trivially-preserved-terms Cwt{}))))
       
  
;; (defun fxri-let*-soln/greedy1 (term->flits{} var-clique-rep{} Cwt{} fxri{} vl state pval{} ans)
;;   (declare (ignorable vl))
;;   (if (or (endp term->flits{})
;;           (endp fxri{}))
;;       (value ans)
;;     (b* ((pval{} (update-pval-alist pval{} fxri{} term->flits{} Cwt{}))
;;          (fname (choose-maximal-pval-fxri pval{}))
;;          (- (cw? (debug-flag vl) "~| Cgen/Debug: Maximal pvalued fixer: ~x0~%" fname))
;;          (ans (cons (fxri-b*-entry (assoc-equal fname fxri{})) ans))
;;          (fxri1{} (delete-assoc-equal fname fxri{}))
;;          (fxri1{} (remove-unpreserved-fxrs fxri{} fname))
;;          (term->flits1{} (remove-unpreserved-flits term->flits{} fname fxri{}))
;;          )
;;       (fxri-let*-soln/greedy1 term->flits1{} Cwt{} fxri1{} vl state pval{} ans))))


(program)
(set-state-ok t)

(defun to-string (x)
  (declare (xargs :mode :program))
  (coerce (cdr (coerce (fms-to-string "~x0" (list (cons #\0 x))) 'list)) 'string))

(defun term-name (term)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (to-string term) 'cgen::x))


(defun flatten-output-fterm (x term output-vars)
  (cond ((proper-symbolp term) nil)
        ((quotep term) nil)
        ((atom term) nil) ;unreachable?
        (t (and (member-eq x output-vars) ;only flatten if corresponding x is an output
                (list (cons (term-name term) term))))))

(defloop flatten-output-fterms (sigma output-vars)
; "abstract away function-applications, corresponding to outputs, with new
; internal variable names. return the a-list"
  (for ((pair in sigma))
       (append (flatten-output-fterm (car pair) (cdr pair) output-vars))))

(defloop invert-alist (alist)
  (declare (xargs :guard (alistp alist)))
  (for ((x.y in alist))
       (collect (cons (cdr x.y) (car x.y)))))

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


(defloop filter-terms-with-vars (terms vars)
  (for ((term in terms))
       (when (intersectp-eq (acl2::all-vars term) vars)
         (collect term))))

(defun collect-vars (term)
  (reverse (acl2::all-vars term)))
(defloop collect-vars-lst (terms)
  (for ((term in terms)) (append (collect-vars term))))

(defmacro s+ (&rest args)
  "string/symbol(s) concat to return a symbol.
  :pkg and :separator keyword args recognized."
  `(defdata::s+ ,@args :pkg "CGEN"))

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

(defun top-function-symbol (term)
  (case-match term
    (('EQUAL (f1 . &) (f2 . &)) (declare (ignore f2)) f1) ;ignore f2
    (('EQUAL x (f . &)) (if (proper-symbolp x) f nil))
    (('EQUAL (f . &) x) (if (proper-symbolp x) f nil))
    (('QUOTE &) nil)
    ((f . &) f)))

(defun destruct-equality-hyp (hyp)
  (case-match hyp
    (('EQUAL x (f . args)) (list x (acl2::cons-term f args)))
    (('EQUAL (f . args) x) (list x (acl2::cons-term f args)))
    (('EQUAL x y) (list x y))))

(defun monadic-term-p (term)
  (and (consp term)
       (not (equal (acl2::ffn-symb term) 'QUOTE))
       (consp (cdr term))
       (null (cddr term))))
(defloop monadic-term-listp (terms)
  (for ((term in terms)) (always (monadic-term-p term))))

(defloop equality-vars (eq-terms)
  (for ((eq-term in eq-terms))
       (collect (b* (((list w &) (destruct-equality-hyp eq-term)))
                  w))))
  

;;; merge fixer term from frulei into one subcircuit term with
;;; pre-fixers from eparam-fxri{} and post-fixers from
;;; internal-eq-fxri{}
(defun make-subckt-frule (eparam-fxri{} internal-eq-fxri{} W{} cterm frulei)
  (b* ((frules-eq (strip-cdrs internal-eq-fxri{}))
       (frules-param (strip-cdrs eparam-fxri{}))
       (internal-vars (equality-vars (get1-lst :constraint-term frules-eq)))
       (B-eq (convert-conspairs-to-listpairs W{}))
       (frulei (put-assoc-eq :constraint-term cterm frulei))
       (frulei (put-assoc-eq :fixes (list cterm) frulei)) ;TODO: what about single fixer fixing multiple terms
       (frulei (put-assoc-eq :preserves (list cterm) frulei))
       (In (union-eq (get1-lst :In frules-param)
                     (union-eq (set-difference-eq (get1 :In frulei)
                                                  (get1-lst :Out frules-param))
                               (set-difference-eq (get1-lst :In frules-eq)
                                                  internal-vars))))
       (frulei (put-assoc-eq :In In frulei))
       (Out (union-eq (set-difference-eq (get1 :Out frulei) internal-vars)
                      (get1-lst :Out frules-eq)))
       (frulei (put-assoc-eq :Out Out frulei))
       (B (append (union-lsts (get1-lst :fixer-let-binding frules-param))
                  B-eq
                  (get1 :fixer-let-binding frulei)
                  (union-lsts (get1-lst :fixer-let-binding frules-eq))))
       (frulei (put-assoc-eq :fixer-let-binding B frulei)))
    frulei))
         
(defun add-to-fxri{} (frule1I fxri{}) ; --> fxri{}
  (b* ((ctx 'add-to-fxri{})
       (nm (get1 :name frule1I))
       (existing-entry (assoc-equal nm fxri{}))
       ((unless existing-entry) (put-assoc-equal nm frule1I fxri{}))
       (fxri-data (cdr existing-entry))
       ((unless (and (equal (get1 :In fxri-data) (get1 :In frule1I))
                     (equal (get1 :Out fxri-data) (get1 :Out frule1I))
                     (equal (get1 :fixer-let-binding fxri-data) (get1 :fixer-let-binding frule1I))))
        (er hard? ctx "~| Incompatible fixer rule instances have same key; cannot be merged! ~ 
existing: ~x0 new: ~x1~%" fxri-data frule1I))
       (hyps  (union-equal (get1 :hyps fxri-data) (get1 :hyps frule1I)))
       (fixes (union-equal (get1 :fixes fxri-data) (get1 :fixes frule1I)))
       ;;update hyps and fixes
       (fxri-data (put-assoc-equal :hyps hyps (put-assoc-equal :fixes fixes fxri-data))))
    (put-assoc-equal nm fxri-data fxri{})))

(defun append-fxri{} (fxri1{} fxri{})
  (if (endp fxri1{})
      fxri{}
    (add-to-fxri{} (cdar fxri1{})
                   (append-fxri{} (cdr fxri1{}) fxri{}))))

(defun equalitize (cons-pair)
;"convert (s . t) to (equal s t)"
  `(EQUAL ,(car cons-pair) ,(cdr cons-pair)))

(u::defloop equalitize-lst (alst)
  (for ((cons-pair in alst)) (collect (equalitize cons-pair))))

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

(defun fixer-rules-table (wrld)
  (table-alist 'FIXER-RULES-TABLE wrld))

(defun preservation-rules-table (wrld)
  (table-alist 'PRESERVATION-RULES-TABLE wrld))


(mutual-recursion
(defun instantiate-fixer-rule (frule cterm all-terms vl state)
; fixer rule * pseudo-termp * pseudo-term-listp * vl * state
; --> (mv erp fxri{} state)
  (b* ((ctx 'instantiate-fixer-rule)
       (rule-name (get1 :rule-name frule))
       ((mv yesp s-alist) (acl2::one-way-unify (get1 :constraint-term frule) cterm))
       ((unless yesp) (value '()))
       ;; check that meta-precondition is satisfied
       (meta-precondition (get1 :meta-precondition frule))
       (letb (acl2::listlis (strip-cars s-alist) (acl2::kwote-lst (strip-cdrs s-alist))))
       ((mv erp okp) (if (equal meta-precondition 't)
                         (mv nil t)
                       (trans-my-ev-w `(LET ,letb
                                            (declare (ignorable ,@(strip-cars s-alist)))
                                            ,meta-precondition)
                                      ctx (w state) nil)))
       
       ((unless (and (not erp) okp))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Meta-precondition for fixer rule ~x0 not satisfied.~%" rule-name)
         (value '())))
       
       ;; variable abstraction
       (W{} (flatten-output-fterms s-alist (get1 :Out frule)))

       (r-alist (pairlis$ (strip-cars s-alist)
                          (acl2::sublis-expr-lst (invert-alist W{})
                                                 (strip-cdrs s-alist))))
       ((unless (valid-output-symbols (acl2::sublis-expr-lst r-alist (get1 :Out frule))))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Fixer rule ~x0 not applicable due to non-variable output.~%" rule-name)
         (value '())))
       
       (fruleI (fixer-rule-instance frule r-alist))
       (allvars (acl2::all-vars1-lst all-terms '()))
       (curr-vars (union-eq (strip-cars W{}) allvars))
       (rule-hyps (filter-terms-with-vars (get1 :hyps fruleI) curr-vars))

       ;TODO: rename to avoid variable capture
       (eparam-hyps (set-difference-equal (get1 :hyps fruleI) rule-hyps))
       ((unless (monadic-term-listp eparam-hyps))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Test/Enum parameter hypotheses should be monadic ~x0!~%" eparam-hyps)
         (value '())))
       (E (equalitize-lst W{}))
       (query `(IMPLIES (AND ,@all-terms ,@E) (AND . ,rule-hyps)))
       (hints '())
       ((mv erp res state) (cgen::bash-fn query hints (debug-flag vl) ctx state))
       ((unless (and (not erp) (eq res nil)))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Unable to relieve query for fixer rule ~x1!~%" query rule-name)
         (value '())))
       (enum-hyps (filter-type-hyps eparam-hyps (w state)))
       (to-fix-eparam-hyps (set-difference-equal eparam-hyps enum-hyps))
       (frules (strip-cdrs (fixer-rules-table (w state))))
       ((er eparam-fxri{}) (instantiate-fixer-rules frules to-fix-eparam-hyps all-terms vl state '()))
       ((when (and (consp to-fix-eparam-hyps) (endp eparam-fxri{})))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Supporting Enum-param fixers not found for rule ~x0!~%" rule-name)
         (value '())))
       ((er internal-eq-fxri{}) (instantiate-fixer-rules frules E all-terms vl state '()))
       ((when (and (consp E) (endp internal-eq-fxri{})))
        (prog2$
         (cw? (verbose-flag vl)
              "~| Cgen/Note: Supporting internal equation fixers not found for rule ~x0!~%" rule-name)
         (value '())))
       (subckt-frulei (make-subckt-frule eparam-fxri{} internal-eq-fxri{} W{} cterm
                                         ;; add enum hyps here itself
                                         (put-assoc-eq :enum-hyps enum-hyps fruleI))))
    (value subckt-frulei)))
    
    

;; iterate over frules
(defun instantiate-fixer-rules1 (frules cterm all-terms vl state fxri{})
; pseudo-termp * listof fixer-rule * pseudo-term-listp * fixnum * state 
; --> (mv erp fxri{} state)
  (b* (((when (endp frules)) (value fxri{}))
       ((er fruleI) (instantiate-fixer-rule (car frules) cterm all-terms vl state))
       (fxri{} (add-to-fxri{} fruleI fxri{})))
    (instantiate-fixer-rules1 (cdr frules) cterm all-terms vl state fxri{})))

;; iterate over terms
(defun instantiate-fixer-rules (frules terms all-terms vl state fxri{})
  (b* (((when (endp terms))  (value fxri{}))
       (term (car terms))
       ;; (fn-sym (top-function-symbol term))
       ;; TODO (frules (filter-frules-by-top-function frules fn-sym))
       ((er fxri1{}) (instantiate-fixer-rules1 frules term all-terms vl state '())))
    (instantiate-fixer-rules frules (cdr terms) all-terms vl state
                             (append-fxri{} fxri1{} fxri{}))))
)

       
(include-book "acl2s/cgen/prove-cgen" :dir :system :ttags :all)

(defun term-preserved-by-fxr-test? (pterm fixer-binding pterm-fxr-binding type-hyps vl state)
  (declare (ignorable vl))
  (b* ((bound-vars (remove-duplicates-eq (strip-cars (append pterm-fxr-binding
                                                             fixer-binding))))
       (query `(IMPLIES (AND ,@type-hyps)
                        (LET* (,@pterm-fxr-binding ;;this makes pterm true
                               ,@fixer-binding) ;; this updates
                              (declare (ignorable ,@bound-vars))
                              ,pterm))) ;check if pterm is still true after update
       (cgen-state (make-cgen-state-fn
                    query
                    (list :testing-enabled :naive
                          :num-trials 1000
                          :search-strategy :simple
                          :num-counterexamples 1000
                          :num-witnesses 1000
                          :sampling-method :uniquery-random
                          :use-fixers nil)
                    (w state)))
       ((er cgen-state) (prove/cgen query nil cgen-state state))
       (gcs% (cget gcs))
       (num-vac (access gcs% vacs))
       (valid-runs (- (access gcs% runs) num-vac))
       ;; if more than half of runs are not vacuous, and more than a
       ;; half of these are witnesses then we deem that fixer-binding
       ;; preserves pterm
       (good-enough? (and (> valid-runs 500)
                          (> (/ (access gcs% wts) valid-runs) 50/100))))
    (value good-enough?)))
  

;;; find the associated fixer let-binding for term in fxri{}
(defloop assoc-fixer-binding (term fxri{})
  (for ((fxri-entry in fxri{}))
       (when (equal term (get1 :constraint-term (cdr fxri-entry)))
         (return (get1 :fixer-let-binding (cdr fxri-entry))))))

;; Note that fxr F is represented as the fixer let-binding
(defun filter-terms-preserved-by-fxr (pterms F fxri{} type-hyps vl state)
  (declare (ignorable vl))
  (b* (((when (endp pterms)) (value nil))
       (pterm-F (assoc-fixer-binding (car pterms) fxri{}))
       ((er yesp) (term-preserved-by-fxr-test? (car pterms) F pterm-F type-hyps vl state))
       ((er rest) (filter-terms-preserved-by-fxr (cdr pterms) F fxri{} type-hyps vl state)))
    (value (append (and yesp (list (car pterms)))
                   rest))))

;;; dynamically update :preserves field for each frule in fxri-entries
(defun update-preservation-relation (fxri-entries cterms fxri{} type-hyps vl state)
  (declare (ignorable vl))
  (b* (((when (endp fxri-entries)) (value nil))
       ((cons nm frulei) (car fxri-entries))
       (pterms (filter-terms-with-vars cterms (get1 :Out frulei)))
       (trivial-preserved-terms (set-difference-equal cterms pterms))
       ((er preserved-terms)
        (filter-terms-preserved-by-fxr pterms (get1 :fixer-let-binding frulei)
                                       fxri{} type-hyps vl state))
       ((er rest-fxri-entries)
        (update-preservation-relation (cdr fxri-entries) cterms fxri{} type-hyps vl state))
       (frulei (put-assoc-eq :preserves (cons (get1 :constraint-term frulei)
                                              preserved-terms)
                             (put-assoc-eq :trivially-preserves trivial-preserved-terms
                                           frulei))))
    (value (cons (cons nm frulei) rest-fxri-entries))))
                                                
       
  

;;; Compute a fixer circuit, in terms of let* binding, that satisfies
;;; the maximum number of cterms.
(defun maxsat-fxr-ckt (cterms Cwt{} fxri{} vl state)
  (declare (ignorable cterms Cwt{} fxri{} vl state))
  (value (list nil nil)))



(defun fixer-arrangement1 (terms all-terms Cwt{} vl ctx state)
; returns (mv erp (list let*-soln-binding new-hyps unsat-terms) state)
; - unsat-terms are a subset of terms. they exclude type-hyps and
;   those terms that have no applicable fixer rules.
;   these terms were unsat, because the preservation rules did not work out
; - new-hyps characterize new parameters introduced by applicable fixer rules
  (b* ((wrld (w state))
       (frules (strip-cdrs (fixer-rules-table wrld)))
       (prules (strip-cdrs (preservation-rules-table wrld)))
       (type-hyps (filter-type-hyps terms wrld))
       (cterms (set-difference-equal terms type-hyps))
       ((er fxri{}) (instantiate-fixer-rules frules cterms all-terms vl state '()))
       ;; ((er fxri{}) (instantiate-pres-rules prules cterms all-terms vl state fxri{}))
       ((er fxri{}) (update-preservation-relation fxri{} cterms fxri{} type-hyps vl state))
       (fixable-terms (filter-fixable-terms cterms fxri{}))
       ((er (list let*-soln01 C_sat))
        (maxsat-fxr-ckt fixable-terms Cwt{} fxri{} vl state))

       (C_unsat (set-difference-equal fixable-terms C_sat))
       ;(b*-soln (to-b*-mv-binding let*-soln))
       ;(let*-soln (assoc-equal-lst vars let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixer-bindings: ~x0~%" let*-soln))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixed terms: ~x0~%" C_sat))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Unsat fixable terms: ~x0~%" C_unsat))
       ;; TODO check that this let* binding is sound/correct, i.e., it
       ;; satisfies all the hyps under fixer and pres rules.
       (new-hyps (union-lsts (get1-lst :enum-hyps (strip-cdrs fxri{}))))
       )
    (value (list let*-soln new-hyps C_unsat))))

(defun fixer-arrangement1/repeat (C i all-terms vl ctx state B new-hyps)
  (if (endp C)
      (value (list B new-hyps '()))
    (b* ((- (cw? (verbose-stats-flag vl)
                 "~| Cgen/Note: Recursively fix (loop iteration: ~x0) ~x1~%" i C))
         ((mv erp res state) (fixer-arrangement1 C all-terms vl ctx state))
         ((when erp) (value (list B new-hyps C))) ;return current

         ((list B1 new-hyps1 C_unsat) res)
         ((unless (< (len C_unsat) (len C))) (value (list B new-hyps C))) ;pathological case that helps termination
         
         (B (append B1 B))
         (new-hyps (union-equal new-hyps1 new-hyps)))
      (fixer-arrangement1/repeat C_unsat (1+ i) all-terms vl ctx state B new-hyps))))
         

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
    
  
(defun to-b*-mv-binding-aux (letB ans)
  (if (endp letB)
      (reverse ans) ;keep original order
    (b* (((list var e) (car letB))
         ((unless (and (consp e) (equal (car e) 'MV-NTH)))
          (to-b*-mv-binding-aux (cdr letB) (cons (car letB) ans)))
         (`(MV-NTH (QUOTE ,index) (MV-LIST (QUOTE ,arity) ,mv-term)) e))
      (to-b*-mv-binding-aux (cdr letB) (update-mv-binding var index arity mv-term ans)))))
         
(defun to-b*-mv-binding (letB)
  (to-b*-mv-binding-aux letB '()))

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


(defun fixer-arrangement-builtin (hyps concl vl ctx state)
  (b* ((terms (append hyps  (if (not (acl2::logic-termp concl (w state)))
                                '()
                              (list (cgen-dumb-negate-lit concl)))))
       ((mv erp res state) (fixer-arrangement1 terms terms vl ctx state))
       ((when erp) (value (list nil nil)))
       
       ((list B new-hyps C_unsat) res)
              (rec-fixp (acl2s-defaults :get :recursively-fix))
       ((mv & (list B new-hyps C_unsat) state) ;does not return an error
        (if (and rec-fixp
                 (< (len C_unsat) (len terms)))
            (fixer-arrangement1/repeat C_unsat 1 terms vl ctx state B new-hyps)
          (value (list B new-hyps C_unsat)))) ;o.w return current values

       (- (cw? (and (verbose-stats-flag vl) rec-fixp (consp C_unsat))
               "~| Cgen/Verbose: ~x0 still not fixed! ~%" C_unsat))
        
       (b*-binding (collapse-b*-binding (to-b*-mv-binding B) nil)))
    
    (value (list b*-binding new-hyps))))


(logic)
(defttag t)
(defattach (fixer-arrangement fixer-arrangement-builtin) :skip-checks t)
(defttag nil)

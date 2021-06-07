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
       


(defloop filter-terms-without-vars (terms vars)
  (for ((term in terms))
       (when (not (intersectp-eq (acl2::all-vars term) vars))
         (collect term))))

       
(program)
(set-state-ok t)

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
       (test-hypsI  (acl2::sublis-expr-lst alist (get1 :test-hyps frule)))
 
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
       (fruleI (put-assoc :test-hyps test-hypsI fruleI))
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
  (and (consp hyp)
       (member-equal (car hyp)
                     '(EQUAL EQ EQL = INT= STRING-EQUAL ACL2::HONS-EQUAL))
       (case-match hyp
         ((& x (f . args)) (list x (acl2::cons-term f args)))
         ((& (f . args) x) (list x (acl2::cons-term f args)))
         ((& x y) (list x y)))))

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
       (frulei (put-assoc-eq :preserves '() frulei))
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
       ((unless (get1 :name frule1I)) fxri{})
       (nm (get1 :name frule1I))
       (existing-entry (assoc-equal nm fxri{}))
       ((unless (consp existing-entry)) (put-assoc-equal nm frule1I fxri{}))
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
    (acl2::put-assoc-equal-fast nm fxri-data fxri{})))

(defun revappend-fxri{} (fxri1{} fxri{})
  (if (endp fxri1{})
      fxri{}
    (revappend-fxri{} (cdr fxri1{})
                      (add-to-fxri{} (cdar fxri1{}) fxri{}))))

(defun equalitize (cons-pair)
;"convert (s . t) to (equal s t)"
  `(EQUAL ,(car cons-pair) ,(cdr cons-pair)))

(u::defloop equalitize-lst (alst)
  (for ((cons-pair in alst)) (collect (equalitize cons-pair))))


(defloop filter-type-hyps (terms wrld)
  (for ((term in terms))
       (append (and (consp term) (defdata::is-type-predicate (car term) wrld)
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
                             (revappend-fxri{} fxri1{} fxri{}))))
)


(defun destruct-var-equality-hyp (hyp)
  (case-match hyp
    ((& x (f . args)) (list x (acl2::cons-term f args)))
    ((& (f . args) x) (list x (acl2::cons-term f args)))
    ((& x y) (if (acl2::symbol-< x y) (list x y) (list y x)))))

(defun make-dummy-equality-frule-instance (eq-hyp)
  (b* (((list x equal-to-term) (destruct-var-equality-hyp eq-hyp))
       (out-vars (list x))
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


(defloop dummy-eq-frule-instances (hyps)
  (for ((hyp in hyps))
       (when (is-var-equality-hyp hyp)
         (collect (make-dummy-equality-frule-instance hyp)))))



(include-book "acl2s/cgen/prove-cgen" :dir :system :ttags :all)

(defun term-preserved-by-fxr-test? (pterm frule pterm-frule all-terms vl ctx state)
  (declare (ignorable vl all-terms))
  (b* ((pterm-fxr-binding (get1 :fixer-let-binding pterm-frule))
       (fixer-binding (get1 :fixer-let-binding frule))
       (bound-vars (remove-duplicates-eq (strip-cars (append pterm-fxr-binding
                                                             fixer-binding))))
       (ign-vars (set-difference-eq bound-vars (collect-vars pterm)))
       ;; (cl (clausify-hyps-concl all-terms ''nil))
       ;; ((mv contradictionp type-alist pot-lst)
       ;;  (acl2::cheap-type-alist-and-pot-lst cl (acl2::ens state) (w state) state))
       ;; (acl2-type-hyps (and (not contradictionp) (reify-type-alist-hyps type-alist)))
       ;; (acl2-leq-hyps (and (not contradictionp) (reify-pot-lst-hyps pot-lst)))
       ;; (type-hyps (union-equal (filter-type-hyps all-terms (w state))
       ;;                         acl2-type-hyps))
       (type-hyps (remove-duplicates-equal
                   (append (get1 :hyps frule) (get1 :test-hyps frule)
                           (get1 :hyps pterm-frule) (get1 :test-hyps pterm-frule))))
       (query `(IMPLIES (AND ,@type-hyps) ;,@acl2-leq-hyps)
                        (LET* (,@pterm-fxr-binding ;;this makes pterm true
                               ,@fixer-binding) ;; this updates
                              (declare (ignorable ,@ign-vars))
                              ,pterm))) ;check if pterm is still true after update
       (cgen-state (make-cgen-state-fn
                    query ctx
                    (list :num-trials 500
                          :testing-enabled :naive
                          :search-strategy :simple
                          :sampling-method :random ;more efficient
                          :num-witnesses 251
                          :num-print-counterexamples 0
                          :num-print-witnesses 0
                          :use-fixers nil
                          :verbosity-level (if (system-debug-flag vl) 3 1))
                    (w state)))
       ((mv & cgen-state state) (test/cgen query nil cgen-state state))
       ;; ((er &) (print-testing-summary cgen-state ctx state))
       
       (gcs% (cget gcs))
       (num-vac (access gcs% vacs))
       (total-runs (access gcs% runs))
       (valid-runs (- total-runs num-vac))
       ;; if more than half of runs are not vacuous, and more than a
       ;; half of these are witnesses then we deem that fixer-binding
       ;; preserves pterm
       (good-enough? (and (posp total-runs)
                          (> (/ valid-runs total-runs) 1/2)
                          (posp valid-runs)
                          (> (/ (access gcs% wts) valid-runs) 1/2))))
    (value good-enough?)))
  

;;; find one associated fixer rule for term in fxri{}
(defloop assoc-frule (term fxri{})
  (for ((fxri-entry in fxri{}))
       (when (equal term (get1 :constraint-term (cdr fxri-entry)))
         (return (cdr fxri-entry)))))

;; find all fixer rules associated with term in fxri{}
(defloop assoc-all-frules (term fxri{})
  (for ((fxri-entry in fxri{}))
       (when (equal term (get1 :constraint-term (cdr fxri-entry)))
         (collect (cdr fxri-entry)))))


(defloop assoc-frule-lst (terms fxri{})
  (for ((term in terms))
       (append (assoc-all-frules term fxri{}))))


;; Note that fxr is represented as the fixer let-binding
(defun filter-terms-preserved-by-fxr (pterms fxr-rule fxri{} all-terms vl ctx state)
  (declare (ignorable vl))
  (b* (((when (endp pterms)) (value nil))
       (pterm-frule (assoc-frule (car pterms) fxri{}))

       ((er yesp) (term-preserved-by-fxr-test? (car pterms) fxr-rule
                                               pterm-frule
                                               all-terms vl ctx state))
       ((er rest) (filter-terms-preserved-by-fxr (cdr pterms) fxr-rule
                                                 fxri{} all-terms vl ctx state)))
    (value (append (and yesp (list (car pterms)))
                   rest))))

;;; dynamically update :preserves field for each frule in fxri-entries
(defun update-preserves-relation (fxri-entries cterms fxri{} all-terms vl ctx state)
  (declare (ignorable vl))
  (b* (((when (endp fxri-entries)) (value nil))
       ((cons nm frulei) (car fxri-entries))
       (pterms (filter-terms-with-vars cterms (get1 :Out frulei)))
       (trivial-preserved-terms (set-difference-equal cterms pterms))
       ((er preserved-terms)
        (filter-terms-preserved-by-fxr (remove1-equal (get1 :constraint-term frulei) pterms)
                                       frulei
                                       fxri{} all-terms vl ctx state))
       ((er rest-fxri-entries)
        (update-preserves-relation (cdr fxri-entries) cterms fxri{} all-terms vl ctx state))
       (frulei (put-assoc-eq :preserves preserved-terms
                             (put-assoc-eq :trivially-preserves trivial-preserved-terms
                                           frulei))))
    (value (cons (cons nm frulei) rest-fxri-entries))))
                                                
       

(defun cweight (c Cwt{})
  (or (get1 c Cwt{})
      0))

(defun cweight-lst (cs Cwt{})
  (if (endp cs)
      0
    (+ (cweight (car cs) Cwt{})
       (cweight-lst (cdr cs) Cwt{}))))

;; Compute pval of fixer fname that gives a measure of how many terms
;; it preserves.
(defun pval0 (fname cterms fxri{} Cwt{})
  (b* ((fruleI (get1 fname fxri{}))
       (cterm (get1 :constraint-term fruleI))
       (pterms (intersection-equal (get1 :preserves fruleI) cterms))
       (trivial-preserved-terms (intersection-equal (get1 :trivially-preserves fruleI) cterms)))
    (+ (cweight cterm Cwt{})
       (cweight-lst pterms Cwt{})
       (cweight-lst trivial-preserved-terms Cwt{}))))

#|
(defun pval0-lst (fnames cterms fxri{} Cwt{})
  (if (endp fnames)
      0
    (+ (pval0 (car fnames) cterms fxri{} Cwt{})
       (pval0-lst (cdr fnames) cterms fxri{} Cwt{}))))


(defun pval0-max-lst (fnames cterms fxri{} Cwt{} ans)
  (if (endp fnames)
      ans
    (pval0-max-lst (cdr fnames) cterms fxri{} Cwt{}
                   (max (pval0 (car fnames) cterms fxri{} Cwt{})
                        ans))))
|#

(mutual-recursion 
 (defun pval-fxr-aux (fname cterms fxri{} Cwt{})
   ;; (if (member-equal fname seen)
   ;;     (prog2$ (cw " Already seen ~x0~%" fname)
   ;;             0)
     (b* (
          ;;(- (cw "fname :~x0~%" fname))
          ;;(- (cw "len=~x0 seen :~x1~%" (len seen) seen))
          (fruleI (get1 fname fxri{}))
          (cterms (remove1-equal (get1 :constraint-term fruleI) cterms))
          (pterms (intersection-equal (get1 :preserves fruleI) cterms))
          (trivial-preserved-terms (intersection-equal (get1 :trivially-preserves fruleI) cterms))
          (all-pterms (append pterms trivial-preserved-terms))
          ;;(- (cw "len=~x0 pterms :~x1~%" (len pterms) pterms))
          )
       (+ (pval0 fname cterms fxri{} Cwt{})
          (pval-terms pterms all-pterms fxri{} Cwt{} 0))))

 (defun pval-fxr-max-lst (fnames cterms fxri{} Cwt{} ans)
   (if (endp fnames)
       ans
     (pval-fxr-max-lst (cdr fnames) cterms fxri{} Cwt{}
                       (max (pval0 (car fnames) cterms fxri{} Cwt{}) ans)
                       ;; (max (pval-fxr-aux (car fnames) cterms fxri{} Cwt{} seen) ans)
                       )))
 
 (defun pval-terms (terms cterms fxri{} Cwt{} ans)
   (if (endp terms)
       ans
     (b* ((term (car terms))
          (fnames (get1-lst :name (assoc-all-frules term fxri{})))
          ;; (- (cw "get max of ~x0 fxrs~%" (len fnames)))
          (pval-max (pval-fxr-max-lst fnames cterms fxri{} Cwt{} 0))
          )
       
       (pval-terms (cdr terms) cterms fxri{} Cwt{} (+ pval-max ans)))))
 )    

(memoize 'pval0 :ideal-okp t)

(defun pval-fxr (fname cterms fxri{} Cwt{})
  (pval-fxr-aux fname cterms fxri{} Cwt{}))

(memoize 'pval-fxr :ideal-okp t)

;; insert pval field into each frule in fxri-entries
(defun assign-pval-scores-aux (fxri-entries cterms fxri{} Cwt{})
  (if (endp fxri-entries)
      '()
    (b* (((cons fname frule) (car fxri-entries))
         (pval (pval-fxr fname cterms fxri{} Cwt{}))
         ;; (pval (pval0 fname cterms fxri{} Cwt{}))
         (frule (put-assoc-eq :pval pval frule)))
      (cons (cons fname frule)
            (assign-pval-scores-aux (cdr fxri-entries) cterms fxri{} Cwt{})))))
         
(defun assign-pval-scores (fxri{} cterms Cwt{})
  (b* ((- (cw? nil "DEBUG:: assign-pval-scores - len(fxri) is ~x0~%" (len fxri{}))))
    (assign-pval-scores-aux fxri{} cterms fxri{} Cwt{})))

(defun max-pval-frule (fxri{} ans-frule)
  (if (endp fxri{})
      ans-frule
    (max-pval-frule (cdr fxri{})
                    (if (> (get1 :pval (cdar fxri{}))
                           (get1 :pval ans-frule))
                        (cdar fxri{})
                      ans-frule))))


;; Delete all fixer rules associated with terms in fxri{}
(defloop delete-frules (terms fxri{}) ;; -> fxri{}
  (for ((fxri-entry in fxri{}))
       (unless (member-equal (get1 :constraint-term (cdr fxri-entry)) terms)
         (collect fxri-entry))))



(defun remove-chosen-fixer (frule cterms fxri{}) ;; -> (mv cterms fxri{})
  (b* ((pterms (append (get1 :preserves frule)
                       (get1 :trivially-preserves frule)))
       (cterm (get1 :constraint-term frule))
       (not-preserved-terms (remove1-equal cterm (set-difference-equal cterms pterms)))
       (- (cw? nil "~% remove-chosen-fixer:~x0 cterm:~x1  ~% not-preserved-terms: ~x2~%"
               (get1 :fixer-term frule) cterm not-preserved-terms))

       ;; get rid of cterms that are not preserved
       (rest-cterms (set-difference-equal cterms not-preserved-terms)) 
       (reduced-fxri{} (delete-frules not-preserved-terms fxri{}))

       ;; remove what has already been taken care of
       (rest-cterms (set-difference-equal rest-cterms (list cterm)))
       (reduced-fxri{} (delete-frules (list cterm) reduced-fxri{}))
       )
    (mv rest-cterms reduced-fxri{})))
       
(defun maxsat-fxr-ckt-aux (fxri{} cterms Cwt{} ans-fxri{} fixer-B)
  (declare (ignorable Cwt{}))
  (if (endp fxri{})
      (mv ans-fxri{} fixer-B)
    (b* ((frule (max-pval-frule fxri{} (cdar fxri{})))
         ((mv rest-cterms reduced-fxri{}) (remove-chosen-fixer frule cterms fxri{}))
         ;; (fxri{} (assign-pval-scores fxri{} cterms Cwt{}))
         )
      (maxsat-fxr-ckt-aux reduced-fxri{} rest-cterms Cwt{}
                          (acons (get1 :name frule) frule ans-fxri{})
                          (append (get1 :fixer-let-binding frule)
                                  fixer-B)))))

;;; Compute a fixer circuit, as a let* binding, that greedily satisfies the
;;; maximum number of constraint terms. Return reduced fxri{} that has only the
;;; fixers that took part in the solution and the solution as a B* binding.
(defun maxsat-fxr-ckt (fxri{} cterms Cwt{})
  ;; TODO: perhaps its better to update pval scores everytime fxri{} changes!?
  (maxsat-fxr-ckt-aux (assign-pval-scores fxri{} cterms Cwt{})
                      cterms Cwt{} '() '()))

(defloop filter-fxri-constraint-terms (cterms fxri{})
  (for ((cterm in cterms))
       (when (assoc-frule cterm fxri{})
         (collect cterm))))

(defun fixer-arrangement1 (terms all-terms Cwt{} vl ctx state)
; returns (mv erp (list let*-soln-binding new-hyps unsat-terms) state)
; - unsat-terms are a subset of terms. they exclude type-hyps and
;   those terms that have no applicable fixer rules.
;   these terms were unsat, because the preservation rules did not work out
; - new-hyps characterize new parameters introduced by applicable fixer rules
  (b* ((wrld (w state))
       (frules (strip-cdrs (fixer-rules-table wrld)))
       (?prules (strip-cdrs (preservation-rules-table wrld)))
       (type-hyps (filter-type-hyps terms wrld))
       (cterms (set-difference-equal terms type-hyps))
       ((er fxri{}) (instantiate-fixer-rules frules cterms all-terms vl state
                                             (dummy-eq-frule-instances cterms)))
       ;; ((er fxri{}) (instantiate-pres-rules prules cterms all-terms vl state fxri{}))
       (fixable-terms (filter-fxri-constraint-terms cterms fxri{}))
       ((mv start-time state) (acl2::read-run-time state))
       ((er fxri{}) (update-preserves-relation fxri{} fixable-terms fxri{} all-terms vl ctx state))
       ((mv end-time state) (acl2::read-run-time state))
       (- (cw? (verbose-stats-flag vl)
               "~| Cgen/Verbose: Time taken for updating preservation relation = "))
       ((er &) (if (verbose-stats-flag vl)
                   (pprogn (print-rational-as-decimal (- end-time start-time)
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                 (value nil)))

       ((mv start-time state) (acl2::read-run-time state))
       ((mv fxri{} soln-fxr-binding) (maxsat-fxr-ckt fxri{} fixable-terms Cwt{}))
       ((mv end-time state) (acl2::read-run-time state))
       (- (cw? (verbose-stats-flag vl)
               "~| Cgen/Verbose: Time taken by maxsat-fxr-ckt = "))
       ((er &) (if (verbose-stats-flag vl)
                   (pprogn (print-rational-as-decimal (- end-time start-time)
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                 (value nil)))
       
       ;; (C_sat fixable-terms) ;;For now just line up all fixers. This probably makes recursive fixing inconsequential.
       ;; (C_unsat '())
       (C_sat (filter-fxri-constraint-terms fixable-terms fxri{}))
       (C_unsat (set-difference-equal fixable-terms C_sat))
       ;(b*-soln (to-b*-mv-binding soln-fxr-binding))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixer-bindings: ~%~x0~%" soln-fxr-binding))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Fixed terms: ~x0~%" C_sat))
       (- (cw? (verbose-stats-flag vl) "~| Cgen/Verbose: Unsat fixable terms: ~x0~%~%" C_unsat))
       ;; TODO check that this let* binding is sound/correct, i.e., it
       ;; satisfies all the hyps under fixer and pres rules.
       (new-hyps (union-lsts (get1-lst :enum-hyps (assoc-frule-lst C_sat fxri{}))))
       )
    (value (list soln-fxr-binding new-hyps C_unsat))))

(defun fixer-arrangement1/repeat (C i all-terms Cwt{} vl ctx state B new-hyps)
  (if (endp C)
      (value (list B new-hyps '()))
    (b* ((- (cw? (verbose-stats-flag vl)
                 "~| Cgen/Note: Recursively fix (loop iteration: ~x0) ~x1~%" i C))
         ((mv erp res state) (fixer-arrangement1 C all-terms Cwt{} vl ctx state))
         ((when erp) (value (list B new-hyps C))) ;return current

         ((list B1 new-hyps1 C_unsat) res)
         ((unless (< (len C_unsat) (len C))) (value (list B new-hyps C))) ;pathological case that helps termination
         
         (B (append B1 B))
         (new-hyps (union-equal new-hyps1 new-hyps)))
      (fixer-arrangement1/repeat C_unsat (1+ i) all-terms Cwt{} vl ctx state B new-hyps))))
         

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

;; TODO: assign more weight to a term that is harder to satisfy by Cgen.
(defloop heuristic-weights (terms wrld)
  (for ((term in terms))
       (collect (cond ((and (consp term) (defdata::is-type-predicate (car term) wrld))
                       (cons term 0))
                      ((monadic-term-p term)   (cons term 1))
                      (t (cons term 2))))))
  
(defun fixer-arrangement-builtin (hyps concl vl ctx state)
  (b* ((terms (append hyps  (if (not (acl2::logic-termp concl (w state)))
                                '()
                              (list (cgen-dumb-negate-lit concl)))))
       ((mv start-time state) (acl2::read-run-time state))
       (Cwt{} (heuristic-weights terms (w state)))
       ((mv erp res state) (fixer-arrangement1 terms terms Cwt{} vl ctx state))
       ((when erp) (value (list nil nil)))
       
       ((list B new-hyps C_unsat) res)
              (rec-fixp (acl2s-defaults :get :recursively-fix))
       ((mv & (list B new-hyps C_unsat) state) ;does not return an error
        (if (and rec-fixp
                 (< (len C_unsat) (len terms)))
            (fixer-arrangement1/repeat C_unsat 1 terms Cwt{} vl ctx state B new-hyps)
          (value (list B new-hyps C_unsat)))) ;o.w return current values

       (- (cw? (and (verbose-stats-flag vl) rec-fixp (consp C_unsat))
               "~| Cgen/Verbose: ~x0 still not fixed! ~%" C_unsat))
        
       (b*-binding (collapse-b*-binding (to-b*-mv-binding B) nil))
       ((mv end-time state) (acl2::read-run-time state))
       (- (cw? (verbose-stats-flag vl)
               "~| Cgen/Verbose: Time taken for arranging fixers = "))
       ((er &) (if (verbose-stats-flag vl)
                   (pprogn (print-rational-as-decimal (- end-time start-time)
                                                      (standard-co state)
                                                      state)
                           (princ$ " seconds" (standard-co state) state)
                           (newline (standard-co state) state)
                           (value :invisible))
                 (value nil))))
    
    (value (list b*-binding new-hyps))))


(logic)
(defttag t)
(defattach (fixer-arrangement fixer-arrangement-builtin) :skip-checks t)
(defttag nil)

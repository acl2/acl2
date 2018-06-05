#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "simple-search")
(include-book "incremental-search")
          

(set-state-ok t)

;; Feb 22 2013 Add a new global state variable which points to
;; a stack of accumulated cgen recorded statistics. 

;; [2014-05-03 Sat] Modified again. Now we just have one global cgen-state
;; which stores all the information used and recorded by cgen/testing.

;NOTE: interesting - I cant use defmacro instead of defabbrev

;; (defun get-s-hist-global (ctx state) 
;;   (if (f-boundp-global 'cgen-state state)
;;     (b* ((cgen-state (@ cgen-state))
;;          ((unless (valid-cgen-state-p cgen-state))
;;           (er hard? ctx "~|CEgen/Error: (get-s-hist) cgen-state is ill-formed~|"))
;;          (s-hist (cdr (assoc-eq :s-hist cgen-state))))
;;       (if (s-hist-p s-hist)
;;           s-hist
;;         (er hard? ctx "~|CEgen/Error: hist found in globals is of bad type~|")))
;;     (er hard? ctx "~|CEgen/Error: cgen-state not found in globals ~|")))


;; (defabbrev put-s-hist-global (s-hist) 
;;   (if (f-boundp-global 'cgen-state state)
;;       (if (s-hist-p s-hist)
;;           (b* ((cgen-state (@ cgen-state))
;;                ((unless (valid-cgen-statep cgen-state))
;;                 (prog2$ 
;;                  (er hard? ctx "~|CEgen/Error: (put-s-hist) cgen-state is ill-formed~|")
;;                  state))
;;                (cgen-state (put-assoc-eq :s-hist s-hist cgen-state))
;;                (- (assert$ (valid-cgen-state-p cgen-state) 'put-s-hist-global)))
;;           (f-put-global 'cgen-state cgen-state state))
;;         (progn$
;;          (cw? (debug-flag vl) "~|BAD s-hist : ~x0~|" s-hist)
;;          (er hard? ctx "~|CEgen/Error: hist being put in globals is of bad type~|")
;;          state))
;;     (prog2$ (er hard? ctx "~|CEgen/Error: cgen-state not found in globals ~|")
;;             state)))


(defconst *initial-test-outcomes%* 
  (acl2::make test-outcomes% 
              :cts '() :wts '() :vacs '() 
              :|#wts| 0 :|#cts| 0 
              :|#vacs| 0 :|#dups| 0))

(def initial-s-hist-entry% (name hyps concl vars 
                                 elide-map start)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list 
                      symbol-alist rational) 
              -> s-hist-entry%)
        :doc "make initial s-hist-entry% given args")
  (acl2::make s-hist-entry% 
              :name name :hyps hyps :concl concl :vars vars 
              :elide-map elide-map
              :start-time start :end-time start
              :test-outcomes *initial-test-outcomes%*))
          






#|     
(defthm obvious1 
  (implies (and (pseudo-termp s)
                (not (variablep s))
                (not (fquotep s))
                (not (consp (ffn-symb s))))
           (symbolp (ffn-symb s))))
      
(defthm obvious2
  (implies (and (symbolp a)
                (symbol-listp l))
           (symbol-listp (add-to-set-eq a l))))
|#

(mutual-recursion
(defun all-functions. (term ans.)
  "gather all functions in term"
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-termp term)
                              (symbol-listp ans.))))
  (if (variablep term)
      ans.
    (if (fquotep term)
        ans.
      (let ((fn (ffn-symb term))
            (args (fargs term)))
        (if (or (equal fn 'ACL2::IF)
                (consp fn)) ;lambda
            (all-functions-lst. args ans.)
          (all-functions-lst. args (add-to-set-eq fn ans.)))))))

(defun all-functions-lst. (terms ans.)
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp terms)
                              (symbol-listp ans.))))
  (if (endp terms)
      ans.
    (all-functions-lst.
     (cdr terms) 
     (union-eq (all-functions. (car terms) ans.) 
               ans.)))))
#|      
(defthm all-functions.-type
  (implies (and (symbol-listp a)
                (pseudo-termp term))
           (symbol-listp (all-functions. term a)))
  :hints (("Goal" :induct (all-functions. term a))))
Why is ACL2 not good at this?
|#

;(verify-guards all-functions.)

(defun all-functions (term)
  (declare (xargs :verify-guards nil
                  :guard (pseudo-termp term)))
  (all-functions. term '()))

; TODO: why not just use all-fnnames and all-fnnames-lst (probably they are in
; program mode and verify-termination didt work...)

(defun all-functions-lst (terms)
  (declare (xargs :verify-guards nil
                  :guard (pseudo-term-listp terms)))
  (all-functions-lst. terms'()))


;; collect output signature arity of all multi-valued fns
(defun mv-sig-alist1 (fns wrld)
  "for each fn with output arity n>1, the result alist
   will have an entry (fn . n)"
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
                                    
  (if (endp fns)
      nil
    (let* ((fn (car fns))
           (stobjs-out ;(acl2::stobjs-out fn wrld))) program mode
            (acl2-getprop fn 'acl2::stobjs-out wrld :default '(nil))))
      (if (and (consp stobjs-out)
               (consp (cdr stobjs-out))) ;(mv * ...)
          (acons fn (len stobjs-out)
                 (mv-sig-alist1 (cdr fns) wrld))
        (mv-sig-alist1 (cdr fns) wrld)))))

(defun mv-sig-alist (terms wrld)
  "for each fn with output arity n>1 in terms, the result alist
   will have an entry (fn . n)"
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp terms)
                              (plist-worldp wrld))))
  (b* ((fns (all-functions-lst terms)))
    (mv-sig-alist1 fns wrld)))

(defloop var-var-eq-hyps (hyps)
  (for ((h in hyps)) (append (and (equiv-hyp? h)
                                  (list h)))))

;let*/b* binding
(defun update-var-var-binding (rep other B)
  (if (endp B)
      (acons other rep nil)
    (cons (cons (caar B) (if (eq other (second (car B))) rep (second (car B))))
          (update-var-var-binding rep other (cdr B)))))

(defun var-var-cc (var-var-eq-hyps bindings hyps)
  (declare (xargs :mode :program))
  (if (endp var-var-eq-hyps)
      (mv bindings hyps)
    (b* (((list & x1 x2) (car var-var-eq-hyps))
         ((mv x-rep x-other) (if (term-order x1 x2) (mv x1 x2) (mv x2 x1)))
         (rest (acl2::subst-var-lst x-other x-rep (cdr var-var-eq-hyps))))
      (var-var-cc rest
                  (update-var-var-binding x-rep x-other bindings)
                  (acl2::subst-var-lst x-other x-rep hyps)))))


;;; The Main counterexample/witness generation function           
(def cgen-search-local (name H C
                          type-alist tau-interval-alist
                          programp
                          test-outcomes% gcs% cgen-state
                          ctx state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list
                      alist symbol-alist
                      boolean 
                      test-outcomes%-p gcs%-p cgen-state-p
                      symbol state)
              -> (mv erp (list boolean test-outcomes% gcs%) state))
        :mode :program
        :doc 
;Note: It does not update the global values @gcs% and @s-hist.
"
* Synopsis       
  Local interface to subgoal-level counterexample and witness
  search using either naive testing or incremental dpll
  style search for counterexamples.

* Input parameters (other than those in csearch, that are accumulated)
  - test-outcomes% :: newly created test-outcomes% for this subgoal
  - gcs% :: reified gcs%

* Output signature 
  - (mv erp (list stop? test-outcomes% gcs%) state) where erp is the error tag which is non-nil
    when an error took place during evaluation of (search ...). 
    stop? is T if we should abort our search, i.e our stopping
    condition is satisfied (this value is given by run-tests), 
    otherwise stop? is NIL (by default). test-outcomes% and gcs% are 
    accumulated in the search for cts and wts in the current conjecture

* What it does
  1. retrieve the various search/testing parameters

  2. call simple or incremental search
     depending on the search-strategy set in defaults.
  
  3. return error triple with value (list stop? test-outcomes% gcs%)
")

  
  (b* (
       ;; (defaults (cget params))
;;        (N (get1 :num-trials defaults 0)) ;shudnt it be 100?
;; ;Note: I dont need to provide the default arg 0 above, since we are
;; ;sure the defaults alist we get is complete i.e it would definitely
;; ;contain the key ':num-trials'. But I am envisioning a scenario, where
;; ;I might call this function on its own and not via test?, then this
;; ;functionality is useful for debugging.
;;        (sm (get1 :sampling-method defaults :uniform-random))
;;        (ss (get1 :search-strategy defaults :simple))
;;        (blimit (get1 :backtrack-limit defaults 2))
;;        (num-cts (get1 :num-counterexamples defaults 3))
;;        (num-wts (get1 :num-witnesses defaults 3))
;;        (timeout-secs (get1 :cgen-local-timeout defaults 10))
       (vl (cget verbosity-level))
       
; mv-sig-alist : for each mv fn in H,C, stores its output arity
       (mv-sig-alist (mv-sig-alist (cons C H) (w state)))

       ;;take care of var-var equalities [2016-10-29 Sat]
       (var-var-eq-hyps (var-var-eq-hyps H))
       ((mv elim-bindings H) (var-var-cc var-var-eq-hyps '() H))
       (- (cw? (and (consp elim-bindings)
                    (debug-flag vl))
               "Cgen/Debug : cgen-search:: elim-bindings:~x0  H:~x1~%" elim-bindings H))

       (vars (vars-in-dependency-order H C (w state)))
       )
         
  
;   in
    (case (cget search-strategy)
      (:simple      (simple-search name 
                                   H C vars '() elim-bindings
                                   type-alist tau-interval-alist mv-sig-alist
                                   test-outcomes% gcs%
                                   vl cgen-state
                                   programp nil
                                   ctx state))
      

      (:incremental (if (endp vars)
;bugfix 21 May '12 - if only zero var, delegate to simple search
                        (simple-search name
                                       H C vars '() elim-bindings
                                       type-alist tau-interval-alist mv-sig-alist
                                       test-outcomes% gcs%
                                       vl cgen-state
                                       programp nil
                                       ctx state)
                      
                      (b* ((- (cw? (verbose-stats-flag vl) 
                                   "~%~%CEgen/Note: Starting incremental (dpll) search~%"))
                           (x0 (select (cons (cgen-dumb-negate-lit C) H) vl (w state)))
                           (- (assert$ (proper-symbolp x0) x0))
                           (a% (acl2::make a% ;initial snapshot
                                           :vars vars :hyps H :concl C 
                                           :partial-A '() :elim-bindings elim-bindings
                                           :type-alist type-alist
                                           :tau-interval-alist tau-interval-alist
                                           :inconsistent? nil :cs nil
                                           :var x0 :val ''? :kind :na :i 0)))
;                         in
                        (incremental-search a% '() ;vars has at least 1
                                            name mv-sig-alist
                                            test-outcomes% gcs%
                                            vl cgen-state
                                            programp
                                            ctx state))))
      
      
      (otherwise (prog2$ 
                  (cw? (normal-output-flag vl)
                       "~|CEgen/Error: Only simple & incremental search strategy are available~|")
                  (mv T NIL state))))))

   
(def cgen-search-fn (name H C 
                          type-alist tau-interval-alist elide-map 
                          programp 
                          cgen-state
                          ctx state)
  (decl :sig ((string pseudo-term-list pseudo-term 
                      alist symbol-alist symbol-alist
                      boolean 
                      cgen-state-p
                      symbol state)
              -> (mv erp cgen-state state))
        :mode :program
        :doc 
"
* Synopsis       
  Main Interface to searching for counterexamples (and witnesses)
  in the conjecture (H => C)

* Input parameters
  - name :: name of subgoal or \"top\" if run from test?
  - H :: hyps - the list of terms constraining the cts and wts search
  - C :: conclusion
  - type-alist :: ACL2 type-alist (from call of forward-chain)
  - tau-interval-alist :: tau interval inferred by caller
  - elide-map :: elide-map[v] = term for each elided variable v
  - programp :: T when form has a program mode fun or we are in :program
  - cgen-state :: current cgen-state (to be accumulated)
  - ctx :: ctx (context -- usually a symbol naming the caller function)
  - state :: state

* Output signature 
  - (mv erp cgen-state-p state) where erp is the error tag which is non-nil
    when an error took place during evaluation of (search ...). 
    cgen-state is the updated cgen-state.

* What it does
  1. construct a new s-hist-entry% and call cgen-search-local fun
     with globals reified as explicit arguments: gcs%, test-outcomes%
  2. the return values of test-outcomes% (a field in s-hist-entry%), gcs% 
     are recorded in cgen-state
  3. return (mv erp cgen-state state)
")

  (f* ((update-cgen-state () (b* ((s-hist-entry% (change s-hist-entry% test-outcomes test-outcomes%))
                                  (s-hist-entry% (change s-hist-entry% end-time end))
                                  (s-hist (cget s-hist))
                                  (s-hist (put-assoc-equal name s-hist-entry% s-hist))
                                  (cgen-state (cput s-hist s-hist))
                                  (cgen-state (cput gcs gcs%))
                                  (cgen-state (cput stopping-condition-p stop?)))
                               cgen-state)))

    (b* (((mv start state) (acl2::read-run-time state))
         (vl (cget verbosity-level))
         (vars (vars-in-dependency-order H C (w state)))
         (s-hist-entry% (initial-s-hist-entry% name H C vars elide-map start))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (gcs% (cget gcs))
         ((mv erp res state) (cgen-search-local name H C
                                                type-alist tau-interval-alist
                                                programp 
                                                test-outcomes% gcs% cgen-state
                                                ctx state))
         ((when erp) (mv T cgen-state state)) ;I have already printed the Error message
         ((unless (and (= 3 (len res))
                       (booleanp (first res))
                       (test-outcomes%-p (second res))
                       (gcs%-p (third res))))
          (prog2$ 
           (cw? (verbose-flag vl)
                "~|Cgen/Error : Ill-formed result from local Cgen/testing driver code!~|")
           (mv T cgen-state state)))
         
         ((list stop? test-outcomes% gcs%) res)
         ((mv end state) (acl2::read-run-time state))
         (cgen-state (update-cgen-state)))
      (value cgen-state))))
       
 
 ;TODO im losing testing summary here!

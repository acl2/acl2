#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "acl2s-parameter")
(include-book "utilities")
(include-book "basis")

(defrec gcs% 
; global-coverage-stats 
; Only accumulates sound and top-reproducible cts/wts
; i.e is not modified after a cross-fertilize ledge of the waterfall
  ((runs dups . vacs)
   (cts . wts))
  NIL)


(defconst *initial-gcs%* (acl2::make gcs% :cts 0 :wts 0 :runs 0 :vacs 0 :dups 0))

(defconst *gcs-fields* '(cts wts runs dups vacs))
(defun gcs%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (;layout exposed in main.lisp/print-testing-summary-fn
     ('gcs% (runs dups . vacs)
            (cts . wts))
     (and (unsigned-29bits-p cts)
          (unsigned-29bits-p wts)
          (unsigned-29bits-p runs)
          (unsigned-29bits-p dups)
          (unsigned-29bits-p vacs)
          ))))

(defmacro gcs-1+ (fld-nm)
  `(change gcs% ,fld-nm
             (acl2::|1+F| (access gcs% ,fld-nm))))
                                   

(defconst *cgen-state-givens*  '(start-time user-supplied-term displayed-goal top-ctx params))
(defconst *cgen-state-derived* '(top-vt-alist))
(defconst *cgen-state-transient* '(gcs processor-hist s-hist stopping-condition-p proof-aborted-p end-time))
(defconst *cgen-state-fields* (append *cgen-state-transient* *cgen-state-givens* *cgen-state-derived*))

(defun cgen-state-p (v)
  (declare (xargs :guard T))
  (and (symbol-alistp v)
       ;(= (len v) 4) extensible
       (assoc-eq 'user-supplied-term v)
       (assoc-eq 'displayed-goal v)
       (assoc-eq 'start-time v)
       (assoc-eq 'params v)
       (symbol-alistp (cdr (assoc-eq 'params v)))
       (assoc-eq 'top-ctx v)
       (gcs%-p (cdr (assoc-eq 'gcs v)))
       ))

(defun cget-fn (key cgen-state)
  (declare (xargs :guard (and (cgen-state-p cgen-state)
                              (member-eq key *cgen-state-fields*))))
  (let ((entry (assoc-eq key cgen-state)))
    (if (consp entry)
        (cdr entry)
      nil)))

(defun cget-param-fn (key cgen-state)
  (declare (xargs ;:verify-guards nil
                  :guard (and (cgen-state-p cgen-state)
                              (acl2s::acl2s-parameter-p key))))
  (let* ((params (cget-fn 'params cgen-state))
         (entry (assoc-eq (acl2s::keywordify key) params)))
    (if (consp entry)
        (cdr entry)
      nil)))
  
(defmacro cget (key)
  "get value of key from cgen-state. if key is a param-key is acl2s-parameters,
then appropriately get the corresponding value stored in the param field of
cgen-state"
  (cond ((member-eq key *cgen-state-fields*)
         (list 'CGET-FN (kwote key) 'CGEN-STATE))
        ((acl2s::acl2s-parameter-p key)
         (list 'CGET-PARAM-FN (kwote key) 'CGEN-STATE))
        (t (er hard 'cget "~| Unsupported cgen-state field/key: ~x0~%" key))))

(defun cput-fn (key val cgen-state)
  (declare (xargs :guard (and (cgen-state-p cgen-state)
                              (member-eq key *cgen-state-fields*))))
  (put-assoc-eq key val cgen-state))

; prove the return type theorem -- will be hard... since its in alist form
(defmacro cput (key val)
  "put value into key entry of cgen-state (acl2s-parameter keys not allowed, unlike cget)"
  (list 'CPUT-FN (kwote key) val 'CGEN-STATE))


(defun var-p (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (not (or (keywordp x);a keyword
                (booleanp x);t or nil
                (legal-constantp x)))))

(defun var-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (var-p (car x))
           (var-listp (cdr x)))
    (null x)))

(defun var-alistp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (var-p (caar x))
           (var-alistp (cdr x)))
    (null x)))

; make this attachable
(defstub allowed-cgen-event-ctx-p (*) => *)
(defun allowed-cgen-event-ctx-p-no-defun (ctx)
  (declare (xargs :guard t))
  (cond ((equal ctx "( THM ...)") t)
        ;; Pete: added this test because callback.lisp has this call
        ;; (init-cgen-state/event (acl2s::acl2s-defaults-alist) start :undefined)
        ;; and the third arg to init-cgen-state/event is supposed to
        ;; satisfy allowed-cgen-event-ctx-p
        ((equal ctx :undefined) t)
        ((member-equal ctx '(ACL2::THM ACL2::DEFTHM ACL2::VERIFY-GUARDS)))
        ((and (consp ctx)
              (member-equal (car ctx) '(ACL2::DEFTHM ACL2::VERIFY-GUARDS))) t)
        ((and (consp ctx)
              (member-equal (car ctx) (list "( VERIFY-GUARDS ~x0)"))) t)
        (t nil)))
  
;; (defun allowed-cgen-event-ctx-p-with-defun (ctx)
;;   (cond ((equal ctx "( THM ...)") t)
;;         ((member-eq ctx '(ACL2::THM ACL2::DEFTHM ACL2::VERIFY-GUARDS ACL2::DEFUN ACL2::DEFUNS)))
;;         ((and (consp ctx)
;;               (member-eq (car ctx) '(ACL2::DEFTHM ACL2::VERIFY-GUARDS ACL2::DEFUN ACL2::DEFUNS))) t)
;;         ((and (consp ctx)
;;               (member-equal (car ctx) (list "( VERIFY-GUARDS ~x0)" "( DEFUNS ~x0)" ACL2::*MUTUAL-RECURSION-CTX-STRING*))) t)
;;         (t nil)))

(defattach allowed-cgen-event-ctx-p allowed-cgen-event-ctx-p-no-defun)

(defun cgen-params-p1 (v)
  "alist capturing key-value pair from acl2s-defaults-table"
  (declare (xargs :verify-guards nil :guard t))
   (b* (((acl2::assocs 
         ;cgen/testing parameters (keep in sync with acl2s-parameter)
          (num-trials :num-trials)
          (verbosity-level :verbosity-level)
          (num-counterexamples :num-counterexamples)
          (num-witnesses :num-witnesses)
          (sampling-method :sampling-method)
          (backtrack-limit :backtrack-limit)
          (search-strategy :search-strategy)
          (testing-enabled :testing-enabled)
          (cgen-local-timeout :cgen-local-timeout)
          (cgen-single-test-timeout :cgen-single-test-timeout)
          (print-cgen-summary :print-cgen-summary)
          (use-fixers :use-fixers)
          (recursively-fix :recursively-fix)
          (num-print-counterexamples :num-print-counterexamples)
          (num-print-witnesses :num-print-witnesses)
          
          ) v))
    (and (fixnump num-trials)
         (fixnump verbosity-level)
         (fixnump num-counterexamples)
         (fixnump num-witnesses)
         (member-eq sampling-method acl2s::*sampling-method-values*)
         (fixnump backtrack-limit)
         (member-eq search-strategy acl2s::*search-strategy-values*)
         (member-eq testing-enabled acl2s::*testing-enabled-values*)
         (rationalp cgen-local-timeout)
         (rationalp cgen-single-test-timeout)
         (booleanp print-cgen-summary)
         (booleanp use-fixers)
         (booleanp recursively-fix)
         (fixnump num-print-counterexamples)
         (fixnump num-print-witnesses)
        
         )))
         
(defun cgen-params-p (v)
  (declare (xargs :guard t))
  (ec-call (cgen-params-p1 v)))

; Data structure test-outcomes%

; statistics/results in run-tests. are accumulated in test-outcomes%
; cts is a list of counterexample assignments/value-bindings
; wts is a list of witness          " 
; vacs is a list of vacuous         "
; #dups is the number of duplicates encountered (but only in wts and cts [2015-04-07 Tue]) 
; [2015-04-07 Tue] vacs-hyp-vals-list is (listof (listof boolean))
(defrec test-outcomes% 
  ((|#cts| cts cts-hyp-vals-list) (|#wts| wts wts-hyp-vals-list) (|#vacs| vacs vacs-hyp-vals-list) |#dups| disp-enum-alist elim-bindings) ;[2016-04-25 Mon] record these too
  NIL)


(defun test-outcomes%-p (v)
  (declare (xargs :guard T))
  (case-match v ;internal layout hidden everywhere else
    (('test-outcomes% (|#cts| cts cts-hyp-vals-list) (|#wts| wts wts-hyp-vals-list) (|#vacs| vacs vacs-hyp-vals-list) |#dups| disp-enum-alist elim-bindings)
; symbol-doublet-list-listp is a list of assignments/value-bindings              
     (and (symbol-doublet-list-listp cts)
          (symbol-doublet-list-listp wts)
          (symbol-doublet-list-listp vacs)
          (true-list-listp cts-hyp-vals-list)
          (true-list-listp wts-hyp-vals-list)
          (true-list-listp vacs-hyp-vals-list)
          (unsigned-29bits-p |#wts|)
          (unsigned-29bits-p |#cts|)
          (unsigned-29bits-p |#vacs|)
          (unsigned-29bits-p |#dups|)
          (symbol-alistp disp-enum-alist)
          (alistp elim-bindings) ;elim-bindings is now a b* binding [2016-09-05 Mon]
          ))))
          

(defmacro test-outcomes-1+ (fld)
  "increments the number-valued fields of test-outcomes%"
  (declare (xargs :guard (member-eq fld '(cts wts vacs dups))))
  (let* ((fld-dc (string-downcase (symbol-name fld)))
         (fld-nm (acl2s::fix-intern-in-pkg-of-sym 
                  (concatenate-names (list "#" fld-dc)) 'test-outcomes%)))
    `(change test-outcomes% ,fld-nm
             (acl2::|1+F| (access test-outcomes% ,fld-nm)))))


;; records data that is later needed for printing stats/summary 
(defrec s-hist-entry% (test-outcomes 
                       (hyps vars . concl)
                       (elide-map) ;printing top-level cts/wts
                       (start-time . end-time) . name) NIL)

(defun s-hist-entry%-p (v)
  (declare (xargs :guard T))
  (case-match v ;internal layout hidden
    (('s-hist-entry% test-outcomes
                     (hyps vars . concl)
                     (elide-map)
                     (start-time . end-time) . name)
     (and (test-outcomes%-p test-outcomes)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-listp vars)
          (symbol-alistp elide-map) ;actually symbol term alist
          (stringp name)
          (rationalp start-time)
          (rationalp end-time)))))
          
  
(defun s-hist-p (v)
"is a alist mapping strings to s-hist-entry% records"
  (declare (xargs :guard T))
  (if (atom v)
      (null v)
    (and (consp (car v))
         (stringp (caar v))
         (s-hist-entry%-p (cdar v))
         (s-hist-p (cdr v)))))



(defun valid-cgen-state-p1 (v)
  (declare (xargs :verify-guards nil :guard T))
   (b* (((acl2::assocs 
; transient storage
         gcs ;global coverage stats
         processor-hist ;for all-bets-off?
         s-hist         ;subgoal testing history
         stopping-condition-p
         proof-aborted-p ;TODO
;given by user
         start-time     
         ;;end-time ;leave to end
         user-supplied-term
         displayed-goal
         top-ctx ; either ctx is user-defined or comes from event form, but updated to callback ctx
         params ;it is an alist form of acl2s-defaults table
;derived          
         top-vt-alist ;dumb var-type alist inferred
         ) 
        v))

    (and (gcs%-p gcs)
         (subsetp-eq processor-hist acl2::*preprocess-clause-ledge*)
         (s-hist-p s-hist)
         (booleanp stopping-condition-p)
         (booleanp proof-aborted-p)

         (rationalp start-time)
         ;(rationalp end-time)
         (pseudo-termp user-supplied-term)
         (not (eq :undefined displayed-goal))
         (or (member-eq top-ctx '(:user-defined test?))
             (not (null top-ctx))); (allowed-cgen-event-ctx-p top-ctx))
         (cgen-params-p params)

         (var-alistp top-vt-alist)
         )))

(defun valid-cgen-state-p (v)
  (declare (xargs :guard T))
  (ec-call (valid-cgen-state-p1 v)))

  

(encapsulate
  ((stopping-condition? 
    (gcs% nc nw) t
    :guard (and (gcs%-p gcs%)
                (natp nc)
                (natp nw))))
  (local (defun stopping-condition? (x y z) (list x y z))))


;TODO -- this is in inner loop, make it more efficient.
(defun stopping-condition?-builtin (gcs% num-cts num-wts)
  (declare (xargs :guard (and (natp num-cts)
                              (natp num-wts)
                              (gcs%-p gcs%))))
  (and (>= (access gcs% cts) (nfix num-cts))
       (>= (access gcs% wts) (nfix num-wts))))

;; (defun stopping-condition?-builtin-gv (gcs% num-cts num-wts)
;;   (declare (xargs :guard T))
;;   (ec-call (stopping-condition?-builtin cgen-state)))

(defattach stopping-condition? stopping-condition?-builtin)

(table cgen::builtin-relations nil
       '((:member . (member-equal member-eq member))
         (:assoc . (assoc-equal assoc assoc-eq assoc-eql))
         (:equal . (=  equal eq eql int= string-equal hons-equal))
         (:less . (< <=))
         (:greater . (> >=)))
       :clear)

(defun membership-relationp (R wrld) ;TODO clean this up
  (or (member-equal R '(acl2::member-eq acl2::member acl2::member-eql acl2::member-equal acl2s::in |ACL2S B|::in))
      (b* ((br-tbl (table-alist 'cgen::builtin-relations wrld))
           (mem-relations (get1 :member br-tbl)))
        (member-equal R mem-relations))))

(defun add-builtin-relation (key R wrld)
  (b* ((br-tbl (table-alist 'cgen::builtin-relations wrld))
       (relations (get1 key br-tbl))
       (new-val (append relations (list R))))
    new-val))
      
(defmacro add-member-builtin-relation (R)
  `(table cgen::builtin-relations :member (add-builtin-relation :member ',R acl2::world) :put))


; [2016-04-03 Sun] Added placeholder for fixer-arrangement which gives back a
; fixer/elim-binding as a b*-binding that can be used in simple-search
(defstub fixer-arrangement (* * * *  state) => (mv * * state))
(defun fixer-arrangement/dummy (hyps concl vl ctx state)
  (declare (ignore hyps concl vl ctx))
  (declare (xargs :stobjs (state)))
  (mv nil (list nil nil) state))
(defattach (fixer-arrangement fixer-arrangement/dummy))

; [2017-08-17 Thu] This can be either attached to a gl backend or a greedy algo.
(defstub fxri-let*-soln (* * * * * state) => (mv * * state))
(defun fxri-let*-soln/dummy (flits term->f-lits-lst relevant-terms fxri{} vl state)
  (declare (ignore flits term->f-lits-lst relevant-terms fxri{} vl))
  (declare (xargs :stobjs (state)))
  (mv nil (list nil nil) state))
(defattach (fxri-let*-soln fxri-let*-soln/dummy))



; other basic functionality

;The following 2 function only look at the outermost implies form
;get hypothesis from acl2 term being proved.
(defun get-hyp (form)
  (declare (xargs :guard t))
  (if (atom form)
    t;no hyps is equivalent to true
    (if (and (consp (cdr form))
             (eq 'implies (first form)))
      (second form)
      t)));;no hyps is equivalent to true

; use expand-assumptions-1 instead when you have a term
(defun get-hyps (pform)
  (declare (xargs :guard t))
  (b* ((hyp (get-hyp pform))
       ((when (eq hyp 't)) nil)
       ((unless (and (consp hyp)
                     (consp (cdr hyp))
                     (eq (car hyp) 'and)))
        (list hyp))
       (rst (cdr hyp)))
    rst))


;get conclusion from acl2 term being proved
(defun get-concl (form)
  (declare (xargs :guard t))
  (if (atom form)
    form
    (if (and (consp (cdr form))
             (consp (cddr form))
             (eq 'implies (first form)))
      (third form)
      form)))

(program)

(mutual-recursion
 (defun strip-return-last (term)
   (declare (xargs :verify-guards nil :guard (pseudo-termp term)))
   (cond ((acl2::variablep term) term)
         ((acl2::fquotep term) term)
         ((eq (acl2::ffn-symb term) 'acl2::hide) term)
         (t
          (let* ((stripped-args (strip-return-last-lst (fargs term)))
                 (fn (acl2::ffn-symb term)))
               
            (cond ((eq fn 'ACL2::RETURN-LAST) ;get rid return-last
                   (car (last stripped-args)))
                  (t (acl2::cons-term fn stripped-args)))))))

(defun strip-return-last-lst (term-lst)
  (declare (xargs :guard (pseudo-term-listp term-lst)))
  (cond ((endp term-lst) '())
        (t (cons (strip-return-last (car term-lst))
                 (strip-return-last-lst (cdr term-lst))))))

 )


(mutual-recursion
 (defun strip-force (term)
   (declare (xargs :verify-guards nil :guard (pseudo-termp term)))
   (cond ((acl2::variablep term) term)
         ((acl2::fquotep term) term)
         ((eq (acl2::ffn-symb term) 'acl2::hide) term)
         (t
          (let* ((stripped-args (strip-force-lst (fargs term)))
                 (fn (acl2::ffn-symb term)))
               
            (cond ((eq fn 'ACL2::FORCE) ;get rid force
                   (first stripped-args))
                  (t (acl2::cons-term fn stripped-args)))))))

(defun strip-force-lst (term-lst)
  (declare (xargs :guard (pseudo-term-listp term-lst)))
  (cond ((endp term-lst) '())
        (t (cons (strip-force (car term-lst))
                 (strip-force-lst (cdr term-lst))))))

 )

(defun orient-equality (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term) 
           (member-eq (car term) '(EQUAL EQ EQL =))
           (consp (cdr term)) (consp (cddr term))
           (variablep (third term)))
      (list (first term) (third term) (second term))
    term))

(include-book "../defdata/defdata-util")

(u::defloop orient-equalities (terms)
  (for ((term in terms)) (collect (orient-equality term))))
      
(defun partition-hyps-concl (term str state)
  (declare (xargs :stobjs (state)))
  ;; (decl :mode :program
  ;;       :sig ((pseudo-termp stringp state) -> (mv pseudo-term-listp pseudo-termp state))
  ;;       :doc "expand lambdas,strip return-last, extracts hyps and concl from term")
;expensive operation
  ;; get rid of lambdas i.e let/let*
  (b* ((term  (defdata::expand-lambda term))
       (wrld (w state))
       (pform (acl2::prettyify-clause (list term) nil wrld))
       ((mv phyps pconcl)  (mv (get-hyps pform) (get-concl pform)))
       
       ((er hyps) (acl2::translate-term-lst phyps 
                                            t nil t str wrld state))
       ((er concl) (acl2::translate pconcl t nil t str wrld state)))
    (mv hyps concl state)))

(defun partition-into-hyps-concl-and-preprocess (term str state)
  (declare (xargs :stobjs (state)))
  ;; (decl :mode :program
  ;;       :sig ((pseudo-termp stringp state) -> (mv pseudo-term-listp pseudo-termp state))
  ;;       :doc "expand lambdas,strip return-last, extracts hyps and concl from term")
;expensive operation
  ;; get rid of lambdas i.e let/let*
  (b* ((term  (defdata::expand-lambda term))
       (wrld (w state))
       (pform (acl2::prettyify-clause (list term) nil wrld))
       ((mv phyps pconcl)  (mv (get-hyps pform) (get-concl pform)))
       
       ((er hyps) (acl2::translate-term-lst phyps 
                                            t nil t str wrld state))
       ((er concl) (acl2::translate pconcl t nil t str wrld state))
       (hyps (strip-return-last-lst hyps))
       (hyps (strip-force-lst hyps))
       (concl (strip-return-last concl))
       (concl (strip-force concl))
       (hyps (orient-equalities hyps))
       (concl (orient-equality concl))
       )
    (mv hyps concl state)))

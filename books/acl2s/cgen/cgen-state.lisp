#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


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
          (print-cgen-summary :print-cgen-summary)
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
         (booleanp print-cgen-summary))))
         
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
  ((|#cts| cts cts-hyp-vals-list) (|#wts| wts wts-hyp-vals-list) (|#vacs| vacs vacs-hyp-vals-list) . |#dups|)
  NIL)


(defun test-outcomes%-p (v)
  (declare (xargs :guard T))
  (case-match v ;internal layout hidden everywhere else
    (('test-outcomes% (|#cts| cts cts-hyp-vals-list) (|#wts| wts wts-hyp-vals-list) (|#vacs| vacs vacs-hyp-vals-list) . |#dups|)
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
          (unsigned-29bits-p |#dups|)))))
          

(defmacro test-outcomes-1+ (fld)
  "increments the number-valued fields of test-outcomes%"
  (declare (xargs :guard (member-eq fld '(cts wts vacs dups))))
  (let* ((fld-dc (string-downcase (symbol-name fld)))
         (fld-nm (intern-in-package-of-symbol 
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
         top-ctx ; either ctx is user-defined or comes from event form
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
             (allowed-cgen-event-ctx-p top-ctx))
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

(defun membership-relationp (R) ;TODO make this more general
  (member-equal R '(acl2::member-eq acl2::member acl2::member-eql acl2::member-equal acl2s::in |ACL2S B|::in)))


#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "basis")

(include-book "type")

(include-book "acl2s-parameter")
(include-book "simple-graph-array")
(include-book "../defdata/random-state")
(include-book "build-enumcalls")
(include-book "with-timeout" :ttags ((:acl2s-timeout)))


(set-state-ok t)


;;;; * Main Idea
;;;; Given any formula, we want to test it using test? or
;;;; amidst a prove call.  By test it, I mean we search for an
;;;; instantiation (or assignment) of the free variables in the
;;;; formula *and* evaluate the ground formula resulting from
;;;; substituting the assignment.  The way 'Cgen' (name of our
;;;; implementation) works is as follows. We set up the type
;;;; infrastructure, i.e we store type meta data in ACL2 tables for
;;;; all primitive/basic types in ground ACL2 and provide the user
;;;; with macros (defdata) to introduce new types. These macros
;;;; automate maintenance of type meta data. The metadata henceforth
;;;; called defdata tables, store the enumerators for each type
;;;; predicate, and also capture the relationship (subtype and
;;;; disjoint) among the different types. The latter are useful in
;;;; finding the minimal (possible) type information for a variable
;;;; constrained by multiple predicates/relations. When we say 'type',
;;;; we refer to a name that characterizes a set in the ACL2
;;;; Universe. This 'type' is characterized redundantly both with a
;;;; predicate and an enumerator. When the user asks
;;;; to test?/thm a conjecture, Cgen queries the defdata tables to
;;;; obtain the name of the corresponding enumerator for each variable
;;;; constrained by a monadic predicate in the conjecture.  In
;;;; practice what Cgen derives is not an enumerator function but an
;;;; enumerat(or/ing) expression with holes. When these holes are filled
;;;; with random natural numbers, it will evaluate to a random value
;;;; satisfying the type-like constraints of the concerned
;;;; variable in the conjecture under test. Also in practice there is
;;;; dependency among variables and naively instantiating all of them
;;;; independently will lead to poor test data, since the full
;;;; assignment might turn out to be vacuous (inconsistent hypotheses)
;;;; many a time. (And this indeed is the main hurdle to be crossed).
;;;; 
;;;; Clearly to obtain the best results, we want to be able to do the
;;;; following things.
;;;; 1. Derive an enumerator expression for each variable that
;;;; evaluates to a minimal set of values, the variable is allowed to
;;;; take.
;;;; 2. Derive an enumerator expression for each
;;;; variable that takes into account its dependency on other
;;;; variables. i.e If (= x (f y)) and (posp y), then enumerator
;;;; expression call (enumcall) for y is (nth-pos n) and for x it is
;;;; simply (f y). Thus x never evaluates to a value that would make
;;;; its constraint inconsistent. Things are more complicated for
;;;; mutually-dependent variables and for complex dependency
;;;; relations. 
;;;; 
;;;; Feb 3 2012
;;;; This is basically a constraint satisfaction problem and there exist
;;;; naive backtracking algorithms for finite-domain variables. There also
;;;; exists the notion of arc-consistency, which basically tells you if it
;;;; is possible to extend an partial assignment without backtracking. So
;;;; the "ideal scenario" is to construct the assignment without backtracking.

;;;; Right now, in one search strategy, which is named "simple", we
;;;; simply compute enumerator/type expressions for all free
;;;; variables, taking into account "equality" dependencies and use
;;;; this as a template code to plug in random natural numbers or
;;;; bounded consecutive natural number tuples to obtain either random
;;;; value assignment or a consecutive value assignment in the bounded
;;;; value space of free variables. 

;;;; Alternatively, in the DPLL-style search strategy, which we named
;;;; as "incremental", we incrementally build the assignment, taking
;;;; into account dependency, by selecting the least "dependent"
;;;; variable in the dependency graph built from the conjecture. After
;;;; every variable is assigned a new value (satisfying its local type
;;;; constraints), this information is propagated using the theorem
;;;; prover itself. If the resulting hypotheses of the partially
;;;; instantiated conjecture are contradictory/inconsistent, then we
;;;; backtrack to the last "decision" Assign. We stop when we either
;;;; backtrack too many times, or we have obtained the full value
;;;; assignment (called sigma hereafter).

;;;; The following illustrates the top-level driver pseudocode

;;;; Top-level test driver loop for Conjecture/Subgoal G
;;;; All type alists below have as keys the free variables of G.

;;;; Initialization code:
;;;; defattach conclusion-val/hypotheses-val for G
;;;; T_naive := get naive type alist from defdata tables for G
;;;; T_ACL2  := get ACL2 type alist for freevars(G)
;;;; T_final := get type expression alist for freevars(G) using
;;;;            T_naive, T_ACL2 and the dependency graph of G.
;;;; E := get enumerator expression alist for G using T_final
;;;; make defun next-sigma using E and random seed, BE arg tuple
;;;; defattach next-sigma to a fun computing assignments
;;;;   
;;;;
;;;; Driver loop code:
;;;; repeat *num-trial* times or till we meet stopping condition
;;;; \sigma := (next-sigma ...)
;;;;   if (hypotheses-val \sigma)
;;;;      if (conclusion-val \sigma)
;;;;         record witness 
;;;;       record counterexample
;;;;    record vacuous
;;;; end
;;;;
;;;; conclusion-val and hypotheses-val are stub functions which
;;;; are attached during the main search function.
;;;; They take a substitution and apply it to G, returning a boolean.

;;;;harshrc
;;;;10th Jan 2012 (Tuesday)

;;; Purpose: Given a value substitution, the following functions will
;;; apply it to the hypotheses and conclusion of the conjecture under
;;; test and compute the value of the resulting ground formula.
;;; Sig: sigma -> boolean
;;; where sigma is the let bindings or simply the binding of free variables to
;;; values satisfying the "types" of the respective variables.
;(defstub hypotheses-val (*) => *)
(encapsulate
  ((hypotheses-val
    (A) t
    :guard (symbol-doublet-listp A)))
 
  (local (defun hypotheses-val (A) (list A))))



;(defstub conclusion-val (*) => *)
(encapsulate
  ((conclusion-val
    (A) t
    :guard (symbol-doublet-listp A)))
 
  (local (defun conclusion-val (A) (list A))))

;;; Purpose: For the current ... , generate the next value-alist
;;; (sigma) for the formula under test.  next-sigma : (sampling-method
;;; seed tuple) ->  seed' * tuple' * A' Given the sampling method,
;;; current random seed, the current nth-tuple (of nats), it computes
;;; the full assignment (sigma) to be used in the upcoming test run
;;; and also returns the updated seed and updated nth-tuple
(defstub next-sigma (* * *) => (mv * * *))


(def single-hypothesis (hyp-list)
  (decl :sig ((pseudo-term-list) -> (oneof 'T pseudo-term))
        :doc
"?: Transform a list of hypotheses into an equivalent hypothesis
 eg: (single-hypothesis '((posp x) (stringp s))) ==> (and (posp x) (stringp s))
     (single-hypothesis '()) ==> T")
  (if (endp hyp-list)
    't
    `(and ,@hyp-list)))


(def make-let-binding-for-sigma (vs sigma-symbol)
  (decl :sig ((symbol-list symbol) -> symbol-doublet-listp)
        :doc 
"(make-let-binding-for-sigma '(x y) 'A) => ((x (get-val x A))
                                            (y (get-val y A)))
")
  (if (endp vs)
      '()
    (cons `(,(first vs) (cadr (assoc-eq ',(first vs) ,sigma-symbol)))
          (make-let-binding-for-sigma (cdr vs) sigma-symbol))))



(defs 
  (mv-list-ify (term mv-sig-alist)
    (decl :sig ((pseudo-term symbol-list) -> pseudo-term)
          :doc "wrap all mv fn calls with mv-list")
    (if (variablep term)
      term
      (if (fquotep term)
        term
      (b* ((fn (ffn-symb term))
           (args (fargs term))
           (A mv-sig-alist)
           (entry (assoc-eq fn A))
           ((unless entry)
            (acl2::cons-term fn
                       (mv-list-ify-lst args A)))
           ((cons fn m) entry)) 
;m is output arity and should be greater than 1.
        (acl2::cons-term 'acl2::mv-list
                   (list (kwote m)
                         (acl2::cons-term fn (mv-list-ify-lst args A))))))))

  (mv-list-ify-lst (terms mv-sig-alist)
   (decl :sig ((pseudo-term-list symbol-list) -> pseudo-term-list))
   (if (endp terms)
       '()
     (cons (mv-list-ify (car terms) mv-sig-alist)
           (mv-list-ify-lst (cdr terms) mv-sig-alist)))))


; 9th Nov '13 -- stupid bug. I recently fixed -gv function to have
; :verify-guards t, so that even in the presence of
; set-verify-guards-eagerness 0, but in program mode, or if
; hypotheses-val-current has a program mode function, then the pair
; :verify-guards t is not allowed.
(def make-hypotheses-val-defuns (terms ord-vars mv-sig-alist programp)
  (decl :sig ((pseudo-term-list symbol-list symbol-alist boolean) -> all)
        :doc "make the defun forms for hypotheses-val defstub")
  `((defun hypotheses-val-current (A)
      (declare (ignorable A))
      (declare (xargs :verify-guards nil :normalize nil
                      :guard (symbol-doublet-listp A)))
      (let ,(make-let-binding-for-sigma ord-vars 'A)
        (declare (ignorable ,@ord-vars))
          ,(mv-list-ify (single-hypothesis terms)
                        mv-sig-alist)))
    (defun hypotheses-val-current-gv (A)
      (declare (xargs :guard T :verify-guards ,(not programp)))
      (ec-call (hypotheses-val-current A)))))

(def make-conclusion-val-defuns (term ord-vars mv-sig-alist programp)
  (decl :sig ((pseudo-term symbol-list symbol-alist boolean) -> all)
        :doc "make the defun forms for conclusion-val defstub")
  `((defun conclusion-val-current (A)
      (declare (ignorable A))
      (declare (xargs :verify-guards nil :normalize nil
                      :guard (symbol-doublet-listp A)))
      (let ,(make-let-binding-for-sigma ord-vars 'A)
        (declare (ignorable ,@ord-vars))
          ,(mv-list-ify term mv-sig-alist)))
    (defun conclusion-val-current-gv (A)
      (declare (xargs :guard T :verify-guards ,(not programp)))
      (ec-call (conclusion-val-current A)))))

;add the following for guard verif
(defthm symbol-doublet-listp-=>-symbol-alistp
  (implies (symbol-doublet-listp x)
           (symbol-alistp x))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 1)
                 ))



;;; [2015-04-07 Tue]  
;;; collect stats about which hyps failed to satisfy.
(encapsulate
  ((hyp-val-list
    (A) t
    :guard (symbol-doublet-listp A)))
 
  (local (defun hyp-val-list (A) A)))


(def make-hyp-val-list-defuns (terms ord-vars mv-sig-alist programp)
  (decl :sig ((pseudo-term-list symbol-list symbol-alist boolean) -> all)
        :doc "make the defun forms for hyp-val-list defstub")
  `((defun hyp-val-list-current (A)
      (declare (ignorable A))
      (declare (xargs :verify-guards nil :normalize nil
                      :guard (symbol-doublet-listp A)))
      (let ,(make-let-binding-for-sigma ord-vars 'A)
        (declare (ignorable ,@ord-vars))
          ,(mv-list-ify (cons 'LIST terms)
                        mv-sig-alist)))
    (defun hyp-val-list-current-gv (A)
      (declare (xargs :guard T :verify-guards ,(not programp)))
      (ec-call (hyp-val-list-current A)))))




(set-verify-guards-eagerness 2)
(defconst *sampling-method-values* '(:random :uniform-random :be :mixed)) ;redundant if not for package diff

(defun local-sampling-method-builtin (sampling-method i N)
  (declare (xargs :guard (and (natp N)
                              (natp i)
                              (member-eq sampling-method *sampling-method-values*)
                              (<= i N))))
  (b* (((unless (eq :mixed sampling-method))
        sampling-method))

    (cond ((zp N) :random)
          ((< (/ i N) (/ 50 100))
; first half do bounded-exhaustive testing, then switch to random testing
           :be)
          (t :random))))

(encapsulate
  ((local-sampling-method 
    (s i N) t
    :guard (and (member-eq s *sampling-method-values*)
                (natp i) (natp N) (<= i N))))
  
  (local (defun local-sampling-method (s i N) (list s i N))))

(defattach (local-sampling-method local-sampling-method-builtin))


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
         (entry (assoc-eq (defdata::keywordify key) params)))
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
  (cond ((equal ctx "( THM ...)") t)
        ((member-eq ctx '(ACL2::THM ACL2::DEFTHM ACL2::VERIFY-GUARDS)))
        ((and (consp ctx)
              (member-eq (car ctx) '(ACL2::DEFTHM ACL2::VERIFY-GUARDS))) t)
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
         (member-eq sampling-method *sampling-method-values*)
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


(set-verify-guards-eagerness 1)

(def run-single-test. (vl sampling-method N i r. BE.)
  (decl 
        :sig ((fixnum keyword fixnum fixnum fixnum symbol-fixnum-alist) 
              -> 
              (mv keyword true-listp symbol-doublet-listp fixnum symbol-fixnum-alist))
        :doc 
"?:
* Synopsis 
Run single trial of search for cts/wts for the formula under test.

* Input parameters 
vl is verbosity-level.
'N' stands for num-trials.  sampling-method is
itself.  i is the current local-trial number.  'r.' is the current
pseudo-random seed.  'BE.' is alist that holds previous
bounded-exhaustive nat arg seeds used to compute sigma.

* Return sig: (mv res hyp-vals A r. BE.)
A is computed sigma (value binding) used to test this run
hyp-vals is the list of boolean values for each of hyps under A
res is :vacuous if the hypotheses were inconsistent under A
res is :witness if both conclusion and hyps eval to T under A
else is :counterexample
r. is updated pseudo-random seed
BE. is the updated bounded-exhaustive arg/seed alist.

eg:n/a")
  
  (b* ((sm (local-sampling-method sampling-method i N))
       ((mv A r. BE.) (next-sigma sm r. BE.))
       (- (cw? (system-debug-flag vl) 
               "~|CEgen/Sysdebug/run-single: A: ~x0 seed: ~x1~%" A r.))
       (|not vacuous ?|  (hypotheses-val A))
       (hyp-vals (and (verbose-stats-flag vl) (hyp-val-list A)))

       (- (cw? (and (system-debug-flag vl)
                    (not |not vacuous ?|)) 
               "~|CEgen/Sysdebug/run-single: hyp-vals : ~x0~%" hyp-vals))
       )
;  in
   (if |not vacuous ?|
       ;; bugfix: why even try to evaluate conclusion when
       ;; the hypotheses arnt satisfied, the whole form's value
       ;; is simply true - May 2nd '12
       (let ((res (if (conclusion-val A) :witness :counterexample)))
        (mv res hyp-vals A r. BE.))
     (mv :vacuous hyp-vals A r. BE.))))





; sort utility for use in record-testrun.
(defun merge-car-symbol-< (l1 l2)
  (declare (xargs :measure (+ (acl2-count l1) (acl2-count l2))))
                    (cond ((endp l1) l2)
                          ((endp l2) l1)
                          ((symbol-< (car (car l1)) (car (car l2)))
                           (cons (car l1)
                                 (merge-car-symbol-< (cdr l1) l2)))
                          (t (cons (car l2)
                                   (merge-car-symbol-< l1 (cdr l2))))))

(defthm acl2-count-evens-strong
  (implies (and (consp x)
                (consp (cdr x)))
           (< (acl2-count (evens x)) (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-evens-weak
  (<= (acl2-count (evens x)) (acl2-count x))
  :hints (("Goal" :induct (evens x)))
  :rule-classes :linear)


(defun merge-sort-car-symbol-< (l)
  (cond ((endp (cdr l)) l)
        (t (merge-car-symbol-< (merge-sort-car-symbol-< (evens l))
                               (merge-sort-car-symbol-< (odds l))))))

; TODO: This function is in the inner loop. See if it can be furthur
; optimized.
(def record-testrun. (test-result hyp-vals A num-cts num-wts vl test-outcomes% gcs%)
  (decl :sig ((keyword true-listp symbol-doublet-listp fixnum fixnum fixnum test-outcomes%-p gcs%-p)
              ->
              (mv test-outcomes%-p gcs%-p))
        :doc 
"?: records (accumulates) the outcome of a single test trial run ")
  (b* ((A (merge-sort-car-symbol-< A))
       (gcs% (gcs-1+ runs)))
;   in
    (case test-result
      (:counterexample   (b* ((A-cts (access test-outcomes% cts))
                             
                             ((when (member-equal A A-cts))
                              (mv (test-outcomes-1+ dups) (gcs-1+ dups)));ignore A
                                                                                       
                             (gcs% (gcs-1+ cts))
                             (m    (access test-outcomes% |#cts|))
                             (test-outcomes% ;TODO:per subgoal num-cts stored??
                              (if (< m num-cts) ;dont store extra unless
                                  (b* ((test-outcomes% (change test-outcomes% cts (cons A A-cts)))
                                       (test-outcomes% (change test-outcomes% cts-hyp-vals-list
                                                               (cons hyp-vals (access test-outcomes% cts-hyp-vals-list)))))
                                    test-outcomes%)
                                test-outcomes%))
                             (test-outcomes%   (test-outcomes-1+ cts)))
;                              in
                         (mv test-outcomes% gcs%)))


      (:witness          (b* ((A-wts (access test-outcomes% wts))
                             ((when (member-equal A A-wts))
                              (mv (test-outcomes-1+ dups) (gcs-1+ dups)))
                             
                             (gcs% (gcs-1+ wts))
                             (m    (access test-outcomes% |#wts|))
                             (test-outcomes%   
                              (if (< m num-wts)
                                  (b* ((test-outcomes% (change test-outcomes% wts (cons A A-wts)))
                                       (test-outcomes% (change test-outcomes% wts-hyp-vals-list
                                                               (cons hyp-vals (access test-outcomes% wts-hyp-vals-list)))))
                                    test-outcomes%)
                                test-outcomes%))
                             (test-outcomes%   (test-outcomes-1+ wts)))
;                         in       
                          (mv test-outcomes% gcs%)))

                                             
      (:vacuous          (b* ((A-vacs (access test-outcomes% vacs))

                              ;; ((when (member-equal A A-vacs)) ;costly -- commenting out ;; this makes #dups inconsistent
                              ;; (mv ( test-outcomes-1+ dups) (gcs-1+ dups)))

                             (test-outcomes% 
                              (if (verbose-stats-flag vl)
                                  (change test-outcomes% vacs-hyp-vals-list
                                          (cons hyp-vals (access test-outcomes% vacs-hyp-vals-list)))
                                test-outcomes%))
                             
                             (gcs% (gcs-1+ vacs))
                             (m    (access test-outcomes% |#vacs|))
                             (test-outcomes%   
                              (if (or (< m (acl2::+f num-wts num-cts))
                                      (verbose-stats-flag vl)) ;[2015-04-07 Tue]

; TODO: [2014-04-26 Sat] To (post-) diagnose vacuous tests, we ought
; to store or at least provide a way to do on-the-fly
; diagnosis. Provide a hook here?
                                  (change test-outcomes% vacs (cons A A-vacs))
                                test-outcomes%))
                             (test-outcomes%   (test-outcomes-1+ vacs)))
;                         in
                          (mv test-outcomes% gcs%)))
      (otherwise         (prog2$ (er hard 'test? "not possible") 
                                 (mv test-outcomes% gcs%))))))


(def run-n-tests. (n num-trials sm vl num-cts num-wts 
                     r. BE. 
                     test-outcomes% gcs%)
  (decl :sig ((fixnum fixnum keyword fixnum fixnum fixnum 
                      fixnum symbol-fixnum-alist 
                      test-outcomes% gcs%)
              -> (mv boolean fixnum symbol-fixnum-alist 
                     test-outcomes% gcs%))
        :doc
"?: 
* Synopsis
  Run 'n' remaining tests on the formula under consideration.

* Input parameters 
   n is num-trials minus current local-trial number.
   r.  is the current pseudo-random seed.
   BE. is alist mapping variables to bounded-exhaustive seeds used in last instantiation
   num-trials (the current cgen default)
   sm is sampling-method (the current cgen default)
   vl is verbosity-level (the current cgen default)
   num-cts is num-counterexamples (the current cgen default)
   num-wts is num-witnesses (the current cgen default)
   test-outcomes% stores testrun results.
   gcs% is the global/top-level (testing) coverage statistics.

* Returns: (mv stop? r. BE. test-outcomes% gcs%)
where
  stop? is T when stopping-condition? call is satisfied
  r. is updated pseudo-random seed
  BE. is the updated alist of bounded-exhaustive seeds
  test-outcomes% is the updated testrun results
  gcs% is the updated global coverage stats.
")
  (b* (((when (zpf n)) ;Oops, ran out of random trials
        (mv NIL r. test-outcomes% gcs%))
       ((when (stopping-condition? gcs% num-cts num-wts))
;return, cos we have reached our goal  
         (mv T r. test-outcomes% gcs%))

       (local-trial-num  (acl2::|1+F| (acl2::-f num-trials n)))
       ((mv res hyp-vals A r. BE.) ; res = test value  A= value-bindings
        (run-single-test. vl sm num-trials local-trial-num  r. BE.))
       ((mv test-outcomes% gcs%) (record-testrun. res hyp-vals A num-cts num-wts vl test-outcomes% gcs%))
       (- (cw? (system-debug-flag vl) 
               "~|CEgen/Sysdebug/run-n-tests: Finished run n: ~x0 -- got ~x1~|" n res)))
;  in   
   (run-n-tests. (acl2::|1-F| n) num-trials sm vl num-cts num-wts 
                 r. BE. 
                 test-outcomes% gcs%)))

          


;; Pre Condition: hypothesis-val, conclusion-val and next-sigma have been
;; attached when this function is called!
(def run-tests. (N sm vl num-cts num-wts 
                   rseed. BE. 
                   test-outcomes% gcs%)
  (decl :sig ((fixnump keywordp fixnump fixnum fixnum 
                       fixnump symbol-fixnum-alistp 
                       test-outcomes%-p gcs%-p) 
              -> (mv boolean fixnum test-outcomes% gcs%))
        ;:trace T
        :doc 
"?: Run a bunch of simple random/bounded-exhaustive tests/trials to
  find cts/wts for formula under test")
;do timeout wrapper here!        
  (b* (((mv stop? rseed. test-outcomes% gcs%)
        (run-n-tests. N N
                      sm vl num-cts num-wts
                      rseed. BE.
                      test-outcomes% gcs%))
       
       (- (cw? (system-debug-flag vl) 
               "~|CEgen/Sysdebug/run-tests.: test-outcomes%: ~x0 ~|gcs%: ~x1~%" test-outcomes% gcs%)))
   ;;in
    (mv stop? rseed. test-outcomes% gcs%)))
         
          
         


(def separate-const/simple-hyps. (ts wrld Hc. Hs. Ho.)
  (decl :sig ((pseudo-term-list plist-world 
               pseudo-term-list pseudo-term-list pseudo-term-list) 
              -> (mv pseudo-term-list pseudo-term-list pseudo-term-list))
        :doc "given a list of hyps, separate constant hyps, simple defdata-type hyps and others")
  (f* ((add-others-and-recurse... () (separate-const/simple-hyps. 
                                      rst wrld Hc. Hs. (cons hyp Ho.)))
       (add-constant-and-recurse (h) (separate-const/simple-hyps.
                                      rst wrld (cons h Hc.) Hs. Ho.)))
  (if (endp ts)
      (mv Hc. Hs. Ho.)
    
    (b* (((cons hyp rst) ts))
    (case-match hyp
      ((P t1)     (if (and (symbolp t1)
                           (defdata::is-type-predicate P wrld))
                      (separate-const/simple-hyps. rst wrld 
                                                   Hc. (cons hyp Hs.) Ho.)
                    (add-others-and-recurse...)))
                          
      ((R t1 t2)  (if (acl2::equivalence-relationp R wrld)
                      (cond ((and (symbolp t1) (quotep t2))
                             (add-constant-and-recurse (list R t1 t2)))
                            
                            ((and (quotep t1) (symbolp t2))
                             (add-constant-and-recurse (list R t2 t1)))
                            
                            (t (add-others-and-recurse...)))
                    (add-others-and-recurse...)))
      (&          (add-others-and-recurse...)))))))



(defun membership-relationp (R) ;TODO make this more general
  (member-equal R '(acl2::member-eq acl2::member acl2::member-eql acl2::member-equal)))


;identify (equal x y)
(defun equiv-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql));TODO
       (proper-symbolp (second hyp))
       (proper-symbolp (third hyp))))


(mutual-recursion
(defun possible-constant-value-expressionp-lst (expr-lst)
  (if (atom expr-lst)
    t
    (and (possible-constant-value-expressionp (car expr-lst))
         (possible-constant-value-expressionp-lst (cdr expr-lst)))))

(defun possible-constant-value-expressionp (expr)
   (cond ((null expr) t);if nil
         ((defdata::possible-constant-value-p expr) t); if a constant
         ((atom expr) (defdata::possible-constant-value-p expr));if an atom, it has to go through this
         ((not (symbolp (car expr))) nil)
         (t (possible-constant-value-expressionp-lst (cdr expr))))
   )
)

;identify (equal 3 x) or (equal x 42)
(defun constant-hyp? (hyp)
  (and (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql))
       (or (and (proper-symbolp (second hyp))
                (possible-constant-value-expressionp (third hyp)))
           (and (proper-symbolp (third hyp))
                (possible-constant-value-expressionp (second hyp))))))

;chyp=(equal x <const>) or (equal <const> x)
;gives (mv x <const>)
(defun destruct-simple-hyp (chyp)
  (if (proper-symbolp (second chyp))
      (mv (second chyp) (third chyp))
    (mv (third chyp) (second chyp))))

;identify (equal x expr) or (equal expr y) where expr is not a const expr
;disjoint with constant-hyp? and equiv-hyp?
;added an extra argument storing scc information about variable dependency.
;avoid hyps which may lead to circular dependency

; MODIFIED May 7 2011, if expr is (g a v) then return false, because we want it
; to furthur get dest-elimed, since if we there is still a mget call around it
; has to be a list/map mget call and we want the other variable to get mset
; into the list/map variable rather than the x getting value from mget of
; list/map variable .
(defun simple-var-hyp? (hyp var-quotient-alst list-dest-fns)
  (and (not (constant-hyp? hyp));not (= x c)
       (not (equiv-hyp? hyp));not (= x y)
       (= 3 (len hyp))
       (member-eq (car hyp) '(equal = eq eql))
       (or (proper-symbolp (second hyp))
           (proper-symbolp (third hyp)))
       (mv-let (var expr)
               (destruct-simple-hyp hyp)
               (and 
                ;;No cycles
                (let* ((vquotient (get-val var var-quotient-alst))
;get-free-vars1 only non-buggy for terms
                       (dvars (get-free-vars1 expr nil))
                       (dquotients (get-val-lst dvars var-quotient-alst)))
                  (not (member-equal vquotient dquotients)))
                ;;No top-level mget in expr
                (not (member-eq (car expr) list-dest-fns))))))
                    



(defun directed-2-rel? (hyp)
  ;(declare (xargs :guard (pseudo-termp hyp)))
;is hyp a directed (computationally) binary relation term
;hyp = (R x (f y)), where f should represent
;some computation other than accessors
;Assumption, hyp cannot be a constant hyp, since
;this function is always called after constant-hyp?
;in function build-vdependency-graph
;TODO maintain a global list of common accessor functions
  (and (= (len hyp) 3)
       (let* ((t2 (second hyp))
              (t3 (third hyp)))
         (or (and (proper-symbolp t2) 
                  (consp t3)
                  (not (member-eq (car t3) 
                           '(acl2::mget acl2::g g
                                        acl2::nth acl2::car ;SET::head
                                        acl2::cdr))))
             (and (proper-symbolp t3) 
                  (consp t3);copy paste bug
                  (not (member-eq (car t3) 
                           '(acl2::mget acl2::g g
                                        acl2::nth acl2::car ;SET::head
                                        acl2::cdr))))))))
              
(defun undirected-2-rel? (hyp)
 ; (declare (xargs :guard t))
;is hyp a undirected (computationally) binary relation term
;hyp = (~ x y), where ~ should be one of 
;(= eq equal eql subset-equal < <= > >=)
;TODO maintain a global list of such functions

  (and (= (len hyp) 3)
       (let* ((t2 (second hyp))
              (t3 (third hyp)))
         (and (proper-symbolp t2) 
              (proper-symbolp t3)
              (member-eq (first hyp) ;Relation
                  '(acl2::= acl2::equal acl2::eq acl2::eql
                            acl2::< acl2::<= 
                            acl2::> acl2::>=))))))

;hyp is of form (R term1 term2 ... termn)
;alst is basically the adjacency list rep of a graph
;Assumption term-lst is a term-listp otherwise get-free-vars1
;will not operate correctly
(defun put-interdependency-edges-in-alst (term-lst all-terms alst)
  #|(declare (xargs :guard (and (true-listp term-lst)
                              (true-listp all-terms)
                              (alistp alst))))|#
  (if (endp term-lst)
    alst
    (let* ((term (car term-lst))
           (vars (get-free-vars1 term nil))
           (rest-terms (remove-equal term all-terms))
           (rest-vars (get-free-vars1-lst rest-terms nil))
           )
      (put-interdependency-edges-in-alst 
       (cdr term-lst) all-terms
       (union-entries-in-adj-list vars ;sloppy, dont want self-edges
                                  (set-difference-eq rest-vars vars)
                                  alst)))))
         
;make a dependency graph of variables in a formula.
;TODO: equal can be any equivalence relation
;An edge from A to B means, A depends on B
;Note: (equal x <constant-expr>) forces x to be a leaf!!

;alst = ((var . (listof var)) ...) 
;alst-C= ((var . nil)) ;constants are forced to be leaves
;incoming = (map var (map symbol nat)) 
;e.g  (x . ((= . 1) (R . 2) (< . 1)) YET to be IMPLEMENTED

;PreCondition: hyp-lst is a term-list (IMPORTANT)
(defun build-vdependency-graph (hyp-lst alst alst-C incoming)
  (declare (ignorable incoming))
  (declare (xargs :verify-guards nil
                  :guard (and (pseudo-term-listp hyp-lst)
                              (symbol-alistp alst);       TODO
                              (symbol-alistp alst-C);     lost
                              (symbol-alistp incoming))));type information
 "return the dependency graph in alst, when all hypotheses have been 
processed, the annotation of edges is also returned"
  (if (endp hyp-lst)
    (append alst alst-C) ;ques: shouldnt the order be the other way round?
    (let ((hyp (car hyp-lst)))
      (cond 
       ((constant-hyp? hyp) ;(equal x (cons 1 2))
        (b* (((mv var &) (destruct-simple-hyp hyp)))
          (build-vdependency-graph (cdr hyp-lst)
                                   (remove-entry var alst)
;annotate the fact that var is assigned to a constant
                                   (put-assoc-equal var nil alst-C)
                                   incoming)))
       
; 15 Oct '13 --harshrc: Commented out the following, so that (= x y)
; case is subsumed by the default case of cond i.e (R term1 ... termN)
; Thus, instead of not drawing an edge, a undirected edge is added
; between x and y.

;;        ((undirected-2-rel? hyp);(~ x  y)
;; ;dont draw an edge
;;         (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming))

       ((directed-2-rel? hyp);(= x (f y))
        (b* (((mv var term) (destruct-simple-hyp hyp))
             (fvars (remove-equal ;sloppy code
                     var (get-free-vars1 term nil))));buggy for non-terms
          (build-vdependency-graph 
           (cdr hyp-lst)
;Q:shudnt we overwrite instead?
;A:No, consider both (= x (f y)) (= x (g w)) in hyps
;But does it matter either way? TODO
           (union-entry-in-adj-list var fvars alst) 
           alst-C
           incoming)))
;       [2015-04-16 Thu] Add special support for member
       ((and (membership-relationp (car hyp)) ;(member x term)
             (proper-symbolp (second hyp)))
        (b* ((var (second hyp))
             (term (third hyp))
             (fvars (remove-equal ;sloppy code
                     var (get-free-vars1 term nil))));buggy for non-terms
          (build-vdependency-graph 
           (cdr hyp-lst)
           (union-entry-in-adj-list var fvars alst) 
           alst-C
           incoming)))
       
       (t
;(R term1 term2 ...termN) ==> add edges between x and y where x \in termI
;and y \in termJ and I=!J and R is a N-ary relation
        (let* 
            ((vars (get-free-vars1 hyp nil));only non-buggy for terms
             (num-vars (len vars)))
          (if (<= num-vars 1);unchanged
              (build-vdependency-graph (cdr hyp-lst) alst alst-C incoming)
            (b* ((alst1 (put-interdependency-edges-in-alst 
                         (cdr hyp) ;recurse (term1 ... termn)
                         (cdr hyp) ;all-terms
                         alst))) 
              (build-vdependency-graph (cdr hyp-lst) 
                                       alst1 alst-C incoming)))))))))


(defun build-variable-dependency-graph (hyps vars)
  (build-vdependency-graph hyps (make-empty-adj-list vars) nil nil))


(def all-vars-lst (terms)
  (decl :sig ((pseudo-term-listp) -> symbol-list)
        :doc "all free variables in list of terms")
  (all-vars1-lst terms '()))

;(verify-termination dumb-negate-lit)


(def vars-in-dependency-order (hyps concl vl wrld)
  (decl :sig ((pseudo-term-list pseudo-term fixnum plist-world) -> symbol-list)
        :doc "return the free variables ordered according to the notion of
  dependency that treats equality relation specially. See FMCAD paper for
  details, but I have not completely implemented the improvements in the
  paper. This is where I can use better heuristics. But with no hard examples
  to work on, I am doing a naive job for now.")
  (b* ((cterms (cons (dumb-negate-lit concl) hyps))
; cterms names constraint terms
       (vars (all-vars-lst cterms))
       ((mv Hc Hs Ho) (separate-const/simple-hyps. cterms wrld '() '() '()))
       
       (dgraph (build-variable-dependency-graph Ho vars)) ;TODO rewrite
       (ord-vs (reverse (approximate-topological-sort dgraph (system-debug-flag vl))))
       
       (cvars (all-vars-lst Hc))
       (svars (all-vars-lst Hs))
; add only those svars that are not in ord-vs to front of ord-vs
; cvars should always be in front, i.e they should be chosen first
       (ord-vs (union-eq svars ord-vs)) ;NOT a set operation
       (ord-vs (union-eq cvars 
                         (set-difference-eq ord-vs cvars)))

; 8th Jan 2013 Possible CCG bug
; Overcaution: remove t and nil which escape pseudo-termp
       (ord-vs (set-difference-eq  ord-vs '(t nil)))
       )

   ord-vs))
       







;;;; * Collecting type and additional constraints

;;; Given a list of hypotheses and a conclusion, we want to find the
;;; type constraints on each free variable. We collect 4 categories of
;;; constraints: 1. defdata type and spilled defdata types 2. equality
;;; constraints 3. range constraints 4. additional constraints.

;;; A defdata type has a type-predicate and a type-enumerator
;;; associated with it.  Ideally we would like to compute the minimal
;;; (best possible) defdata type information, but this can fail, due
;;; to incomplete subtype type information.  So we end up also storing
;;; spillover types, whose union/join is the conservative (superset)
;;; type of the corresponding variable. We also store the equality
;;; constraint, since its a very strong constraint and often comes up
;;; in naive dependencies. Finally we also store additional
;;; constraints, just so as to not throw away information that can
;;; fruitfully be utilized to come up with the smallest set of
;;; possible values the constrained variable can take.
;;; range is just a tau-intervalp

(defrec cs% (defdata-type spilled-types 
              eq-constraint 
              range
              member-constraint ; [2015-04-16 Thu] Added support for member-equal
              additional-constraints) NIL)


(defun cs%-p (v)
  (declare (xargs :guard T))
  (case-match v ;layout not hidden -- see build-enumcalls.lisp
    (('cs% dt st eqc int mem ac)

     (and (possible-defdata-type-p dt) 
          (possible-defdata-type-list-p st)
          (or (pseudo-termp eqc)
              (eq 'defdata::empty-eq-constraint eqc))
          (acl2::tau-intervalp int)
          (pseudo-termp mem)
          (pseudo-term-listp ac)))))
    

(defun |is (symbol . cs%)| (v)
  (declare (xargs :guard T))
  (case-match v
    ((x . y)      (and (symbolp x)
                       (cs%-p y)))))

(defun symbol-cs%-alistp (vs)
  (declare (xargs :guard T))
  (if (consp vs)
      (and (|is (symbol . cs%)| (car vs))
           (symbol-cs%-alistp (cdr vs)))
    NIL))
           

  ;; (foldl (lambda (v acc) (and acc (|is a (symbol . type-constraints%)| v) ))
  ;;        T vs)) 
; Note: The above expression if implemented is not as efficient as 
;; (defun _-list-p (xs) 
;;   (if (endp x) T 
;;     (and (_-p (car x))
;;          (_-list-p (cdr x)))))
  ;; (and (true-listp vs)
  ;;      (null ([ x : x in vs : (not (|is a (symbol . type-constraints%)|)) ])))
 

;; TODO: conclusion is not taken care of now. Only negated conclusion
;; is treated, but we would like to be symmetric with respect to
;; searching cts and wts. --harshrc 4th March 2012.

(def put-additional-constraints. (vs term v-cs%-alst.)
  (decl :sig ((symbol-list pseudo-term symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put term in alist for all keys in vs")
  (if (endp vs)
      v-cs%-alst.
    (b* (((cons v cs%) (assoc-eq (car vs) v-cs%-alst.))
         (cs% (change cs% additional-constraints 
                      (cons term (access cs% additional-constraints)))))
    (put-additional-constraints. (cdr vs) term 
                                 (put-assoc-eq v cs% v-cs%-alst.)))))

(def insert-before-key  (key entry alist)
  (decl :sig ((symbol entry symbol-alist) -> symbol-alist)
        :doc "insert entry before key in alist")
  (if (endp alist)
      nil
    (if (eq key (caar alist))
        (cons entry alist)
      (cons (car alist)
            (insert-before-key key entry (cdr alist))))))
              
;2 july '13 (type-info-lost-via-dest-elim issue)
; TODO: check if check for cycles is correct!
; 15 Oct '13: ugly hack to reorder around dependency change.
(def put-var-eq-constraint. (v1 v2 vl wrld v-cs%-alst.)
  (decl :sig ((symbol symbol vl plist-world symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put variable equality constraint in alist for key v")
  (declare (xargs :verify-guards nil))
  (b* (((cons & cs1%) (assoc-eq v1 v-cs%-alst.))
       ((cons & cs2%) (assoc-eq v2 v-cs%-alst.))
       (dt1 (acl2::access cs% cs1% :defdata-type))
       (dt2 (acl2::access cs% cs2% :defdata-type))
       (M  (table-alist 'defdata::type-metadata-table wrld))
       (P1 (defdata::predicate-name dt1 M))
       (P2 (defdata::predicate-name dt2 M))
       ((mv v other-v cs% other-cs%) (if (defdata::subtype-p P2 P1 wrld) 
                                         (mv v1 v2 cs1% cs2%) ;dt2 is better
                                       (mv v2 v1 cs2% cs1%) 
                                       ))
       (eqc (acl2::access cs% cs% :eq-constraint))
       (other-eqc (acl2::access cs% other-cs% :eq-constraint))
       ((when (eq other-v eqc)) v-cs%-alst.) ;redundant
       ((when (eq v other-eqc)) v-cs%-alst.) ;avoid cycle!!
       (- (cw? (and (verbose-stats-flag vl)
                    (not (eq 'defdata::empty-eq-constraint eqc))) 
               "CEgen/Note: Overwriting (variable) eq-constraint for ~x0 with ~x1~|" v other-v))
       (cs% (change cs% eq-constraint other-v))
       (v-cs%-alst. (put-assoc-eq v cs% v-cs%-alst.)))
; 15 Oct '13 -- other-v should come before v in the order of keys in
; v-cs%-alst. or at least in the let* binding. Since there two
; variables are related by an equivalence relation, all entries
; between them will also be in the same equivalence class, so it
; suffices to remove the other-v entry and insert it just in front of
; the entry of v.
    (insert-before-key v (cons other-v other-cs%)
                       (delete-assoc-eq other-v v-cs%-alst.))))


(def put-eq-constraint. (v term vl v-cs%-alst.)
  (decl :sig ((symbol pseudo-term vl symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put eq-constraint term in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (eqc (access cs% eq-constraint))
       (- (cw? (and (verbose-stats-flag vl)
                    (not (eq 'defdata::empty-eq-constraint eqc)))
               "CEgen/Note: Overwriting eq-constraint for ~x0 with ~x1~|" v term))
       (cs% (change cs% eq-constraint term)))
   (put-assoc-eq v cs% v-cs%-alst.)))


(def put-member-constraint. (v term vl v-cs%-alst.)
  (decl :sig ((symbol pseudo-term vl symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put member-constraint term in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (memc (access cs% member-constraint))
       (- (cw? (and (verbose-stats-flag vl)
                    (not (equal 'defdata::empty-mem-constraint memc)))
               "CEgen/Note: Overwriting member-constraint for ~x0 with ~x1~|" v term))
       (cs% (change cs% member-constraint term)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def put-defdata-type. (v typ vl v-cs%-alst.)
  (decl :sig ((symbol possible-defdata-type-p fixnum symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "put defdata type typ in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (dt (access cs% defdata-type))
       (- (cw? (and (verbose-stats-flag vl) (not (eq 'ACL2S::ALL dt)))  ;TODO perhaps use is-top? but that might be expensive?
"CEgen/Note: Overwriting defdata type for ~x0. ~x1 -> ~x2~|" v dt typ))
       (cs% (change cs% defdata-type typ)))
   (put-assoc-eq v cs% v-cs%-alst.)))



(defs  ;;might be mut-rec, but right now I assume tht I wont encounter
       ;;AND and OR like if expressions, and hence dont need the
       ;;mutually-recursive counterpart of v-cs%-alist-from-term. TODO
  (v-cs%-alist-from-term. (term vl wrld ans.)
  (decl :sig ((pseudo-term fixnum plist-world  symbol-cs%-alist)
              ->
              symbol-cs%-alist)
        :doc "helper to collect-constraints")
  (declare (xargs :verify-guards nil))
;Invariant: ans. is an alist thats in the order given by dependency analysis
  (f* ((add-constraints... () (put-additional-constraints. fvars term ans.))
; [2015-04-16 Thu] add support for membership
       (add-eq/mem-constraint... (t1) (if (membership-relationp R)
                                          (put-member-constraint. x t1 vl ans.)
                                        (add-eq-constraint... t1)))
       (add-eq-constraint... (t1) (if (acl2::equivalence-relationp R wrld)
                                      (if (symbolp t1)
                                          (put-var-eq-constraint. x t1 vl wrld ans.)
                                        (put-eq-constraint. x t1 vl ans.))
                                    (add-constraints...))))
     
   (b* ((fvars (all-vars term)))
           
    (case-match term
      
;the following is a rare case (I found it when the conclusion is nil
;and its negation is 'T
      (('quote c) (declare (ignore c))  ans.) ;ignore quoted constant terms 

;TODO possible field variable (i.e f is a getter/selector)
; Note that term cannot have a lambda applicaton/let, so the car of the term is
; always a function symbol if term is a consp.
      ((P (f . &)) (declare (ignore P f))  (add-constraints...)) 

;x has to be an atom below, otherwise, we would have caught that case above.
      (('not x)      (put-eq-constraint. x ''nil vl ans.))
      
      ((P x)   (b* ((tname (defdata::is-type-predicate P wrld))
                    ((cons & cs%) (assoc-eq x ans.))
                    (curr-typ (access cs% defdata-type))
                    (smaller-typ (meet tname curr-typ vl wrld )))
                (if tname
                    (if (not (eq smaller-typ curr-typ))
                        (put-defdata-type. x smaller-typ vl ans.)
                      ans.)
                  (add-constraints...))))

      ((R (f . &) (g . &)) (declare (ignore R f g)) (add-constraints...))

;x has to be an atom below, otherwise, we would have caught that case
;above.
      ((R x ('quote c))    (add-eq/mem-constraint... (kwote c)))
      ((R ('quote c) x)    (add-eq-constraint... (kwote c)))
      ((R x (f . args))    (add-eq/mem-constraint... (acl2::cons-term f args)))
      ((R (f . args) x)    (add-eq-constraint... (acl2::cons-term f args)))
      ((R x y)             (add-eq/mem-constraint... y))
      
      ;; has to be a (R t1 t2 ...) or atomic term
      (&                   (add-constraints...)))))))
                         
  
(def v-cs%-alist-from-terms. (terms vl wrld ans.)
  (decl :sig ((pseudo-term-listp fixnum plist-worldp symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc "helper to collect-constraints%")
  (declare (xargs :verify-guards nil))
  (if (endp terms)
      ans.
    (v-cs%-alist-from-terms. (cdr terms) vl wrld  
                             (v-cs%-alist-from-term. (car terms)
                                                     vl wrld ans.))))

(def put-range-constraint. (v int v-cs%-alst.)
  (decl :sig ((symbolp acl2::tau-intervalp symbol-cs%-alistp) 
              -> symbol-cs%-alistp)
        :doc "put interval int in alist for key v")
  (b* (((cons & cs%) (assoc-eq v v-cs%-alst.))
       (cs% (change cs% range int)))
   (put-assoc-eq v cs% v-cs%-alst.)))

(def range-is-alias-p (interval type wrld)
  (decl :sig ((non-empty-non-universal-interval-p symbolp plist-worldp) -> boolean)
        :doc "is interval an alias of type?")
  (declare (xargs :verify-guards nil))
  (b* ((lo (acl2::access acl2::tau-interval interval :lo))
       (hi (acl2::access acl2::tau-interval interval :hi))
       (lo-rel (acl2::access acl2::tau-interval interval :lo-rel))
       (hi-rel (acl2::access acl2::tau-interval interval :hi-rel))
       (P (defdata::predicate-name type (table-alist 'DEFDATA::TYPE-METADATA-TABLE wrld))))
    (case (acl2::access acl2::tau-interval interval :domain)
      (acl2::integerp (or (and (defdata::subtype-p P 'ACL2::NATP wrld) ;use the fact that integers are squeezed (weak inequalities)
                               (equal lo 0)
                               (null hi))
                          (and (defdata::subtype-p P 'ACL2::POSP wrld) 
                               (equal lo 1)
                               (null hi))
                          (and (defdata::subtype-p P 'ACL2::NEGP wrld) 
                               (null lo)
                               (equal hi -1))))
      (otherwise (or (and (defdata::subtype-p P 'ACL2::POSITIVE-RATIONALP wrld)
                          lo-rel ;strict
                          (null hi)
                          (equal lo 0))
                     (and (defdata::subtype-p P 'ACL2::NEGATIVE-RATIONALP wrld) 
                          hi-rel
                          (null lo)
                          (equal hi 0)))))))

(def assimilate-apriori-type-information (vs type-alist tau-interval-alist vl wrld ans.)
  (decl :sig ((symbol-list symbol-alist symbol-alist fixnum plist-world symbol-cs%-alist) 
              -> symbol-cs%-alist)
        :doc 
"overwrite into v-cs%-alst. the type information in type-alist/tau-interval-alist.
Put defdata symbol types into defdata-type field, but put constants
into eq-constraint field and put interval into range constraint field")
  (declare (xargs :verify-guards nil))
; Aug 30 '12 -- This function fixes a bug in Pete's GE demo, where the
; type=alist had 'NIL as the type, which is a singleton defdata type
; and I was not taking it into consideration when trying to run MEET
; on it, which cannot handle types which are not in the defdata graph,
; and certainly constants are not part of the defdata graph.
  (if (endp vs)
      ans.
    (b* ((x (car vs))
         (prior-t (assoc-eq x type-alist)) ;prior-t is consp assert!
;type-alist of of form (listof (cons var (listof defdata-type)))
;where defdata-type is possible-defdata-type-p. listof represents unions.
         (- 
; TODO: Union types are ignored. Implement them.
; But note that since we always get this through a meet-type-alist, we
; throw away the union type information there itself.
           (cw? (and (verbose-stats-flag vl)
                     (consp prior-t)
                     (consp (cdr prior-t)) 
                     (not (null (cddr prior-t))))
"~|CEgen/Warning: Ignoring rest of union types ~x0 ~|" (cddr prior-t)))
         (typ-given (if (and (consp prior-t) (consp (cdr prior-t)))
                        (cadr prior-t)
                      'ACL2S::ALL))
         ((when (defdata::possible-constant-value-p typ-given))
; is a singleton, then treat it as a eq-constraint
; BOZO: meet-type-alist does it differently. (03/04/13)
          (assimilate-apriori-type-information 
           (cdr vs) type-alist tau-interval-alist vl wrld  
           (put-eq-constraint. x typ-given vl ans.)))
         (int-entry (assoc-eq x tau-interval-alist))
         (int (cdr int-entry)) ;possible type bug
         ((when (singleton-tau-intervalp int))
; is a singleton, then treat it as a eq-constraint
          (assimilate-apriori-type-information 
           (cdr vs) type-alist tau-interval-alist vl wrld  
           (put-eq-constraint. x (kwote (acl2::access acl2::tau-interval int :lo)) vl ans.)))
         ((cons & cs%) (assoc-eq x ans.))
         (curr-typ (access cs% defdata-type))
         (final-typ (meet curr-typ typ-given vl wrld))
         (ans. (if (and (non-empty-non-universal-interval-p int)
                        (not (range-is-alias-p int final-typ wrld)))
                   (put-range-constraint. x int ans.)
                 ans.)))
                   
; update the current defdata type with the new type information (type-alist)
     (assimilate-apriori-type-information 
      (cdr vs) type-alist tau-interval-alist vl wrld
      (put-defdata-type. x final-typ vl ans.)))))

(defconst *empty-cs%*
  (acl2::make cs%
        :defdata-type 'ACL2S::ALL 
        :spilled-types '()
        :eq-constraint 'defdata::empty-eq-constraint
        :range (acl2::make-tau-interval nil nil nil nil nil)
        :member-constraint 'defdata::empty-mem-constraint
        :additional-constraints '()))

(def collect-constraints% (hyps ordered-vars type-alist tau-interval-alist vl wrld)
  (decl :sig ((pseudo-term-listp symbol-listp symbol-alistp symbol-alistp
                                 fixnum plist-worldp) -> symbol-cs%-alist)
        :doc 
" 
* Synopsis 
  For each free variable compute/infer both the simple defdata types
  and additional constraints on it.

* Input 
  hyps is a usually a list of hypotheses of the conjecture under query
  and is a term-listp ordered-vars is the free variables of hyps, but in the
  variable dependency order as computed from the dependency graphs of hyps.
  type-alist is the type information inferred from ACL2 usually (intersected
  with the top-level dumb type inference), or it might be prior type knowledge
  we dont want to lose i.e if the type inferred from hyps are weaker than in
  type-alist we will keep the stronger type information. tau-interval-alist is
  the range type information inferred by Tau.
  

* Output
  An alist mapping free variables to cs% record
")
  (declare (xargs :verify-guards nil))
  (f* ((unconstrained-v-cs%-alst (xs) (pairlis$ xs (make-list (len xs)
                                                              :initial-element 
                                                              *empty-cs%*))))
      ;; initialize the alist
    (b* ((v-cs%-alst  (unconstrained-v-cs%-alst ordered-vars))
         (v-cs%-alst  (assimilate-apriori-type-information
                       ordered-vars type-alist tau-interval-alist
                       vl wrld v-cs%-alst)))
       
     (v-cs%-alist-from-terms. hyps vl wrld v-cs%-alst))))


;bugfix May 24 '12
;partial-A needs to be quoted to avoid being confused with function app
(def kwote-symbol-doublet-list (A)
  (decl :sig ((symbol-doublet-listp) -> quoted-constantp))
  (if (endp A)
      nil
    (cons (list 'list (kwote (caar A)) (cadar A))
          (kwote-symbol-doublet-list (cdr A)))))


(def make-next-sigma-defuns (hyps concl ord-vs 
                                  partial-A type-alist tau-interval-alist
                                  programp vl wrld )
  (decl :sig ((pseudo-term-list pseudo-term symbol-list 
                      symbol-doublet-listp symbol-alist symbol-alist
                      boolean fixnum plist-worldp ) 
              -> (mv erp all symbol-alist))
        :doc "return the defun forms defining next-sigma function, given a
        list of hypotheses and conclusion (terms). Also return the enum-alist to be displayed")
  (declare (xargs :verify-guards nil))
  (f* ((defun-forms ()
         `((defun next-sigma-current (sampling-method seed. BE.)
            "returns (mv A seed. BE.)"
            (declare (ignorable sampling-method)) ;in case ord-vs is nil
            (declare (type (unsigned-byte 31) seed.))
            (declare (xargs :verify-guards nil
                            :mode :program ;New defdata has program-mode enumerators -- Sep 1 2014
                            :guard (and (member-eq sampling-method
                                                   '(:random :uniform-random :be))
                                        (unsigned-byte-p 31 seed.)
                                        (symbol-unsigned-29bits-alistp BE.)
                                        (consp BE.) ;precondition TODOcheck
                                        (and ,@(make-guard-var-member-eq
                                                (strip-cars var-enumcalls-alist)
                                                'BE.)))
                            :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))))
            ,(make-next-sigma_mv-let
                var-enumcalls-alist
; sigma will be output as a let-bindings i.e symbol-doublet-listp
                `(mv ,(make-var-value-list-bindings 
                       (strip-cars var-enumcalls-alist) 
                       (kwote-symbol-doublet-list partial-A))
                     seed. BE.)))
           (defun next-sigma-current-gv (sampling-method seed. BE.)
             (declare (xargs :mode :program ;New defdata has program-mode enumerators -- Sep 1 2014
                             :guard T :verify-guards ,(not programp)))
             ;(declare (type (unsigned-byte 31) seed.))
             (ec-call (next-sigma-current sampling-method seed. BE.))))))
         
; Invariant: v-cs%-alst. should obey a dependency order such that the
; final enum-call alist when converted to a let* will obey the
; dependency order of evaluation. This is mostly satisfied, as
; ord-vars does take care of this. But put-var-eq-constraint. might
; change this, where an extra dependency is created because of type
; information that was ignored during creation of ord-vs, so there is
; an ugly hack in place to reorder in the middle of put-var-eq-constraint.
       
   (b* ((v-cs%-alst (collect-constraints% (cons (dumb-negate-lit concl) hyps)
                                          ord-vs type-alist tau-interval-alist vl wrld ))
        ((mv erp var-enumcalls-alist) (make-enumerator-calls-alist v-cs%-alst vl wrld '()))
        ((when erp) (mv erp '() '()))
        )
;   in
    (mv nil (defun-forms) (displayed-enum-alist v-cs%-alst '())))))




         
        





;; Feb 22 2013 Add a new global state variable which points to
;; a stack of accumulated cgen recorded statistics. 

;; [2014-05-03 Sat] Modified again. Now we just have one global cgen-state
;; which stores all the information used and recorded by cgen/testing.

;NOTE: interesting - I cant use defmacro instead of defabbrev

(defun get-s-hist-global (ctx state) 
  (if (f-boundp-global 'cgen-state state)
    (b* ((cgen-state (@ cgen-state))
         ((unless (valid-cgen-state-p cgen-state))
          (er hard? ctx "~|CEgen/Error: (get-s-hist) cgen-state is ill-formed~|"))
         (s-hist (cdr (assoc-eq :s-hist cgen-state))))
      (if (s-hist-p s-hist)
          s-hist
        (er hard? ctx "~|CEgen/Error: hist found in globals is of bad type~|")))
    (er hard? ctx "~|CEgen/Error: cgen-state not found in globals ~|")))


(defabbrev put-s-hist-global (s-hist) 
  (if (f-boundp-global 'cgen-state state)
      (if (s-hist-p s-hist)
          (b* ((cgen-state (@ cgen-state))
               ((unless (valid-cgen-statep cgen-state))
                (prog2$ 
                 (er hard? ctx "~|CEgen/Error: (put-s-hist) cgen-state is ill-formed~|")
                 state))
               (cgen-state (put-assoc-eq :s-hist s-hist cgen-state))
               (- (assert$ (valid-cgen-state-p cgen-state) 'put-s-hist-global)))
          (f-put-global 'cgen-state cgen-state state))
        (progn$
         (cw? (debug-flag vl) "~|BAD s-hist : ~x0~|" s-hist)
         (er hard? ctx "~|CEgen/Error: hist being put in globals is of bad type~|")
         state))
    (prog2$ (er hard? ctx "~|CEgen/Error: cgen-state not found in globals ~|")
            state)))


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
          


;; COPIED FROM acl2-sources/basis.lisp line 12607
;; because it is program mode there, and verify-termination needed more effort
;; than I could spare.
(defun dumb-negate-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

(def clause-mv-hyps-concl (cl)
  (decl :sig ((clause) 
              -> (mv pseudo-term-list pseudo-term))
        :doc "return (mv hyps concl) which are proper terms given a
  clause cl. Adapted from prettyify-clause2 in other-processes.lisp")
  (cond ((null cl) (mv '() ''NIL))
        ((null (cdr cl)) (mv '() (car cl)))
        ((null (cddr cl)) (mv (list (dumb-negate-lit (car cl)))
                              (cadr cl)))
        (t (mv (dumb-negate-lit-lst (butlast cl 1))
               (car (last cl))))))

(def clausify-hyps-concl (hyps concl)
  (decl :sig ((pseudo-term-list pseudo-term)
              -> clause)
        :doc "given hyps concl which are proper terms return equivalent
  clause cl. inverse of clause-mv-hyps-concl")
  (cond ((and (endp hyps) (equal concl ''NIL)) 'NIL)
        ((endp hyps) (list concl))
        ((endp (cdr hyps)) (list (dumb-negate-lit (car hyps)) concl))
        (t (append (dumb-negate-lit-lst hyps)
                   (list concl)))))






(def ss-stats (ss-temp-result old-test-outcomes%)
  (decl :sig (((list booleanp test-outcomes% gcs%) test-outcomes%) -> all)
        :doc "print some stats about this run of simple-search")
  (b* (((list stop? test-outcomes% &) ss-temp-result)
       (new-num-cts (access test-outcomes% |#cts|))
       (old-num-cts (acl2::access test-outcomes% old-test-outcomes% :|#cts|))
       (new-num-wts (access test-outcomes% |#wts|))
       (old-num-wts (acl2::access test-outcomes% old-test-outcomes% :|#wts|))
       (new-total (+ new-num-cts (access test-outcomes% |#vacs|) new-num-wts (access test-outcomes% |#dups|)))
       (old-total (+ old-num-cts (acl2::access test-outcomes% old-test-outcomes% :|#vacs|) old-num-wts (acl2::access test-outcomes% old-test-outcomes% :|#dups|)))
       (found-wts (- new-num-wts old-num-wts))
       (found-cts (- new-num-cts old-num-cts))
       (n (- new-total old-total))
       (- (cw? t
               "~|CEgen/Stats/simple-search: ~x0/~x1 cts/wts found in this run (~x2 tests)!~|" found-cts found-wts n))
       (- (cw? t
               "~|CEgen/Stats/simple-search: *END* Stopping condition: ~x0~%~%" stop?)))
    nil))
       

; pushed the with-timeout wrapper into the trans-eval make-event of simple-search to get saner cgen::event-stack behavior
; [2015-02-04 Wed] The reason in the above note is irrelevant now that we disallow nested testable events. 
(defun run-tests-with-timeout (timeout-secs N sm vl num-cts num-wts vars test-outcomes% gcs% state)
  (acl2::with-timeout1 
   timeout-secs
   (b* (;((mv rseed. state) ) (acl2::random$ defdata::*M31* state) ;Lets try CL's builtin random number generator
        (rseed. (defdata::getseed state))
        (- (cw? (system-debug-flag vl) 
                "~|CEgen/Sysdebug/run-tests: starting SEED: ~x0 ~%" rseed.))
        (BE.    (pairlis$ vars (make-list (len vars) :initial-element 0)))
        ((mv stop? rseed. test-outcomes% gcs%)
         (run-tests. N sm vl num-cts num-wts rseed. BE. test-outcomes% gcs%))
        (state (defdata::putseed rseed. state))
        )
     (assign ss-temp-result (list stop? test-outcomes% gcs%)))
   ;; timeout form
   (prog2$
    (cw? (normal-output-flag vl)
         "~%Search for counterexamples TIMED OUT! ~
~|Use (acl2s-defaults :set cgen-local-timeout 0) to disable timeout. ~
~|For more information see :doc cgen-local-timeout.~%") 
    (er-progn
     (b* (((mv & (the (unsigned-byte 31) rseed.)) (defdata::genrandom-seed 2 (defdata::getseed state)))
          (state (defdata::putseed rseed. state))) ;make some progress -- dont get stuck on the same sequence of seeds
       (value nil))
     (assign ss-temp-result :timed-out)
     (mv T nil state)))))




;; 1st April 2013 Fix
;; You cannot trust make-event to give the right result
;; through trans-eval. Just use a state temp global.
;; This bug manifests, when you use (skip-proofs ....)

(def simple-search (name 
                    hyps concl vars partial-A 
                    type-alist tau-interval-alist mv-sig-alist
                    test-outcomes% gcs%
                    N vl sm num-cts num-wts timeout-secs
                    top-vt-alist
                    programp incremental-flag?
                    ctx state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list symbol-doublet-listp
                variable-alist variable-alist variable-alist
               test-outcomes% gcs% 
               fixnum fixnum keyword fixnum fixnum rational
               variable-alist
               boolean boolean
               symbol state) 
              -> (mv erp (list boolean test-outcomes% gcs%) state))
        :mode :program
        :doc 
        "
Use :simple search strategy to find counterexamples and witnesses.

* What it does
  1. if form has no free variables exit with appropriate return val o.w
  2. make hypotheses-val conclusion-val,  attach them
  3. take intersection of acl2 type-alist with top-level one from gcs%.
  4. make next-sigma defun and attach it
  5. call run-tests!.
  6. store/record information (test-outcomes%,gcs%) and 
     returns (list stop? test-outcomes% gcs%) where stop? is T when
     stopping condition is satisfied and there was no error in ld.
")
  
  (if (endp vars)
; dont even try trivial forms like constant expressions
      (b* ((form  `(implies (and ,@hyps) ,concl))
            ((mv erp c state)
             (trans-eval-single-value form ctx state))
            ((mv test-outcomes% gcs%)
             (record-testrun. (if c :witness :counterexample)
                              '()
                              partial-A
                              num-cts num-wts
                              vl test-outcomes% gcs%)))

;       in
        (prog2$
         (if partial-A
             (cw? (verbose-flag vl)
              "~%CEgen/Note: No point in searching ~x0; it evals to const ~x1 under ~x2~|" name c partial-A)
             (cw? (verbose-flag vl)
              "~%CEgen/Note: No point in searching ~x0; it evals to const ~x1~|" name c))
         (mv erp (list NIL test-outcomes% gcs%) state)))

;ELSE atleast one variable
  (b* ((- (assert$ (consp vars) 'simple-search))
       (- (cw? (verbose-flag vl) "~%~%"))
       (- (cw? (verbose-stats-flag vl) 
               "~|CEgen/Stats/simple-search:: *START*~|"))

       (hyp-val-defuns   (make-hypotheses-val-defuns hyps vars mv-sig-alist programp))
       (concl-val-defuns (make-conclusion-val-defuns concl vars mv-sig-alist programp))
;       [2015-04-07 Tue]
;       Order of hyps is important -- Values of each hyp is stored in seq
       (hyp-val-list-defuns (make-hyp-val-list-defuns hyps vars mv-sig-alist programp))
       
       (wrld (w state))
       ;; ((mv erp0 tr-res state) ;commented out after throwing graph-tc.lisp
       ;;  (trans-eval `(mv-list 2 (meet-type-alist ',type-alist ',top-vt-alist ',vl ',wrld))
       ;;              ctx state t))
       
       ((mv erp type-alist) (meet-type-alist type-alist top-vt-alist vl wrld))
       ((when erp)
        (prog2$
         (cw? (normal-output-flag vl)
              "~|CEgen/Error: Type intersection failed. Skip searching ~x0.~%" name)
         (mv t (list NIL test-outcomes% gcs%) state)))

       ((mv erp next-sigma-defuns disp-enum-alist)
        (make-next-sigma-defuns hyps concl ;developed in build-enumcalls.lisp
                                vars partial-A 
                                type-alist tau-interval-alist
                                t ; programp ;;Aug 2014 -- New defdata has program-mode enumerators
                                vl wrld))
       ((when erp)
        (prog2$ 
           (cw? (normal-output-flag vl)
                "~|CEgen/Error: Couldn't determine enumerators. Skip searching ~x0.~|" name)
           (mv t (list nil test-outcomes% gcs%) state)))
       (- (cw? (system-debug-flag vl) 
               "~|CEgen/Sysdebug: next-sigma : ~| ~x0~|" next-sigma-defuns))

   
       ;;initialize temp result
       ((er &) (assign ss-temp-result :init))
       
       (- (cw? (verbose-flag vl) 
               "~|CEgen/Note: Enumerating ~x0 with ~x1~|" name disp-enum-alist))
; print form if origin was :incremental
       (cl (clausify-hyps-concl hyps concl))
       (pform (acl2::prettyify-clause cl nil (w state)))
       (- (cw? (and incremental-flag?
                    (verbose-flag vl)) 
               "~| incrementally on ~x0 under assignment ~x1~%" pform partial-A))


       (call-form   
        `(acl2::state-global-let*
; :none is almost half as slow!!!  TODO: Do testing in two phases. First check
; for guard violations, if yes, print and proceed with :none, else use nil or t
; for faster execution speed.
          ((acl2::guard-checking-on ,(if (or t programp) :none nil))
           (acl2::inhibit-output-lst
                    ,(if (system-debug-flag vl)
                         ''(summary)
                       ;;shut everything except error
                       (quote #!acl2(remove1-eq 'error *valid-output-names*)))))
                  
          (run-tests-with-timeout ,timeout-secs ,N ,sm ,vl ,num-cts ,num-wts ',vars ',test-outcomes% ',gcs% state)))

      
       
       );end b* bindings
;  IN
   (mv-let 
    (erp trval state)
; [2014-08-30 Sat] Use ld instead of trans-eval+make-event
; Reasons:
; - ld can catch raw lisp errors (although it cannot suppress its error message). Note that we would like to fix any raw lisp errors of Cgen.
; - ld does not use make-event and so can be used in non-event contexts (This is important for Cgen to be used as an API)
; - ld restores previous world on error (We always arrange for the error to be produced at the end) 
; - Can be switched to wormholes if needed. (But then we cant use state to share the result of run-tests)
; - Is this parallelizable? Are wormholes?
; [2014-09-21 Sun] Reverted back to trans-eval. It is simpler and hopefully the interrupt story is saner!
; But we still dont use make-event, due to which we have to redef.
    (trans-eval 
     `(er-progn
           
          (with-output :stack :pop ,@(and (not (system-debug-flag vl)) '(:off :all))
          (progn
; added 2nd May '12. Support program context
          ,@(and programp '((program)))

; Jan 8th 2013 - support program mode 
; Sep 3 2014 - program-mode enumerators need skip-checks
          ,@(and (or t programp) '((defttag :cgen)))

; [2014-09-22 Mon] Instead of make-event, using redef. (Is this thread-safe?)
          #!acl2(PROGN! (SET-LD-REDEFINITION-ACTION '(:WARN! . :OVERWRITE) STATE))
          ,@hyp-val-defuns
          ,@concl-val-defuns
          ,@hyp-val-list-defuns
          ,@next-sigma-defuns
          #!acl2(PROGN! (SET-LD-REDEFINITION-ACTION NIL STATE))
                     

          
; Update Sep 27th 2012
; Folllowing a helpful email by Matt, found a way to fool the function
; to be guard verified, by wrapping its call in an ec-call
; This way I also get rid of the trust tag .... Hurrah!!
; Update Jan 8th 2013, but have to bring back the ttag and skip-checks for
; program mode testing :((
          ,@(if (or t programp)
                '((defattach (hypotheses-val hypotheses-val-current-gv) :skip-checks t)
                  (defattach (conclusion-val conclusion-val-current-gv) :skip-checks t)
                  (defattach (hyp-val-list hyp-val-list-current-gv) :skip-checks t)
                  (defattach (next-sigma next-sigma-current-gv) :skip-checks t))
              '((defattach (hypotheses-val hypotheses-val-current-gv))
                (defattach (conclusion-val conclusion-val-current-gv))
                (defattach (hyp-val-list hyp-val-list-current-gv))
                (defattach (next-sigma next-sigma-current-gv))))
          
          ,@(and (or t programp) '((defttag nil)))

          ))
          ,call-form
          (mv t nil state) ;always give error, to abort the er-progn and revert to the old world
          )
     ctx state t)
        ;; :ld-pre-eval-print nil
        ;; :ld-post-eval-print nil
        ;; :ld-error-triples t
        ;; :ld-error-action :error
        ;; :ld-skip-proofsp t
        ;; :ld-verbose nil
        ;; :ld-prompt nil
                
    ;; mv-let body
    (declare (ignore erp trval))

    (cond ((eq :timed-out (@ ss-temp-result)) (mv T nil state))
          ((atom (@ ss-temp-result))
           (prog2$ 
            (cw? (verbose-flag vl) "~|Cgen/Error : Bad trans-eval call in local Cgen/testing driver code.~|")
            (mv T nil state)))
          (t (prog2$
              (and (verbose-stats-flag vl)
                   (ss-stats (@ ss-temp-result) test-outcomes%))
              (value (@ ss-temp-result)))))))))


; incremental algorithm from FMCAD 2011 paper.
; the implementation below deviates by reusing
; simple-search at each partial assign
(def select (terms debug)
  (decl :sig ((pseudo-term-list boolean) 
              -> symbol)
        :doc "choose the variable with least dependency. Build a dependency
  graph, topologically sort it and return the first sink we find.")
;PRECONDITION: (len vars) > 1
;We have to build a dependency graph at each iteration, since the graph changes
;as we incrementally concretize/instantiate variables.  
;SELECT Ideal Situation:: No variable should be picked before the variable it
;depends on has been selected and assigned

  (b* ((vars (all-vars-lst terms))
       (G (build-variable-dependency-graph terms vars))
;TODO: among the variables of a component, we should vary
;the order of selection of variables!!
       (var (car (last (approximate-topological-sort G debug))))
       (- (cw? debug "~|DPLL: Select var: ~x0~%" var)))
   var))

; May 14 '12: changed to v-cs%-alst parameter for optimization
(def assign-value (x |#assigns| cs% partial-A sm vl ctx wrld state )
  (decl :sig ((symbol fixnum cs% symbol-doublet-listp
                      sampling-method fixnum symbol plist-world state )
              -> (mv erp (list pseudo-term keyword fixnum) state))
        :mode :program
        :doc "assign a value to x. Infer type constraints from hyps, get the
enumcall for x. trans-eval enumcall to get value to be assigned to x. quote it
to obtain a term. return (mv val :decision i+1), if size of type attributed to
x is greater than 1, otherwise return (mv val :implied i) where i= #assigns
made to x already.")
  (f* ((_eval-single-value (call)
              (b* ((vexp (if partial-A 
                             `(let ,partial-A 
                                (declare (ignorable ,@bound-vars))
                                  ,call) 
                           call))
                   (- (cw? (debug-flag vl) 
                           "~|CEgen/Debug/incremental:  ASSIGN ~x0 := eval[~x1]~|" x  vexp)))
                (trans-eval-single-value vexp ctx state))))

  (b* ((- (assert$ (cs%-p cs%) 'assign-value))
       (bound-vars (strip-cars partial-A))
       ((mv size calls) (cs%-enumcalls cs% ctx wrld bound-vars))
       
       (seed. (defdata::getseed state))
       ((mv erp seed. ans state)
        (case sm
             (:uniform-random 
              (b* (((mv m seed.) (defdata::random-natural-seed seed.))
; See comment in build-enumcalls.lisp:541
; (defdata::random-index-seed *recursive-uniform-enum-measure* seed.))
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
       (value (list val-term :implied |#assigns|))
     (value (list val-term :decision (1+ |#assigns|)))))))

;copied from tools/easy-simplify.lisp (by sol swords)
(defun easy-simplify-term1-fn (term hyps hints equiv
                              normalize rewrite
                              repeat
                              backchain-limit
                              state)
  (declare (XargS :mode :program :stobjs state))
  (b* ((world (w state))
       
       ((er hint-settings)
        (acl2::translate-hint-settings
         'simp-term "Goal" hints 'easy-simplify-term world state))
       (ens (acl2::ens state))
       (base-rcnst
        (acl2::change acl2::rewrite-constant
                acl2::*empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((er rcnst)
        (acl2::load-hint-settings-into-rcnst
         hint-settings base-rcnst nil world 'easy-simplify-term state))
       (ens (acl2::access acl2::rewrite-constant rcnst :current-enabled-structure))
       ((mv flg hyps-type-alist ?ttree)
        (acl2::hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state))
       ((mv ?step-limit new-term ?new-ttree state)
        (acl2::pc-rewrite*
         term hyps-type-alist
         (if (eq equiv 'acl2::equal)
             nil
           (list (acl2::make acl2::congruence-rule
                       :rune acl2::*fake-rune-for-anonymous-enabled-rule*
                       :nume nil
                       :equiv equiv)))
         (eq equiv 'acl2::iff)
         world rcnst nil nil normalize rewrite ens state
         repeat backchain-limit
         (acl2::initial-step-limit world state))))
    (value new-term)))

(def simplify-term (term hyps hints state)
  (decl :sig ((pseudo-term pseudo-term-list true-list state) 
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify term under hyps. erp is T if hyps have a contradiction
  in them. return the simplifed term in error triple")
  (easy-simplify-term1-fn term hyps hints 'acl2::equal 't 't 1000 1000 state))



; TODO: WHat will happen if some variable gets elided during this
; simplifcation?  Then our code breaks, especially rem-vars logic and capturing
; full assignment.

(def simplify-hyps1-under-assignment (rem-hyps init-hyps x a hints ans. vl state)
  (decl :sig ((pseudo-term-list pseudo-term-list symbol quoted-constant true-list pseudo-term-list bool state)
              -> (mv erp pseudo-term state))
        :mode :program
        :doc "simplify each hyp in rem-hyps assuming init-hyps (minus
  hyp), accumulate in ans. and return a value triple containing shyps
  and an error triple if a contradiction is found in an syhp")
  (if (endp rem-hyps)
      (value ans.)
    (b* ((hyp         (car rem-hyps))
         (other-hyps  (remove1-equal hyp init-hyps))
         ((er shyp)   (simplify-term hyp other-hyps hints state))
         (simplified? (term-order shyp hyp))
         ((when (equal shyp ''nil)) ;contradiction
          (mv T ans. state))
; 27th Aug '12. FIXED a bug in testing-regression.lsp. In incremental mode
; the assert$ that x should not be in the free vars of the conjecture
; was being violated because I was naively checking against term-order.
; But in the case of small-posp, the type assumptions that could have been
; brought to ACL2's attention using compound-recognizer rules were hidden
; leading to a big IF term being generated in shyp.
; SO now if the above happens(I should give a warning here), at the very
;  least I subst the assignment in hyp.
         (- (cw? (and (system-debug-flag vl) 
                      (not simplified?))
             "~|ACHTUNG: simplify-hyps result not less than hyp in term-order~|"))
         (shyp (if simplified? shyp (subst a x hyp))))
     
      (simplify-hyps1-under-assignment 
       (cdr rem-hyps) init-hyps x a hints
       (if (equal shyp ''t) ans.
         (append ans. (list shyp))) ;dont mess with order
       vl state))))

(def simplify-hyps-under-assignment (hyps x a vl state)
  (decl :sig ((pseudo-term-list symbol quoted-constant boolean state) 
              -> (mv erp pseudo-term-list state))
        :mode :program
        :doc "simplify hyps assuming x=a. return shyps in an error
        triple. erp=T if contradiction found in shyps")
  (b* ((eq-hyp (list 'acl2::equal x a)) ;variable comes first
      ((er shyps1) (simplify-hyps1-under-assignment hyps (list eq-hyp) x a '() '() vl state)))
;I do the above and then again simplify to get order-insensitive list of
;simplified hypotheses i.e the order of the hyps in the argument should not
;change the result of this function.
   (simplify-hyps1-under-assignment shyps1 (cons eq-hyp shyps1) x a '() '() vl state)))
                      
(def propagate (x a hyps concl vl state)
  (decl :sig ((symbol pseudo-term ;actually a quoted constant
                      pseudo-term-list pseudo-term fixnum state)
              -> (mv erp (list pseudo-term-list pseudo-term) state))
        :mode :program
        :doc "propagate the assignment of a to variable x by using a utility
  function from tools/easy-simplify.lisp (earlier I was using
  expander.lisp). return (mv erp (shyps sconcl) state) where erp might be T
  indicating discovery of inconsistency/contradiction in the hypotheses")
 (b* (((er shyps)  (simplify-hyps-under-assignment hyps x a vl state))
;IMP: sconcl shud be a pseudo-term; not a term-list, or an IF
      (- (cw? (debug-flag vl)
"~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" hyps x a shyps))
      (eq-hyp (list 'equal x a)) ;variable comes first
      ((er sconcl) (simplify-term concl (cons eq-hyp shyps) nil state))
      (- (cw? (debug-flag vl)
"~|CEGen/Debug/Propagate: ~x0 ---~x1=~x2--> ~x3~|" concl x a sconcl))
;TODO: this following check is causing problem in regression
; May 13 '12
      ;; ((when (or (pseudo-term-listp sconcl)))
;;                  ;(eq (ffn-symb sconcl) 'IF)))
;; ;IF is okay for an and in the conclusion. But will we ever get an IF from
;; ;inside test-checkpoint??
;;        (mv (prog2$ 
;;             (cw? (normal-output-flag vl)
;; "~|BAD: conclusion got reduced to something we dont want!!~|")
;;             T)
;;            (list shyps sconcl) state))
      (vars (all-vars-lst (cons sconcl shyps))))
  (assert$ (not (member-eq x vars)) (mv NIL (list vars shyps sconcl) state))))
                  

(defun put-val-A (name val dlist) ;use mset instead?
  (declare (xargs :guard (symbol-doublet-listp dlist)))
  (cond ((endp dlist) (list (list name val)))
        ((equal name (caar dlist))
         (cons (list name val) (cdr dlist)))
        (t (cons (car dlist)
                 (put-val-A name val (cdr dlist))))))

;; (def update-A-after-propagate (x a new-vars old-vars A.)
;;   (decl :sig ((symbol quoted-constant symbol-list symbol-list symbol-doublet-list) -> symbol-doublet-list)
;;         :doc "A[x]:=a, for elimed-vars do y:='?." ;TODO: use bindings-lst from ttree like we do elsewhere.
;;         )
;;   (b* ((elimed-vars (remove-duplicates-eq (set-difference-eq old-vars (cons x new-vars))))
;;        (A. (put-val-A x a A.)) ;use (mset x (list a) A) instead?
;;        (rst (pairlis$ elimed-vars (make-list (len elimed-vars)
;;                                              :initial-element 
;;                                              (list (kwote 'ACL2::?))))))
;;     (append rst A.)))
    



; a% represents the snapshot of the beginning of the dpll do-while loop
(defrec a% ((hyps concl vars partial-A type-alist tau-interval-alist) ;args to simple search
            ((var . cs) val kind i . inconsistent?) ;result of assign and propagate
            ) 
  NIL)
;Take special note of field names: test-outcomes and gcs, % is intentionally not
;used in these field names
(defun a%-p (v)
  (declare (xargs :guard T))
  (case-match v
    (('a% (hyps concl vars partial-A type-alist tau-interval-alist) 
          ((var . cs) val kind i . inconsistent?))

     ;==>
     (and (symbol-listp vars)
          (pseudo-term-listp hyps)
          (pseudo-termp concl)
          (symbol-doublet-listp partial-A)
          (symbol-alistp type-alist)
          (symbol-alistp tau-interval-alist)
          (symbolp var)
          (pseudo-termp val)
          (member-eq kind (list :na :implied :decision))
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



;TODO- prove a theorem that the above two fns are inverses


; defabbrev was a BAD idea. I should make this a defun, to avoid variable
; capture bugs. For example I was assigning .. :var x ... instead of :var x1
; below, where x would have been the previously selected variable and unless I
; tested carefully I would not have gotten hold of this simple programming err.
; May 24th '12: making this into a defun
; 18 July '13 -- modified to a simplified signature
(def assign-propagate (a% name sm vl ctx state)
  (decl :sig ((a% string sampling-method 
                  fixnum symbol state)
              -> (mv erp (list pseudo-term-list pseudo-term symbol-list 
                               symbol-doublet-list symbol-alist symbol-alist a%) state))
        :mode :program
        :doc "assign a value to a%.x and propagate this new info to obtain the updated a%")
  (b* ((`(a% ,LV . &) a%)
;ACHTUNG: a% defrec exposed
        ((list H C vars partial-A type-alist tau-interval-alist) LV)
        ((mv x i) (mv (access a% var) (access a% i)))
        (wrld (w state))
        (cs% (or (access a% cs)
                 (assert$ (member-eq x vars)
                          (cdr (assoc-eq x (collect-constraints% 
                                             H vars type-alist tau-interval-alist
                                             vl wrld))))))
;DESIGN decision: not taking into account type constraint from nconcl at the moment.
       
       ((mv erp ans state) (assign-value x i cs% partial-A sm vl ctx wrld state ))
       ((when erp)
        (progn$
         (cw? (normal-output-flag vl)
              "~|CEGen/Error/incremental: assign-value failed (in ~s0).~|" name)
         (cw? (verbose-stats-flag vl)
              "~|CEGen/Stats: Call was (assign-value ~x0 ~x1 ~x2 ...)~|" x i cs%)
         (mv erp nil state)))
        
       ((list a kind i) ans)

       (a% (acl2::change a% a% :cs cs% :val a :kind kind :i i))
       
       ((mv erp res state) (propagate x a H C vl state))
       (str (if erp "inconsistent" "consistent"))
       (- (cw? (verbose-stats-flag vl)
               "~%CEgen/Stats/incremental: Propagate ~x0 := ~x1 (i:~x3) was ~s2.~|" x a str i)))

; But do update i in a% always, and partial-A when consistent
   (if erp 
       (value (list  '() ''t '() '() '() '() ;is it ok to give back empty alists?
                 (acl2::change a% a% :inconsistent? T)))
     ;else 
     (b* (((list vars~ H~ C~) res)
          (cl~ (clausify-hyps-concl H~ C~))
          ;(name~ (acl2::concatenate 'acl2::string name " incremental " (to-string x) " i=" (to-string i)))
          (type-alist~ (get-acl2-type-alist cl~ vars~))
          (tau-interval-alist~ (tau-interval-alist-clause cl~ vars~))
          (- (cw? nil "~% new ta = ~x0 and old ta = ~x1~%" type-alist~ type-alist))
          (- (cw? nil "~% new tau-int-alist = ~x0 and old tau-int-alist = ~x1~%" tau-interval-alist~ tau-interval-alist))
          (partial-A~  (put-val-A x a partial-A)) ; partial-A is a symbol-doublet-listp
          )
       

       (value (list H~ C~ vars~ partial-A~ type-alist~ tau-interval-alist~
                     (acl2::change a% a%
                                   :inconsistent? NIL)))))))


;mutually tail-recursive incremental (dpll) search prodecure
(defs 
  (incremental-search (a% A. 
                          name  mv-sig-alist ;subgoal params
                          test-outcomes% gcs%
                          N vl sm blimit num-cts num-wts timeout-secs
                          top-vt-alist
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
                 fixnum fixnum (enum *sampling-method-values*) fixnum fixnum fixnum rational
                 variable-alist
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
                                             H C vars partial-A type-alist tau-interval-alist
                                             mv-sig-alist
                                             test-outcomes% gcs%
                                             N vl sm num-cts num-wts timeout-secs
                                             top-vt-alist
                                             programp t
                                             ctx state))
         (backtrack... () (backtrack a% A.
                                     name mv-sig-alist
                                     test-outcomes% gcs%
                                     N vl sm blimit num-cts num-wts timeout-secs
                                     top-vt-alist
                                     programp
                                     ctx state))
         
         (recurse... () (incremental-search a% A.
                                            name mv-sig-alist
                                            test-outcomes% gcs%
                                            (floor N (1+ (len A.))) ;geometrically decrease num of trials TODO revisit
                                            vl sm blimit num-cts num-wts timeout-secs
                                            top-vt-alist
                                            programp
                                            ctx state)))

      (b* (((mv erp ap-res state) ;snapshot a% moves to second stage/form
            (trans-eval `(assign-propagate ',a% ',name ',sm ',vl ',ctx state)
                        ctx state t))
           ((when erp) ;error in assign value
            (prog2$
             (cw? (normal-output-flag vl)
                  "~|CEGen/Error: Aborting incremental search!~|")
             (mv T (list NIL test-outcomes% gcs%) state)))
           ((list H C vars partial-A type-alist tau-interval-alist a%) (cadr (cdr ap-res))))
      

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
                (x1 (select (cons (dumb-negate-lit C) H) (debug-flag vl)))
                (a% (acl2::make a% 
                                :vars vars :hyps H :concl C 
                                :partial-A partial-A
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
                 N vl sm blimit num-cts num-wts timeout-secs
                 top-vt-alist
                 programp
                 ctx state)
; when called from incremental, either contradiction in hyps[x=a] or simple-search failed on P of zero/one variable
    (decl :sig (( a%-p a%-listp 
                 string variable-alist
                 test-outcomes%-p gcs%-p
                 fixnum fixnum (enum *sampling-method-values*) fixnum fixnum fixnum rational
                 variable-alist
                 boolean
                 symbol state) 
                -> (mv erp (list boolean test-outcomes% gcs%) state))
         :mode :program
         :doc "backtrack in dpll like search")
   
    (if (or (eq (access a% kind) :implied) 
            (> (access a% i) blimit)) 
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
                      N vl sm blimit num-cts num-wts timeout-secs
                      top-vt-alist
                      programp
                      ctx state)))

;     ELSE a% has a decision which has not reached its backtrack limit
      (incremental-search a% A. 
                          name mv-sig-alist
                          test-outcomes% gcs%
                          (floor N (1+ (len A.)))
                          vl sm blimit num-cts num-wts timeout-secs
                          top-vt-alist
                          programp
                          ctx state))))





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


(defmacro get1 (param alist &optional default-value)
  "get the default value of param as found in alist. if not found return default-value"
  `(b* ((e (assoc-eq ,param ,alist)))
     (if e
         (cdr e)
       ,default-value)))

;;; The Main counterexample/witness generation function           
(def cgen-search-local (name H C
                          type-alist tau-interval-alist
                          programp top-vt-alist
                          defaults ;(params)
                          test-outcomes% gcs%
                          ctx state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list
                      symbol-alist symbol-alist
                      boolean variable-alist
                      cgen-params-p
                      test-outcomes%-p gcs%-p
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

  
  (b* ((N (get1 :num-trials defaults 0)) ;shudnt it be 100?
;Note: I dont need to provide the default arg 0 above, since we are
;sure the defaults alist we get is complete i.e it would definitely
;contain the key ':num-trials'. But I am envisioning a scenario, where
;I might call this function on its own and not via test?, then this
;functionality is useful for debugging.
       (vl (get1 :verbosity-level defaults 1))
       (sm (get1 :sampling-method defaults :uniform-random))
       (ss (get1 :search-strategy defaults :simple))
       (blimit (get1 :backtrack-limit defaults 2))
       (num-cts (get1 :num-counterexamples defaults 3))
       (num-wts (get1 :num-witnesses defaults 3))
       (timeout-secs (get1 :cgen-local-timeout defaults 10))
; mv-sig-alist : for each mv fn in H,C, stores its output arity
       (mv-sig-alist (mv-sig-alist (cons C H) (w state)))
       (vars (vars-in-dependency-order H C vl (w state))))
         
  
;   in
    (case ss ;search strategy
      (:simple      (simple-search name 
                                   H C vars '()
                                   type-alist tau-interval-alist mv-sig-alist
                                   test-outcomes% gcs% 
                                   N vl sm num-cts num-wts timeout-secs
                                   top-vt-alist
                                   programp nil
                                   ctx state))
      

      (:incremental (if (or (endp vars)
                            (endp (cdr vars)))
;bugfix 21 May '12 - if only one or zero var, call simple search
                        (simple-search name
                                       H C vars '()
                                       type-alist tau-interval-alist mv-sig-alist
                                       test-outcomes% gcs% 
                                       N vl sm num-cts num-wts timeout-secs
                                       top-vt-alist
                                       programp nil
                                       ctx state)
                      
                      (b* ((- (cw? (verbose-stats-flag vl) 
                                   "~%~%CEgen/Note: Starting incremental (dpll) search~%"))
                           (x0 (select (cons (dumb-negate-lit C) H) (debug-flag vl)))
                           (a% (acl2::make a% ;initial snapshot
                                           :vars vars :hyps H :concl C 
                                           :partial-A '()
                                           :type-alist type-alist
                                           :tau-interval-alist tau-interval-alist
                                           :inconsistent? nil :cs nil
                                           :var x0 :val ''? :kind :na :i 0)))
;                         in
                        (incremental-search a% '() ;vars has at least 2
                                            name mv-sig-alist
                                            test-outcomes% gcs%
                                            N vl sm blimit num-cts num-wts timeout-secs
                                            top-vt-alist
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
                      symbol-alist symbol-alist symbol-alist
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
  - type-alist :: types inferred by caller (using ACL2 forward-chain)
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
         (vars (vars-in-dependency-order H C vl (w state)))
         (s-hist-entry% (initial-s-hist-entry% name H C vars elide-map start))
         (test-outcomes% (access s-hist-entry% test-outcomes))
         (gcs% (cget gcs))
         (params (cget params))
         (top-vt-alist (cget top-vt-alist))
         ((mv erp res state) (cgen-search-local name H C
                                                type-alist tau-interval-alist
                                                programp top-vt-alist
                                                params
                                                test-outcomes% gcs%
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

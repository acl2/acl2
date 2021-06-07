#|$ACL2s-Preamble$;
;; Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "CGEN")

(include-book "cgen-state")

(include-book "type")

(include-book "simple-graph-array")
(include-book "acl2s/defdata/random-state" :dir :system)

(include-book "infer-enum-shape")
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
;;; N i seed tuple) -> seed' * tuple' * A' Given the sampling method,
;;; num-trials, local-trial number, the current random seed, the
;;; current nth-tuple (of nats), it computes the full assignment
;;; (sigma) to be used in the upcoming test run and also returns the
;;; updated seed and updated nth-tuple
(defstub next-sigma (* * * * *) => (mv * * *))


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


; [2016-09-05 Mon] add mv-list to mv function-calls, except for those who already have it
(defs 
  (mv-list-ify (term mv-sig-alist)
    (decl :sig ((pseudo-term symbol-list) -> pseudo-term)
          :doc "wrap all mv fn calls with mv-list")
    (if (variablep term)
        term
      (if (fquotep term)
          term
        (b* ((fn (ffn-symb term))
             ;; already mv-list-ed so ignore
             ((when (eq fn 'MV-LIST)) term)

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

(def-const *sampling-method-values*
  '(:random :uniform-random :be :mixed)) ;redundant if not for package diff

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

(set-verify-guards-eagerness 1)

(def run-single-test. (vl sampling-method N i r. BE. single-test-timeout)
  (decl
   :sig
   ((fixnum keyword fixnum fixnum fixnum symbol-fixnum-alist rational) 
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
  (declare (ignorable single-test-timeout))
  
  (b* ((sm (local-sampling-method sampling-method i N))
       ((mv A r. BE.) (next-sigma sm N i r. BE.))
       (- (cw? (system-debug-flag vl) 
               "~|Cgen/Sysdebug/run-single: A: ~x0 seed: ~x1~%" A r.))
       (|not vacuous ?|
        #+sb-thread
        (acl2::with-timeout1 single-test-timeout
                             (hypotheses-val A)
                             nil)
        #-sb-thread
        (hypotheses-val A)
        )
       (hyp-vals (and (verbose-stats-flag vl) (hyp-val-list A)))
       (- (cw? (and (system-debug-flag vl)
                    (not |not vacuous ?|)) 
               "~|Cgen/Sysdebug/run-single: hyp-vals : ~x0~%" hyp-vals)))
;  in
    (if |not vacuous ?|
        ;; bugfix: why even try to evaluate conclusion when
        ;; the hypotheses are not satisfied, the whole form's value
        ;; is simply true - May 2nd '12
        (b* ((conc
              #+sb-thread
              (acl2::with-timeout1  single-test-timeout
                                    (conclusion-val A)
                                    0)
              #-sb-thread
              (conclusion-val A)
              )
             (res (cond ((eql conc 0) :vacuous)
                        (conc :witness)
                        (t :counterexample))))
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
  (implies (consp (cdr x))
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
(def record-testrun. (test-result hyp-vals A num-print-cts num-print-wts vl test-outcomes% gcs%)
  (decl
   :sig ((keyword true-listp symbol-doublet-listp fixnum fixnum fixnum test-outcomes%-p gcs%-p)
         ->
         (mv test-outcomes%-p gcs%-p))
   :doc 
   "?: records (accumulates) the outcome of a single test trial run ")
  (b* ((A (merge-sort-car-symbol-< A))
       (gcs% (gcs-1+ runs)))
;   in
    (case test-result
      (:counterexample
       (b* ((A-cts (access test-outcomes% cts))
            ((when (member-equal A A-cts))
             (mv (test-outcomes-1+ dups) (gcs-1+ dups))) ;ignore A
                                                                                       
            (gcs% (gcs-1+ cts))
            (m    (access test-outcomes% |#cts|))
            (test-outcomes% ;TODO:per subgoal num-cts stored??
             (if (< m num-print-cts) ;dont store extra unless
                 (b* ((test-outcomes% (change test-outcomes% cts (cons A A-cts))))
                   test-outcomes%)
               test-outcomes%))
            (test-outcomes% (if (verbose-stats-flag vl)
                                (change test-outcomes% cts-hyp-vals-list
                                        (cons hyp-vals (access test-outcomes% cts-hyp-vals-list)))
                              test-outcomes%))
            (test-outcomes%   (test-outcomes-1+ cts)))
;                              in
         (mv test-outcomes% gcs%)))


      (:witness
       (b* ((A-wts (access test-outcomes% wts))
            ((when (member-equal A A-wts))
             (mv (test-outcomes-1+ dups) (gcs-1+ dups)))
                             
            (gcs% (gcs-1+ wts))
            (m    (access test-outcomes% |#wts|))
            (test-outcomes%   
             (if (< m num-print-wts)
                 (b* ((test-outcomes% (change test-outcomes% wts (cons A A-wts))))
                   test-outcomes%)
               test-outcomes%))
            (test-outcomes% (if (verbose-stats-flag vl)
                                (change test-outcomes% wts-hyp-vals-list
                                        (cons hyp-vals (access test-outcomes% wts-hyp-vals-list)))
                              test-outcomes%))
            (test-outcomes%   (test-outcomes-1+ wts))) ;BUGGY -- we dont know if its a duplicate. FIXME
;                         in       
         (mv test-outcomes% gcs%)))

                                             
      (:vacuous
       (b* ((A-vacs (access test-outcomes% vacs))

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
             (if (or (< m (acl2::+f num-print-wts num-print-cts))
                     (verbose-stats-flag vl)) ;[2015-04-07 Tue]

; TODO: [2014-04-26 Sat] To (post-) diagnose vacuous tests, we ought
; to store or at least provide a way to do on-the-fly
; diagnosis. Provide a hook here?
                 (change test-outcomes% vacs (cons A A-vacs))
               test-outcomes%))
            (test-outcomes%   (test-outcomes-1+ vacs)))
;                         in
         (mv test-outcomes% gcs%)))
                             
      (otherwise
       (prog2$ (er hard 'test? "not possible") 
               (mv test-outcomes% gcs%))))))


(def run-n-tests. (n r. BE. test-outcomes% gcs% vl cgen-state)
  (decl
   :sig
   ((fixnum fixnum symbol-fixnum-alist test-outcomes% gcs% fixnum cgen-state)
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
   test-outcomes% stores testrun results.
   gcs% is the global/top-level (testing) coverage statistics.
   vl is verbosity-level (the current cgen default)
   cgen-state is the current cgen context
   

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

       (num-trials (cget num-trials))
       (num-cts (cget num-counterexamples))
       (num-wts (cget num-witnesses))

       ((when (stopping-condition? gcs% num-cts num-wts))
;return, cos we have reached our goal  
         (mv T r. test-outcomes% gcs%))

       (local-trial-num  (acl2::|1+F| (acl2::-f num-trials n)))

       (single-test-timeout (cget cgen-single-test-timeout))

       ((mv res hyp-vals A r. BE.) ; res = test value  A= value-bindings
        (run-single-test.
         vl (cget sampling-method) num-trials local-trial-num  r. BE. single-test-timeout))
       
       (num-print-cts (cget num-print-counterexamples))
       (num-print-wts (cget num-print-witnesses))
       ((mv test-outcomes% gcs%)
        (record-testrun. res hyp-vals A num-print-cts num-print-wts vl test-outcomes% gcs%))
       
       (- (cw? (system-debug-flag vl) 
               "~|Cgen/Sysdebug/run-n-tests: Finished run n: ~x0 -- got ~x1~|" n res)))
;  in   
    (run-n-tests. (acl2::|1-F| n) r. BE. test-outcomes% gcs% vl cgen-state)))


;; Pre Condition: hypothesis-val, conclusion-val and next-sigma have been
;; attached when this function is called!
(def run-tests. (rseed. BE. test-outcomes% gcs% vl cgen-state)
   (decl
    :sig
    ((fixnump symbol-fixnum-alistp test-outcomes%-p gcs%-p fixnump cgen-state)
     -> (mv boolean fixnum test-outcomes% gcs%))
;:trace T
    :doc 
    "?: Run a bunch of simple random/bounded-exhaustive tests/trials to
  find cts/wts for formula under test")
;do timeout wrapper here!        
  (b* (((mv stop? rseed. test-outcomes% gcs%)
        (run-n-tests. (cget num-trials) rseed. BE. test-outcomes% gcs% vl cgen-state))
       
       (- (cw? (system-debug-flag vl) 
               "~|Cgen/Sysdebug/run-tests.: test-outcomes%: ~x0 ~|gcs%: ~x1~%" test-outcomes% gcs%)))
   ;;in
    (mv stop? rseed. test-outcomes% gcs%)))

;bugfix May 24 '12
;partial-A needs to be quoted to avoid being confused with function app
(def kwote-symbol-doublet-list (A)
  (decl :sig ((symbol-doublet-listp) -> quoted-constantp))
  (if (endp A)
      nil
    (cons (list 'list (kwote (caar A)) (cadar A))
          (kwote-symbol-doublet-list (cdr A)))))



;[2016-09-05 Mon] elim bindings are now b* bindings, so instead of strip-cars,
;use a custom function to get all bound variables

(defloop strip-bound-vars (b*-bindings)
  ; x is either a (var value) or ((mv . vars) value)
  (for ((x in b*-bindings))
       (append (if (and (consp (car x)) (eq 'MV (car (car x))))
                   (remove-eq 'ACL2::& (cdr (car x)))
                 (list (car x))))))

(include-book "select")

(def make-next-sigma-defuns
     (hyps concl partial-A elim-bindings fixer-bindings top-vt-alist
           type-alist tau-interval-alist programp N i use-fixers-p vl state)
     (decl :sig ((pseudo-term-list pseudo-term symbol-doublet-listp
                  symbol-doublet-listp symbol-doublet-listp
                  symbol-doublet-listp alist symbol-alist
                  boolean fixnum fixnum boolean fixnum plist-worldp) 
              -> (mv erp all symbol-alist))
        :doc "return the defun forms defining next-sigma function, given a
        list of hypotheses and conclusion (terms). Also return the enum-alist to be displayed")
  (declare (xargs :verify-guards nil))
  (f* ((defun-forms ()
         `((defun next-sigma-current (sampling-method N i seed. BE.)
             "returns (mv A seed. BE.)"
             (declare (ignorable sampling-method N i)) ;in case ord-vs is nil
             (declare (type (unsigned-byte 31) seed.))
             (declare (xargs :verify-guards nil
                             :mode :program ;New defdata has program-mode enumerators -- Sep 1 2014
                             :guard (and (member-eq sampling-method
                                                    '(:random :uniform-random :be))
                                         (unsigned-byte-p 31 N)
                                         (unsigned-byte-p 31 i)
                                         (unsigned-byte-p 31 seed.)
                                         (symbol-unsigned-29bits-alistp BE.)
                                         (consp BE.) ;precondition TODOcheck
                                         (and ,@(make-guard-var-assoc-eq
                                                 (strip-cars v-cs%-alst)
                                                 'BE.)))
                             :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))))
             ,(make-next-sigma_mv-let v-cs%-alst '() N i use-fixers-p vl wrld
; sigma will be output as a let-bindings i.e symbol-doublet-listp
                                      `(B* ,(append partial-A fixer-bindings elim-bindings)
                                          (mv ,(make-var-value-list-bindings
                                                (remove-duplicates-eq
                                                 (union-eq (strip-cars v-cs%-alst)
                                                           (strip-cars partial-A)
                                                           (strip-bound-vars fixer-bindings)
                                                           (strip-bound-vars elim-bindings))) '())
                                              seed. BE.))))
           (defun next-sigma-current-gv (sampling-method N i seed. BE.)
             (declare (xargs :mode :program ;New defdata has program-mode enumerators -- Sep 1 2014
                             :guard T :verify-guards ,(not programp)))
;(declare (type (unsigned-byte 31) seed.))
             (ec-call (next-sigma-current sampling-method N i seed. BE.))))))

; Invariant: v-cs%-alst. should obey a dependency order such that the
; final enum-call alist when converted to a let* will obey the
; dependency order of evaluation. This is mostly satisfied, as
; ord-vars does take care of this. But put-var-eq-constraint. might
; change this, where an extra dependency is created because of type
; information that was ignored during creation of ord-vs, so there is
; an ugly hack in place to reorder in the middle of put-var-eq-constraint.
       
    (b* ((wrld (w state))
         (ord-vs (vars-in-dependency-order hyps concl vl wrld))
         ;(- (cw "ord-vs is ~x0 and the freshly computed ord-vs1 is ~x1~%" ord-vs ord-vs1))
         (v-cs%-alst (collect-constraints% (cons (cgen-dumb-negate-lit concl) hyps)
                                           ord-vs
                                           top-vt-alist
                                           type-alist tau-interval-alist vl wrld))


        ;; ((mv erp var-enumcalls-alist) (make-enumerator-calls-alist v-cs%-alst vl wrld '()))
        ;; ((when erp) (mv erp '() '()))
        )
;   in
    (mv nil (defun-forms) (displayed-enum-alist v-cs%-alst '())))))









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
               "~|Cgen/Stats/simple-search: ~x0/~x1 cts/wts found in this run (~x2 tests)!~|" found-cts found-wts n))
       (- (cw? t
               "~|Cgen/Stats/simple-search: *END* Stopping condition: ~x0~%~%" stop?)))
    nil))
       

; pushed the with-timeout wrapper into the trans-eval make-event of simple-search to get saner cgen::event-stack behavior
; [2015-02-04 Wed] The reason in the above note is irrelevant now that we disallow nested testable events. 
(defun run-tests-with-timeout (vars test-outcomes% gcs% vl cgen-state state)
  (acl2::with-timeout1 
   (cget cgen-local-timeout)
   (b* (;((mv rseed. state) ) (acl2::random$ defdata::*M31* state) ;Lets try CL's builtin random number generator
        (rseed. (defdata::getseed state))
        (- (cw? (system-debug-flag vl)
                "~|Cgen/Sysdebug/run-tests: starting SEED: ~x0 ~%" rseed.))
        (BE.    (pairlis$ vars (make-list (len vars) :initial-element 0)))
        ((mv stop? rseed. test-outcomes% gcs%)
         (run-tests. rseed. BE. test-outcomes% gcs% vl cgen-state))
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
     (b* (((mv & (the (unsigned-byte 31) rseed.))
           (defdata::genrandom-seed 2 (defdata::getseed state)))
          (state (defdata::putseed rseed. state))) ;make some progress -- dont get stuck on the same sequence of seeds
       (value nil))
     (assign ss-temp-result :timed-out)
     (mv T nil state)))))

(defloop filter-var-eq-hyps (hyps)
  (for ((hyp in hyps))
       (when (is-var-equality-hyp hyp)
         (collect hyp))))



;; 1st April 2013 Fix
;; You cannot trust make-event to give the right result
;; through trans-eval. Just use a state temp global.
;; This bug manifests, when you use (skip-proofs ....)

(def simple-search (name 
                    hyps concl vars partial-A
;[2015-09-19 Sat] added support for refine/expand in assign-value of incremental-search
;[2016-04-03 Sun] elim-bindings will also suffice for incorporating fixers!!
                    elim-bindings 
                    type-alist tau-interval-alist
                    mv-sig-alist
                    test-outcomes% gcs%
                    vl cgen-state
                    programp incremental-flag?
                    ctx state)
  (decl :sig ((string pseudo-term-list pseudo-term symbol-list symbol-doublet-listp
                      symbol-doublet-listp
                      alist variable-alist
                      variable-alist
                      test-outcomes% gcs%
                      fixnum cgen-state
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
  3. make next-sigma defun and attach it
  4. call run-tests!.
  5. store/record information (test-outcomes%,gcs%) and 
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
                             (cget num-print-counterexamples) (cget num-print-witnesses)
                             vl test-outcomes% gcs%)))

;       in
        (prog2$
         (if partial-A
             (cw? (verbose-flag vl)
              "~%Cgen/Note: No point in searching ~x0; it evals to const ~x1 under ~x2~|" name c partial-A)
             (cw? (verbose-flag vl)
              "~%Cgen/Note: No point in searching ~x0; it evals to const ~x1~|" name c))
         (mv erp (list NIL test-outcomes% gcs%) state)))

;ELSE atleast one variable
  (b* ((- (assert$ (consp vars) 'simple-search))
       (- (cw? (verbose-flag vl) "~%~%"))
       (- (cw? (verbose-stats-flag vl) 
               "~|Cgen/Stats/simple-search:: *START*~|"))

       (hyp-val-defuns   (make-hypotheses-val-defuns hyps vars mv-sig-alist programp))
       (concl-val-defuns (make-conclusion-val-defuns concl vars mv-sig-alist programp))
;       [2015-04-07 Tue]
;       Order of hyps is important -- Values of each hyp is stored in seq
       (hyp-val-list-defuns (make-hyp-val-list-defuns hyps vars mv-sig-alist programp))
       

       ;;[2016-04-03 Sun] Added support for fixers
       ((mv erp fxr-res state)
        (if (cget use-fixers)
            ;; reify all eq hyps that are true in the ACL2 context.
            (b* ((eq-hyps (filter-var-eq-hyps (reify-type-alist-hyps type-alist))))
              (fixer-arrangement (union-equal eq-hyps hyps) concl vl ctx state))
          (value (list nil nil))))
       ((list fixer-bindings additional-fxr-hyps) fxr-res)
       
       ((when erp)
        (prog2$ 
           (cw? (and (normal-output-flag vl) (cget use-fixers))
                "~|Cgen/Error: Couldn't compute fixer bindings. Skip searching ~x0.~|" name)
           (mv t (list nil test-outcomes% gcs%) state)))
       
;       (new-fxr-vars (set-difference-equal (acl2::all-vars1-lst additional-fxr-hyps '()) vars))
       (- (cw? (and (verbose-stats-flag vl) additional-fxr-hyps)
               "~|Cgen/Note: Additional Hyps for fixers: ~x0~|" additional-fxr-hyps))
       
       (acl2-vt-dlist (var-types-alist-from-acl2-type-alist type-alist vars '()))
       ((mv erp top+-vt-dlist) (meet-type-alist acl2-vt-dlist (cget top-vt-alist) vl (w state)))
       (top+-vt-dlist (if erp (make-weakest-type-alist vars) top+-vt-dlist))
       ((mv erp next-sigma-defuns disp-enum-alist)
        (make-next-sigma-defuns (union-equal additional-fxr-hyps hyps) concl
;(append new-fxr-vars vars)  Compute it again afresh [2016-10-29 Sat]
                                partial-A elim-bindings fixer-bindings
                                top+-vt-dlist
                                type-alist tau-interval-alist
                                t ; programp ;;Aug 2014 -- New defdata has program-mode enumerators
                                (cget num-trials)
                                0
                                (cget use-fixers)
                                vl state))
       ((when erp)
        (prog2$ 
           (cw? (normal-output-flag vl)
                "~|Cgen/Error: Couldn't determine enumerators. Skip searching ~x0.~|" name)
           (mv t (list nil test-outcomes% gcs%) state)))

       ;;[2016-04-25 Mon] record these for later printing in vacuous-stats
       (fxr-elim-bindings (append fixer-bindings elim-bindings))
       (test-outcomes% (change test-outcomes% disp-enum-alist disp-enum-alist))
       (test-outcomes% (change test-outcomes% elim-bindings fxr-elim-bindings))
       
       (- (cw? (system-debug-flag vl) 
               "~|Cgen/Sysdebug: next-sigma : ~| ~x0~|" next-sigma-defuns))
       (- (cw? (verbose-flag vl) 
               "~|Cgen/Note: Enumerating ~x0 with ~%~x1~%" name disp-enum-alist))
       (- (cw? (and (verbose-flag vl) elim-bindings)
               "~|Cgen/Note: Fixer/Elim bindings: ~%~x0~|" fxr-elim-bindings))

       
; print form if origin was :incremental
       (cl (clausify-hyps-concl hyps concl))
       (pform (acl2::prettyify-clause cl nil (w state)))
       (- (cw? (and incremental-flag? (verbose-flag vl)) 
               "~| incrementally on ~x0 under assignment ~x1~%" pform (append partial-A elim-bindings)))

       ;;initialize temp result
       ((er &) (assign ss-temp-result :init))

       (call-form   
        `(acl2::state-global-let*
; :none is almost half as slow!!!  TODO: Do testing in two phases. First check
; for guard violations, if yes, print and proceed with :none, else use nil or t
; for faster execution speed.
;          ((acl2::guard-checking-on ,(if (or t programp) :none nil))

;; PETE: now controlled by the global cgen::cgen-guard-checking
          ((acl2::guard-checking-on (@ cgen-guard-checking))
           (acl2::inhibit-output-lst
                    ,(if (system-debug-flag vl)
                         ''(summary)
                       ;;shut everything except error
                       (quote #!acl2(remove1-eq 'error *valid-output-names*)))))
                  
          (run-tests-with-timeout ',vars ',test-outcomes% ',gcs% ',vl ',cgen-state state)))

      
       
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
       
     `(with-output :stack :pop ,@(and (not (debug-flag vl)) '(:off :all))
        (STATE-GLOBAL-LET*
         ((LD-SKIP-PROOFSP 'ACL2::INCLUDE-BOOK)
          (INSIDE-SKIP-PROOFS T)
          )
         (er-progn
        (encapsulate () ; Matt's tip
; added 2nd May '12. Support program context
          ,@(and programp '((program)))

; [2016-02-28 Sun] In local contexts, an explicit (defttag :cgen) is not allowed!
; ACHTUNG -- Ask Matt if this is okay!!
          (table acl2::acl2-defaults-table :ttag :cgen-testing-driver-loop)

;; ; [2014-09-22 Mon] Instead of make-event, using redef. (Is this thread-safe?)
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
          ;; ; remove trust tag
          ;; (table acl2::acl2-defaults-table :ttag 'nil)
          ) ;end of progn
          ,call-form
          (mv t nil state) ;always give error, to abort the er-progn and revert to the old world before the preceding PROGN
          )))
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

    (cond ((eq :timed-out (@ ss-temp-result))
           (mv T nil state))
          ((atom (@ ss-temp-result))
           (prog2$ 
            (cw? (verbose-flag vl)
                 "~|Cgen/Error : Bad trans-eval call in local Cgen/testing driver code. ~ 
 ss-temp-result: ~x0~|" (@ ss-temp-result))
            (mv T nil state)))
          (t (prog2$
              (and (verbose-stats-flag vl)
                   (ss-stats (@ ss-temp-result) test-outcomes%))
              (value (@ ss-temp-result)))))))))


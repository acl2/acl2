#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis.lsp")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "utilities")


;;; Keep the following defconst synced with all the acl2s parameters
(defconst *acl2s-parameters* '(num-trials
                               verbosity-level
                               num-counterexamples
                               num-witnesses
                               ;show-top-level-counterexample
                               sampling-method
                               backtrack-limit
                               search-strategy
                               testing-enabled
                               stopping-condition
                               subgoal-timeout
                               ))

;All user-defined parameters are stored here
(table acl2s-defaults-table)

(defrec acl2s-param-info% (value guard setter) NIL)

(defmacro add-acl2s-parameter (name default
                                    &key 
                                    (setter 'nil)
                                    (doc-string 'nil)
                                    (guard 't))
  "Add a new user-defined parameter.
   Put it in the acl2s-defaults-table as a key,
   using the value of :default. 
:guard is a term that checks for legal values of the
   parameter (It uses symbol 'value for variable capture).
getter and setter specify macro names that will be used by
the actual getter/setter mechanism to delegate its function.
Note that setter should be a macro that expands to a state changing
embedded event form, this this is called from inside an make-event.
You have to see the code in acl2s-defaults to understand whats going
on with getter and setter, the situation is assymmetric and I am
being lazy about documentation.
:doc-string is a string that is used to specify the defdoc. 
For internal flags dont use a doc-string"
  
  (b* (((unless (symbolp name))
        (er hard 'add-acl2s-parameter
            "Name must be a symbol, but is ~x0." name))
       ((unless (allp guard))
        (er hard 'add-acl2s-parameter 
            ":guard must be a term, but is ~x0." guard))
       );*b

    `(progn 
       (table acl2s-defaults-table 
              ',name
              ',(acl2::make acl2s-param-info%
                 :guard guard ;store guard too
                 :value default
                 :setter setter)
              :put)
       ,@(and doc-string
              `((defdoc ,name ,doc-string))))))


  


(defdoc ACL2::TESTING
  ":Doc-Section ACL2::TESTING
  
  A counterexample generation framework for ACL2 ~/
                                 
  Test formulas before and during a proof attempt, to find
  counterexamples and witnesses potentially saving time and
  effort and providing more intuition into the conjecture under
  scrutiny.  The testing framework is tightly coupled with the
  data definition (See ~ilc[DATA-DEFINITIONS]) framework.
  
  ~t[test?] guarantees printing counterexamples in
  terms of the top goals variables. See ~ilc[test?]
  for more details and examples.
  
  The framework can be configured via a bunch of parameters
  whose documention you will find below. In particular, see
  ~ilc[num-trials], ~ilc[verbosity-level], ~ilc[testing-enabled].~/ 
  
  To understand more about how testing works,
  please refer to the following paper
  ~url[http://www.ccs.neu.edu/home/harshrc/ITaITP.pdf]
  ")


(add-acl2s-parameter 
 num-trials 1000
 :doc-string 
 ":Doc-Section ACL2::TESTING
  
  Max number of tries to find counterexamples~/~/

  Maximum number of tries (attempts) to construct 
  counterexamples and witnesses.
  By default this parameter is set to 1000. Can be set to
  any natural number ~t[n]. If set to 0, it has the same
  effect as setting testing-enabled parameter to ~t[nil].
  ~bv[]
   Usage:
   (acl2s-defaults :set num-trials 1000)
   (acl2s-defaults :get num-trials)
   :doc num-trials
   ~ev[]"
 :guard (and (natp value) 
             (< value 1000000000)))

(add-acl2s-parameter 
 verbosity-level 1
 :doc-string 
 ":Doc-Section ACL2::TESTING
  
 Control verbosity of Testing~/~/

 Control amount of output printed by random-testing
   Currently 3 verbosity levels are implemented:
   0 - All testing output is turned off
   1 - Normal verbosity level (default)
   2 - More verbose.
   3 - For Debug by normal users
   4 and above - System level debug by developers
  ~bv[]
    Usage:
    (acl2s-defaults :set verbosity-level 1)
    (acl2s-defaults :get verbosity-level)
    :doc verbosity-level
  ~ev[]"
 :guard (natp value))


(add-acl2s-parameter 
  num-counterexamples 3
 :doc-string 
 ":Doc-Section ACL2::TESTING
 
  Number of Counterexamples to be shown~/~/
 
  Set the number of counterexamples desired to be shown
  By default this parameter is set to 3. Can be set to
  any natural number n. Setting this number to 0 implies
  the user is not interested in seeing counterexamples, and
  thus none will be printed in the testing output.
  
  ~bv[]
  Usage:
  (acl2s-defaults :set num-counterexamples 3)
  (acl2s-defaults :get num-counterexamples)
  :doc num-counterexamples
  ~ev[]"
   :guard (natp value))


(add-acl2s-parameter 
  num-witnesses 3
 :doc-string 
 ":Doc-Section ACL2::TESTING
  
  Number of Witnesses to be shown~/~/
  
  Set the number of witnesses desired to be shown
  By default this parameter is set to 3. Can be set to
  any natural number. Setting this number to 0 implies
  the user is not interested in seeing witnesses, and
  thus none will be printed in the testing output.
  
  ~bv[]
  Usage:
  (acl2s-defaults :set num-witnesses 3)
  (acl2s-defaults :get num-witnesses)
  :doc num-witnesses
  ~ev[]"
   :guard (natp value))

;DEPRECATED
;; (add-acl2s-parameter 
;;  show-top-level-counterexample t
;;  :doc-string ":Doc-Section ACL2::TESTING
;;  Show Counterexamples to the top-level <i>goal</i>" 
;;  Show Counterexamples to the top-level <i>goal</i>
;;    instead of to the <i>subgoals</i>.
;;    By default this parameter is set to <tt>t</tt>. 
;;    If set to <tt>nil</tt>, then counterexamples are simply
;;    instances falsifying the respective subgoals.
;;    ~bv[]
;;    Usage:
;;    (acl2s-defaults :set show-top-level-counterexample t)
;;    (acl2s-defaults :get show-top-level-counterexample)
;;    :doc show-top-level-counterexample 
;;    ~ev[]
;;    "
;;  :guard (booleanp value))

;; use test enumerator for user-level controlled testing
(defconst *default-rt-use-test-enum* t)

(defmacro set-acl2s-random-testing-use-test-enumerator (v)
;:Doc-Section RANDOM-TESTING  
 "Set the flag to use test-enumerator if it exists~/
  By default this parameter is set to nil.
  ~bv[]
  Usage:
  (set-acl2s-random-testing-use-test-enumerator nil)
  ~ev[]~/
  "
 `(assign acl2s-rt-use-test-enum ,v))

(defun get-acl2s-random-testing-use-test-enumerator-fn (state)
  (declare (xargs :stobjs (state)))
  (let ((nt (f-boundp-global 'acl2s-rt-use-test-enum state)))
    (if nt
     (f-get-global 'acl2s-rt-use-test-enum state)
      *default-rt-use-test-enum*)))


(defmacro get-acl2s-random-testing-use-test-enumerator ()
;:Doc-Section RANDOM-TESTING  
 "Get the current setting for use of test-enumerator~/
  ~bv[]
  Usage:
  (get-acl2s-random-testing-use-test-enumerator)
  ~ev[]~/
  "
 '(get-acl2s-random-testing-use-test-enumerator-fn state))


(add-acl2s-parameter 
 search-strategy :simple
 :doc-string 
 ":Doc-Section ACL2::TESTING
  
  Specify the search strategy to be used ~/~/
 
  Specify which of the following strategies to
  use for instantiating free variables of the conjecture
  under test: ~t[:simple] or  ~t[:incremental]
  or  ~t[:hybrid] (untested).
  ~t[:incremental] uses a dpll-like algorithm to search
  for counterexamples.
  By default this parameter is set to the symbol <tt>:simple</tt>.
   ~bv[]
    Usage:
    (acl2s-defaults :set search-strategy :simple)
    (acl2s-defaults :get search-strategy)
    :doc search-strategy
   ~ev[]
   "
 :guard (member-eq value '(:simple :incremental :hybrid)))
;; Use natural seeds or random tree of natural numbers 

(add-acl2s-parameter 
 sampling-method :random
 :doc-string 
 ":Doc-Section ACL2::TESTING
 
  Specify sampling method to be used to instantiate variables ~/~/
 
  Specify which of the following methods to
  use for instantiating free variables of the conjecture
  under test: ~t[:be] or ~t[:random] or ~t[:mixed]
  By default this parameter is set to the symbol ~t[:random]
   ~bv[]
    Usage:
    (acl2s-defaults :set sampling-method :random)
    (acl2s-defaults :get sampling-method)
    :doc sampling-method
   ~ev[]
   "
 :guard (member-eq value '(:be :random :mixed)))

;; (add-acl2s-parameter 
;;  flatten-defdata nil
;;  :doc-string ":Doc-Section ACL2::TESTING
;;  Flatten defdata instances during sampling"
;;  Flatten defdata enumerator expressions which stand for
;;    instances of the particular defdata type. Basically if you
;;    have a type triple <tt>(defdata triple (list pos pos pos))</tt>,
;;    then an instance of triple is generated (sampled) by a call to the 
;;    enumerator expression <tt>(nth-triple n)</tt>, where <tt>n</tt>
;;    is some natural number. Alternatively we could flatten the 
;;    defdata instance by representing it with the enumerator 
;;    expression <tt>(list (nth-pos n1) (nth-pos n2) (nth-pos n3))</tt>
;;    which consists purely of instances of primitive and custom types. 
;;    This has the nice property of distribution invariance, 
;;    i.e. a field of a particular type has the same distribution, 
;;    regardless of its position in the body of a complex defdata type.
;;    By default the value of parameter is <tt>nil</tt>.
;;    ~bv[]
;;     Usage:
;;     (acl2s-defaults :set flatten-defdata-instance nil)
;;     (acl2s-defaults :get flatten-defdata-instance)
;;     :doc flatten-defdata-instance
;;    ~ev[]
;;    "
;;  :guard (booleanp value))

(add-acl2s-parameter 
 backtrack-limit 3
 :doc-string 
 ":Doc-Section ACL2::TESTING
 
  Maximum number of backtracks allowed (per variable)~/~/
 
  Maximum number of backtracks allowed by a variable.
   The default backtrack limit is set to 3. Setting this 
   parameter to 0, means that backtracking is disabled.
   ~bv[]
    Usage:
    (acl2s-defaults :set backtrack-limit 3)
    (acl2s-defaults :get backtrack-limit)
    :doc backtrack-limit
   ~ev[]
   "
 :guard (natp value))
        

(add-acl2s-parameter 
 subgoal-timeout 10
 :doc-string 
 ":Doc-Section ACL2::TESTING
 
  Testing timeout (in seconds) per subgoal~/~/
 
  Maximum allowed time (in seconds) to test any 
  subgoal or top-level form.
  The default timeout limit is set to 10 sec.
  Setting this parameter to 0 amounts to disabling
  the timeout mechanism, i.e. its a no-op.
   ~bv[]
    Usage:
    (acl2s-defaults :set subgoal-timeout 10)
    (acl2s-defaults :get subgoal-timeout)
    :doc subgoal-timeout
   ~ev[]
   "
 :guard (natp value))

(add-acl2s-parameter 
 testing-enabled :naive
 :doc-string 
 ":Doc-Section ACL2::TESTING
 
  Testing enable/disable flag~/~/
 
  Testing can be enabled or disabled
  using this parameter.
  The default value is  ~t[:naive] (unless you are in
  the usual ACL2 Sedan session modes, where default is ~t[t]).
  Setting this parameter to ~t[nil] amounts to disabling
  the testing mechanism. Setting this parameter
  to ~t[:naive] leads to top-level testing without any
  theorem prover support.
  ~bv[]
   Usage:
   (acl2s-defaults :set testing-enabled :naive)
   (acl2s-defaults :get testing-enabled)
   :doc testing-enabled
  ~ev[]
   "
 :guard (member-eq value '(T NIL :naive))
 :setter set-acl2s-random-testing-enabled)

(defun mem-tree (x tree)
  (declare (xargs :guard (symbolp x)))
  (if (atom tree)
    (eq x tree)
    (or (mem-tree x (car tree))
        (mem-tree x (cdr tree)))))

(defun get-acl2s-random-testing-hints-flag-fn ( state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  ;; bugfix 30 April '12: I had changed the name of test-each-checkpoint
  ;; to test-checkpoint and forgot the update the fact here. Bad bad bad!
  (and (mem-tree 'TEST-CHECKPOINT ;check if random testing is enabled
                 (override-hints (w state)))
       T))
      

(defdoc get-acl2s-random-testing-hints-enabled
  ":Doc-Section ACL2::TESTING
  
   Get current setting for random-testing-hints-enabled~/~/
  
   Get current setting for random-testing-hints-enabled.
   Returns ~t[nil] if ~t[thm] and ~t[defthm] do not make use of random-testing
   in their proof attempts, and ~t[t] otherwise.
   
   ~bv[]
    Usage:
    (get-acl2s-random-testing-hints-enabled)
   ~ev[]
   ")

;top-level exported macro to know wether random testing is enabled or not
(defmacro get-acl2s-random-testing-hints-enabled ()
 
 `(get-acl2s-random-testing-hints-flag-fn state))

(defun set-acl2s-random-testing-flag-fn (flg mode state)
  (declare (xargs :mode :program
                  :stobjs (state)))
;check if random testing is enabled by searching for the testing hint
  (let ((flg (if (eq flg :naive) NIL flg)))
  (if (get-acl2s-random-testing-hints-enabled)
      ;;; TESTING hint is currently ENABLED
    (if flg ;if enabled and user wants to set it then no-op
      '(value-triple :REDUNDANT)
;if enabled and user wants to turn it off
      (if (eq mode :program)
          '(progn ; Feb 13 2012 bug. Testing-hint cant be disabled
             ;; in program mode. Found by Pete while using defunc.
             ;; Reason: local forms are ignored in program mode.
             (logic)
             (disable-acl2s-random-testing)
             (program))
        '(disable-acl2s-random-testing)))
    ;;; TESTING hint is currently disabled
    (if flg ;if disabled and user wants to set it to t
        (if (eq mode :program)
            '(progn
               (logic)
               (enable-acl2s-random-testing)
               (program))
          '(enable-acl2s-random-testing))
;if testing-hint is disabled and user wants to turn it off its no-op
      '(value-triple :REDUNDANT)))))

(defdoc set-acl2s-random-testing-enabled
   ":Doc-Section ACL2::TESTING
  
   Control enabling/disabling testing hint~/~/
  
   Control enabling/disabling random-testing computed override-hint.
   If set to ~t[nil], thm and defthm retain their default ACL2 behavior.
   If set to ~t[t], then all theorem-proving (defthm, thm, function
   termination, guard-verification) will use random-testing pervasively.
   
   ~bv[]
    Usage:
    (set-acl2s-random-testing-enabled nil)
   ~ev[]" )

;top-level exported macro to know enable random testing
(defmacro set-acl2s-random-testing-enabled (v forms)
  (declare (xargs :guard (member-eq v '(T NIL :naive))))
  `(make-event
     (let ((mode (cdr (assoc-eq :defun-mode 
                                (table-alist
                                 'acl2::acl2-defaults-table 
                                 (w state))))))
       (let ((forms ',forms))
         (value `(progn
                   ,(set-acl2s-random-testing-flag-fn ,v mode state)
                   ,@forms))))))

(defmacro acl2s-defaults (&rest rst)
  (b* (((unless (consp (cdr rst)));atleast 2 elems
        (er hard 'acl2s-defaults
            "~|At least 2 arguments, but given ~x0~%" rst))
       (param (second rst))
       (op (car rst))
       ((unless (or (eq :get op) 
                    (and (eq :set op)
                         (consp (cddr rst));value
                         )))
        (er hard 'acl2s-defaults;TODO be more informative
            "~|Invalid arguments supplied, given ~x0~%" rst)))
    (if (eq :get op)
;get the value at the point of call (runtime)
        `(b* ((param-rec-pair
                 (assoc-eq ',param 
                           (table-alist 'acl2s-defaults-table 
                                        (w state))))
              ((unless (consp param-rec-pair))
                 (er hard 'acl2s-defaults 
                     "~|Parameter ~x0 not found in acl2s-defaults!~%"
                     ',param))
              (r (cdr param-rec-pair))
              (val (access acl2s-param-info% r :value)))
          val)

;get the guard and value at the runtime
;since we need access to state
;and set the new value v
     `(with-output
       :off summary
       (make-event
        (b* ((param-rec-pair
             (assoc-eq ',param 
                      (table-alist 
                       'acl2s-defaults-table (w state))))
             ((unless (consp param-rec-pair))
                 (er hard 'acl2s-defaults 
                     "~|Parameter ~x0 not found in acl2s-defaults!~%"
                     ',param))
;guard is fixed once it is initialized INVARIANT
             (r (cdr param-rec-pair))
             (guard (access acl2s-param-info% r :guard))
             (setter (access acl2s-param-info% r :setter))
             (v (third ',rst)))
        `(make-event ;state changing event 
           (if (not ,(subst v 'value guard))
               (er soft 'acl2s-defaults-table
                 "Guard ~x0 for ~x1 in table failed for VALUE ~x2" 
                 ',guard ',',param ',v)
             (if ',setter
                 (let ((table-update-form
                        `(table acl2s-defaults-table 
                                  ',',',param 
                                  ',(change acl2s-param-info% ',r :value ',v))))
;;; setter is a macro, so dont quote the args to it whereas the above
;;; table macro needs quoted args because its 3rd parameter is &rest rst
                  (value `(,',setter ,',v (,table-update-form));embedded event
                        ))
                           
             (value `(progn
                      (table acl2s-defaults-table 
                             ',',',param 
                             ',(change acl2s-param-info% ',r :value ',v))
                      (value-triple ',',v))))))))))))



;;; copied from main.lisp, since these functions are only called by
;;; set-acl2s-random-testing-enabled, which is defined here


;;; add no-op override hints that test each checkpoint.  The reason
;;; why we need backtrack hint is not that we need clause-list
;;; (children goals of clause), but because we need to do testing only
;;; on checkpoints, and only backtrack hints have access to processor,
;;; if this were not the case, we could have used ":no-op
;;; '(test-each-goal ...)" as an override hint which has no effect but
;;; to test each goal.  Another reason is that because computed-hints
;;; with :COMPUTED-HINT-REPLACEMENT t is not additive like
;;; override-hints it can cause a hint to be not selected otherwise.
(defmacro enable-acl2s-random-testing ()
;; this has to be a makevent because enable-acl2s-random-testing is the
;; expansion result of the make-event in set-acl2s-random-testing-enabled
`(make-event  
  '(acl2::add-override-hints 
    '((list* :backtrack 
;take parent pspv and hist, not the ones returned by clause-processor

             `(test-checkpoint acl2::id 
                                    acl2::clause
                                    acl2::clause-list
                                    acl2::processor
;TODO:ask Matt about sending parent pspv and hist
                                    ',acl2::pspv 
                                    ',acl2::hist
                                    state
                                    )

             ;; `(mv-let (erp tval state)
             ;;          (trans-eval
             ;;           `(test-each-checkpoint ',acl2::id 
             ;;                                  ',acl2::clause 
             ;;                                  ',acl2::processor 
             ;;                                  ',',acl2::pspv 
             ;;                                  ',',acl2::hist state
             ;;                                  ts$)
             ;;           'acl2s-testing ; ctx
             ;;           state
             ;;           t ; aok
             ;;           )
             ;;          (declare (ignorable erp))
             ;;          (mv (cadr tval) (caddr tval) state))

;`(test-each-checkpoint acl2::id acl2::clause acl2::processor ',acl2::pspv ',acl2::hist state)
             acl2::keyword-alist)))))

(defmacro disable-acl2s-random-testing ()
`(make-event  
     '(acl2::remove-override-hints 
       '((list* :backtrack 
                `(test-checkpoint acl2::id 
                                       acl2::clause 
                                       acl2::clause-list
                                       acl2::processor 
                                       ',acl2::pspv 
                                       ',acl2::hist
                                       state
                                      )
;take parent pspv and hist, not the ones returned by clause-processor
                 ;; `(mv-let (erp tval state)
                 ;;      (trans-eval
                 ;;       `(test-each-checkpoint ',acl2::id 
                 ;;                              ',acl2::clause 
                 ;;                              ',acl2::processor 
                 ;;                              ',',acl2::pspv 
                 ;;                              ',',acl2::hist state
                 ;;                              ts$)
                 ;;       'acl2s-testing ; ctx
                 ;;       state
                 ;;       t ; aok
                 ;;       )
                 ;;      (declare (ignorable erp))
                 ;;      (mv (cadr tval) (caddr tval) state))
;`(test-each-checkpoint acl2::id acl2::clause acl2::processor ',acl2::pspv ',acl2::hist state)
                acl2::keyword-alist)))))



; Internal flags
(add-acl2s-parameter 
;show pts at the end of subgoal?
  acl2s-pts-subgoalp NIL
 :guard (booleanp value))


#|ACL2s-ToDo-Line|#



(in-package "ACL2")
(include-book "utilities")
(include-book "xdoc/top" :dir :system)

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



(defmacro add-acl2s-parameter (name default
                                    &key 
                                    (setter 'nil)
                                    (parents  'nil)
                                    (short 'nil)
                                    (long 'nil)
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
:parents, :short and :long is used to specify the xdoc data. "
  
  (b* (((unless (symbolp name))
        (er hard 'add-acl2s-parameter
            "Name must be a symbol, but is ~x0." name))
#|
       ((unless (and (acl2::good-map xdoc)
                     (symbol-listp (mget :parents xdoc))
                     (stringp (mget :short xdoc))
                     (stringp (mget :long xdoc))))
        (er hard 'add-acl2s-parameter 
            ":xdoc must be a xdoc datatype, but is ~x0." xdoc))
            |#
       ((unless (allp guard))
        (er hard 'add-acl2s-parameter 
            ":guard must be a term, but is ~x0." guard))
       );*b

    `(progn 
       (table acl2s-defaults-table 
              ',name
              ',(c nil :guard guard ;store guard too
                  :value default
                  :setter setter)
              :put)
       (defxdoc ,name
         :parents ,parents
         :short ,short
         :long ,long))))


  
(add-acl2s-parameter 
 num-trials 1000
 :parents (ACL2::TESTING)
 :short "Max number of tries to find counterexamples"
 :long 
    "Maximum number of tries (attempts) to construct 
  counterexamples and witnesses.
  By default this parameter is set to 1000. Can be set to
  any natural number <tt>n</tt>. If set to 0, it has the same
  effect as setting testing-enabled parameter to <tt>nil</tt>.
  <code>
   Usage:
   (acl2s-defaults :set num-trials 1000)
   (acl2s-defaults :get num-trials)
   :xdoc num-trials
  </code>"
 :guard (and (natp value) 
             (< value 1000000000)))

(add-acl2s-parameter 
 verbosity-level 1
 :parents (ACL2::TESTING)
 :short "Control verbosity of Testing"
 :long "Control amount of output printed by random-testing
   Currently 3 verbosity levels are implemented:
   0 - All testing output is turned off
   1 - Normal verbosity levels (default)
   2 - More verbose.
   3 - For Debug by normal users
   4 and above - System level debug by developers
  <code>
    Usage:
    (acl2s-defaults :set verbosity-level 1)
    (acl2s-defaults :get verbosity-level)
    :xdoc verbosity-level
   </code>"
 :guard (natp value))


(add-acl2s-parameter 
  num-counterexamples 3
 :parents (ACL2::TESTING)
 :short "Number of Counterexamples to be shown"
 :long "Set the number of counterexamples desired to be shown~/
  By default this parameter is set to 3. Can be set to
  any natural number <tt>n</tt>. Setting this number to 0 implies
  the user is not interested in seeing counterexamples, and
  thus none will be printed in the testing output.
  
  <code>
  Usage:
  (acl2s-defaults :set num-counterexamples 3)
  (acl2s-defaults :get num-counterexamples)
  :xdoc num-counterexamples
  </code>"
   :guard (natp value))


(add-acl2s-parameter 
  num-witnesses 3
 :parents (ACL2::TESTING)
 :short "Number of Witnesses to be shown"
 :long "Set the number of witnesses desired to be shown~/
  By default this parameter is set to 3. Can be set to
  any natural number <tt>n</tt>. Setting this number to 0 implies
  the user is not interested in seeing witnesses, and
  thus none will be printed in the testing output.
  
  <code>
  Usage:
  (acl2s-defaults :set num-witnesses 3)
  (acl2s-defaults :get num-witnesses)
  :xdoc num-witnesses
  </code>"
   :guard (natp value))

;DEPRECATED
;; (add-acl2s-parameter 
;;  show-top-level-counterexample t
;;  :parents (ACL2::TESTING)
;;  :short "Show Counterexamples to the top-level <i>goal</i>" 
;;  :long "Show Counterexamples to the top-level <i>goal</i>
;;    instead of to the <i>subgoals</i>.
;;    By default this parameter is set to <tt>t</tt>. 
;;    If set to <tt>nil</tt>, then counterexamples are simply
;;    instances falsifying the respective subgoals.
;;    <code>
;;    Usage:
;;    (acl2s-defaults :set show-top-level-counterexample t)
;;    (acl2s-defaults :get show-top-level-counterexample)
;;    :xdoc show-top-level-counterexample 
;;    </code>
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
 :parents (ACL2::TESTING)
 :short "Specify the search strategy to be used" 
 :long "Specify which of the following strategies to
  use for instantiating free variables of the conjecture
  under test: <tt>:simple</tt> or <tt>:incremental</tt>
  or <tt:hybrid</tt>.
  <tt>:incremental</tt> uses a dpll-like algorithm to search
for counterexamples.
  By default this parameter is set to the symbol <tt>:simple</tt>.
   <code>
    Usage:
    (acl2s-defaults :set search-strategy :simple)
    (acl2s-defaults :get search-strategy)
    :xdoc search-strategy
   </code>
   "
 :guard (member-eq value '(:simple :incremental :hybrid)))
;; Use natural seeds or random tree of natural numbers 

(add-acl2s-parameter 
 sampling-method :random
 :parents (ACL2::TESTING)
 :short "Specify the sampling method to be used to instantiate variables" 
 :long "Specify which of the following methods to
  use for instantiating free variables of the conjecture
  under test: <tt>:be</tt> or <tt>:random</tt> or <tt>:mixed</tt>.
  By default this parameter is set to the symbol <tt>:random</tt>.
   <code>
    Usage:
    (acl2s-defaults :set sampling-method :random)
    (acl2s-defaults :get sampling-method)
    :xdoc sampling-method
   </code>
   "
 :guard (member-eq value '(:be :random :mixed)))

;; (add-acl2s-parameter 
;;  flatten-defdata nil
;;  :parents (ACL2::TESTING)
;;  :short "Flatten defdata instances during sampling"
;;  :long "Flatten defdata enumerator expressions which stand for
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
;;    <code>
;;     Usage:
;;     (acl2s-defaults :set flatten-defdata-instance nil)
;;     (acl2s-defaults :get flatten-defdata-instance)
;;     :doc flatten-defdata-instance
;;    </code>
;;    "
;;  :guard (booleanp value))

(add-acl2s-parameter 
 backtrack-limit 3
 :parents (ACL2::TESTING)
 :short "Maximum number of backtracks allowed (per variable)"
 :long "Maximum number of backtracks allowed by a variable.
   The default backtrack limit is set to 3. Setting this 
   parameter to 0, means that backtracking is disabled.
   <code>
    Usage:
    (acl2s-defaults :set backtrack-limit 3)
    (acl2s-defaults :get backtrack-limit)
    :xdoc backtrack-limit
   </code>
   "
 :guard (natp value))
        

(add-acl2s-parameter 
 subgoal-timeout 10
 :parents (ACL2::TESTING)
 :short "Testing timeout (in seconds) per subgoal"
 :long "Maximum allowed time (in seconds) to test any 
   subgoal or top-level form.
   The default timeout limit is set to 10 sec.
   Setting this parameter to 0 amounts to disabling
   the timeout mechanism, i.e. its a no-op.
   <code>
    Usage:
    (acl2s-defaults :set subgoal-timeout 10)
    (acl2s-defaults :get subgoal-timeout)
    :xdoc subgoal-timeout
   </code>
   "
 :guard (natp value))

(add-acl2s-parameter 
 testing-enabled :naive
 :parents (ACL2::TESTING)
 :short "Testing enable/disable flag"
 :long "Testing can be enabled or disabled
   using this parameter.
   The default value is <tt>:naive</tt>.
   Setting this parameter to <tt>nil</tt> amounts to disabling
   the testing mechanism. Setting this parameter
   to <tt>:naive</tt> leads to top-level testing without any
   theorem prover support.
   <code>
    Usage:
    (acl2s-defaults :set testing-enabled :naive)
    (acl2s-defaults :get testing-enabled)
    :xdoc testing-enabled
   </code>
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
      

(defxdoc get-acl2s-random-testing-hints-enabled
  :parents (ACL2::TESTING)
  :short "Get current setting for random-testing-hints-enabled"
  :long "Get current setting for random-testing-hints-enabled.
   Returns <tt>nil</tt> if random testing is disabled 
   i.e  thm and defthm do not make use of random-testing
   in their proof attempts, and <tt>t</tt> otherwise.
   
   <code>
    Usage:
    (get-acl2s-random-testing-hints-enabled)
   </code>
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

(defxdoc set-acl2s-random-testing-enabled
  :parents (ACL2::TESTING)
  :short "Control enabling/disabling random-testing"
  :long "Control enabling/disabling random-testing.
   By default this parameter is set to ~c[t], except in the
   Compatible Mode.
   If set to <tt>nil</tt>, thm and defthm retain their default ACL2 behavior.
   If set to <tt>t</tt>, then all theorem-proving (defthm, thm, function
   termination, guard-verification) will use random-testing pervasively.
   
   <code>
    Usage:
    (set-acl2s-random-testing-enabled nil)
   </code>" )
;top-level exported macro to know enable random testing
(defmacro set-acl2s-random-testing-enabled (v forms)
  (declare (xargs :guard (member-eq v '(T NIL :naive))))
  `(with-output
    :on :all
    (make-event
     (let ((mode (cdr (assoc-eq :defun-mode 
                                (table-alist
                                 'acl2::acl2-defaults-table 
                                 (w state))))))
       (let ((forms ',forms))
         (value `(progn
                   ,(set-acl2s-random-testing-flag-fn ,v mode state)
                   ,@forms)))))))

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
              (val (mget :value r)))
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
             (guard (mget :guard r)) 
             (setter (mget :setter r))
             (v (third ',rst)))
        `(make-event ;state changing event 
           (if (not ,(subst v 'value guard))
               (er soft 'acl2s-defaults-table
                 "Guard ~x0 for ~x1 in table failed for VALUE ~x2" 
                 ',guard ',',param ',v)
             (if ',setter
                 (let ((table-update-form
                        `(table acl2s-defaults-table 
                                  ',',',param ',(c ',r :value ',v))))
;;; setter is a macro, so dont quote the args to it whereas the above
;;; table macro needs quoted args because its 3rd parameter is &rest rst
                  (value `(,',setter ,',v (,table-update-form));embedded event
                        ))
                           
             (value `(progn
                      (table acl2s-defaults-table 
                             ',',',param ',(c ',r :value ',v))
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




#|ACL2s-ToDo-Line|#


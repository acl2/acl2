#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/utilities" :dir :system)
(include-book "std/util/bstar" :dir :system)

; [2014-11-25 Tue] Make key package agnostic by always putting it into
; keyword package. Thus we look only at symbol-name of the original
; parameter name.

(defun keywordify (sym)
  (declare (xargs :guard (symbolp sym)))
  (fix-intern-in-pkg-of-sym (symbol-name sym) :a))


;;; Keep the following defconst synced with all the acl2s parameters
(def-const *acl2s-parameters*
  '(:testing-enabled
    :num-trials
    :verbosity-level
    :num-counterexamples
    :num-print-counterexamples
    :num-witnesses
    :num-print-witnesses
    ;;show-top-level-counterexample
    :search-strategy
    :sampling-method
    :backtrack-limit
    :cgen-timeout
    :cgen-local-timeout
    :cgen-single-test-timeout
    :print-cgen-summary
    :backtrack-bad-generalizations
    :use-fixers
    :recursively-fix
    :defdata-aliasing-enabled
    ))

;All user-defined parameters are stored here
(table acl2s-defaults-table)


;TODO: This is too complicated -- cant you make this simpler? [2014-11-26 Wed]
(acl2::defrec acl2s-param-info% (value guard setter) NIL)

(defmacro add-acl2s-parameter (name default
                                    &key 
                                    (setter 'nil)
                                    (guard 't)
                                    short
                                    long)
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
short and long are keyword arguments to defxdoc. 
"
  
  (b* (((unless (symbolp name))
        (er hard 'add-acl2s-parameter
            "Name must be a symbol, but is ~x0." name))
       ;; ((unless (pseudo-termp guard))
       ;;  (er hard 'add-acl2s-parameter 
       ;;      ":guard must be a term, but is ~x0." guard))
       );*b

    `(progn 
       (table acl2s-defaults-table 
              ',(keywordify name)
              ',(acl2::make acl2s-param-info%
                 :guard guard ;store guard too
                 :value default
                 :setter setter)
              :put)
       ,@(and short
              `((defxdoc ,name :parents (acl2::cgen acl2::acl2s-defaults) :short ,short :long ,long))))))


(defxdoc acl2s-defaults
  :parents (acl2::acl2-sedan acl2::cgen)
  :short "Getting and setting defaults for various parameters in Cgen (ACL2 Sedan)"                                 
  :long  
  "
<h3>Examples</h3>
@({
  (acl2s-defaults :set num-trials 1000)
  (acl2s-defaults :get cgen-local-timeout)
  (acl2s-defaults :get testing-enabled)
  (acl2s-defaults :set num-counterexamples 3)
})

<p>
The following parameters are available for control via @('acl2s-defaults').
These are stored in the constant @('*acl2s-parameters*') and are package-agnostic.

@({
                  num-trials
                  verbosity-level
                  num-counterexamples
                  num-witnesses
                  sampling-method
                  backtrack-limit
                  search-strategy
                  testing-enabled
                  cgen-timeout
                  cgen-local-timeout
                  cgen-single-test-timeout
                  print-cgen-summary
                  use-fixers
                  num-print-counterexamples
                  num-print-witnesses

})
</p>
")

(def-const *testing-enabled-values* '(T NIL :naive))

(add-acl2s-parameter 
 testing-enabled :naive
 :short "Testing enable/disable flag"
 :long
" <p>Testing can be enabled or disabled using this parameter.
  The default value is  <tt>:naive</tt> (unless you are in
  the usual ACL2 Sedan session modes, where default is @('t')).
  Setting this parameter to @('nil') amounts to disabling
  the testing mechanism. Setting this parameter
  to <tt>:naive</tt> leads to top-level testing without any
  theorem prover support.</p>
  <code>
   Usage:
   (acl2s-defaults :set testing-enabled :naive)
   (acl2s-defaults :get testing-enabled)
   :doc testing-enabled
  </code>
   "
 :guard (member-eq value *testing-enabled-values*)
 :setter set-acl2s-random-testing-enabled)

(add-acl2s-parameter 
 num-trials 1000
 :short "Max number of tries to find counterexamples"
 :long
" Maximum number of tries (attempts) to construct 
  counterexamples and witnesses.
  By default this parameter is set to 4000. Can be set to
  any natural number <tt>n</tt>. If set to 0, it is similar
  to setting testing-enabled parameter to @('nil').

  <code>
   Usage:
   (acl2s-defaults :set num-trials 4000)
   (acl2s-defaults :get num-trials)
   :doc num-trials
   </code>"
 :guard (and (natp value) 
             (< value 1000000000)))

(add-acl2s-parameter 
 verbosity-level 1
 :short "Control verbosity of Cgen"
 :long "
 <p>Control amount of output printed by Cgen.</p>

<dl>
<dt>Levels</dt>
<dd>   0 - All Cgen output is turned off      </dd> 
<dd>   1 - Normal output (default)            </dd> 
<dd>   2 - Verbose output                     </dd> 
<dd>   3 - More verbose with Cgen statistics  </dd>  
<dd>   4 - For Debug by normal users          </dd>  
<dd>   5 and above - System level debug by developers </dd>
</dl>

  <code>
    Usage:
    (acl2s-defaults :set verbosity-level 1)
    (acl2s-defaults :get verbosity-level)
    :doc verbosity-level
  </code>"
 :guard (natp value))


(add-acl2s-parameter
  num-counterexamples 3
 :short "Number of Counterexamples to be searched"
 :long "
  Set the number of counterexamples desired to be searched.
  By default this parameter is set to 3. Can be set to
  any natural number n. Setting this number to 0 implies
  the user is not interested in searching for counterexamples.
  <code>
  Usage:
  (acl2s-defaults :set num-counterexamples 3)
  (acl2s-defaults :get num-counterexamples)
  :doc num-counterexamples
  </code>"
   :guard (natp value))

(add-acl2s-parameter
  num-print-counterexamples 3
 :short "Number of Counterexamples to be printed"
 :long "
  Set the number of counterexamples desired to be printed.
  By default this parameter is set to 3. Can be set to
  any natural number n. Setting this number to 0 implies
  the user is not interested in seeing counterexamples, and
  thus none will be printed in the testing output.
  
  <code>
  Usage:
  (acl2s-defaults :set num-print-counterexamples 3)
  (acl2s-defaults :get num-print-counterexamples)
  :doc num-counterexamples
  </code>"
   :guard (natp value))

(add-acl2s-parameter 
  num-witnesses 3
 :short "Number of Witnesses to be shown"
 :long "
  Set the number of witnesses desired to be shown
  By default this parameter is set to 3. Can be set to
  any natural number. Setting this number to 0 implies
  the user is not interested in seeing witnesses, and
  thus none will be printed in the testing output.
  
  <code>
  Usage:
  (acl2s-defaults :set num-witnesses 3)
  (acl2s-defaults :get num-witnesses)
  :doc num-witnesses
  </code>"
   :guard (natp value))

(add-acl2s-parameter 
  num-print-witnesses 3
 :short "Number of Witnesses to be printed"
 :long "
  Set the number of witnesses desired to be printed.
  By default this parameter is set to 3. Can be set to
  any natural number. Setting this number to 0 implies
  the user is not interested in seeing witnesses, and
  thus none will be printed in the testing output.
  
  <code>
  Usage:
  (acl2s-defaults :set num-print-witnesses 3)
  (acl2s-defaults :get num-print-witnesses)
  :doc num-print-witnesses
  </code>"
   :guard (natp value))

(def-const *search-strategy-values* '(:simple :incremental :hybrid))
(add-acl2s-parameter 
 search-strategy :simple
 :short "Specify the search strategy to be used."
 :long "
  Specify which of the following strategies to
  use for instantiating free variables of the conjecture
  under test: @(':simple') or  @(':incremental').
  @(':incremental') uses a dpll-like algorithm to search
  for counterexamples (and is currently much slower).
  By default this parameter is set to @(':simple').
   <code>
    Usage:
    (acl2s-defaults :set search-strategy :simple)
    (acl2s-defaults :get search-strategy)
    :doc search-strategy
   </code>
   "
 :guard (member-eq value *search-strategy-values*))

;; Use natural seeds or random tree of natural numbers 

(def-const *sampling-method-values* '(:random :uniform-random :be :mixed))

(add-acl2s-parameter 
 sampling-method :random
 :short "Specify sampling method to be used to instantiate variables "
 :long "
  Specify which of the following methods to
  use for instantiating free variables of the conjecture
  under test: @(':be') or @(':random') or @(':uniform-random') or @(':mixed')
  By default this parameter is set to the symbol @(':random')
   <code>
    Usage:
    (acl2s-defaults :set sampling-method :random)
    (acl2s-defaults :get sampling-method)
    :doc sampling-method
   </code>
   "
 :guard (member-eq value *sampling-method-values*))

(add-acl2s-parameter 
 backtrack-limit 3
 :short "Maximum number of backtracks allowed (per variable)"
 :long "
   Maximum number of backtracks allowed by a variable.
   The default backtrack limit is set to 3. Setting this 
   parameter to 0 disables the backtracking.
   <code>
    Usage:
    (acl2s-defaults :set backtrack-limit 3)
    (acl2s-defaults :get backtrack-limit)
    :doc backtrack-limit
   </code>
   "
 :guard (natp value))

(add-acl2s-parameter 
 cgen-timeout 60 ;bad name -- TODO: change it in a latter version.
 :short "test?/prover timeout (in seconds)"
 :long
  "Maximum allowed time (in seconds) to be spent
  in the ACL2 prover on behalf of Cgen/test? macro.
  This value is used as the first argument of the
  with-timeout macro around the call to 
  prove/cgen.

  The default timeout limit is set to 60 sec.
  Guard : Timeout should be a non-negative rational.
   <code>
    Usage:
    (acl2s-defaults :set cgen-timeout 60)
    (acl2s-defaults :get cgen-timeout)
    :doc cgen-timeout
   </code>
   "
 :guard (and (rationalp value) (<= 0 value)))
        
(add-acl2s-parameter 
 cgen-local-timeout 10
 :short "Cgen/Testing timeout (in seconds)"
 :long
  "Maximum allowed time (in seconds) for Cgen to
  search for counterexamples to a particular form/subgoal.
  The default timeout limit is set to 10 sec.
  Setting this parameter to 0 amounts to disabling
  the timeout mechanism, i.e. its a no-op.
  Guard : Timeout should be a non-negative rational.
   <code>
    Usage:
    (acl2s-defaults :set cgen-local-timeout 10)
    (acl2s-defaults :get cgen-local-timeout)
    :doc cgen-local-timeout
   </code>
   "
 :guard (and (rationalp value) (<= 0 value)))

        
(add-acl2s-parameter 
 cgen-single-test-timeout 1/100
 :short "Cgen/Testing timeout for single, individual tests (in seconds)"
 :long
  "Maximum allowed time (in seconds) for Cgen to check a single test. 
  The default timeout limit is set to 1/100 sec. This is useful if
  you have functions that are very slow on some inputs. A simple
  example is the naive definition of the fibonnaci function.
  Setting this parameter to 0 amounts to disabling the timeout. 
  Guard : Timeout should be a non-negative rational.
   <code>
    Usage:
    (acl2s-defaults :set cgen-single-test-timeout 10)
    (acl2s-defaults :get cgen-single-test-timeout)
    :doc cgen-single-test-timeout
   </code>
   "
 :guard (and (rationalp value) (<= 0 value)))

(add-acl2s-parameter 
 print-cgen-summary T
 :short "Print summary for Cgen"
 :long " <p>Print summary of cgen/testing done in course of test? form (and
  other forms). The default is set to @('T'). Setting this parameter to
  @('NIL'), means that no summary is printed.</p>

   <code>
    Usage:
    (acl2s-defaults :set print-cgen-summary t)
    (acl2s-defaults :get print-cgen-summary)
    :doc print-cgen-summary
   </code>
   "
 :guard (booleanp value))

(add-acl2s-parameter 
 backtrack-bad-generalizations t
 :short "Specify whether to check for and then backtrack from bad generalizations."
 :long "
  By default this parameter is set to <tt>t</tt>.
   <code>
    Usage:
    (acl2s-defaults :set backtrack-bad-generalizations t)
    (acl2s-defaults :get backtrack-bad-generalizations)
    :doc backtrack-bad-generalizations
   </code>
   "
 :guard (booleanp value))

(add-acl2s-parameter 
 use-fixers nil
 :short "Specify whether fixers are to be used."
 :long "
  By default this parameter is set to <tt>nil</tt>.
   <code>
    Usage:
    (acl2s-defaults :set use-fixers t)
    (acl2s-defaults :get use-fixers)
    :doc use-fixers
   </code>
   "
 :guard (booleanp value))

(add-acl2s-parameter 
 recursively-fix t
 :short "Specify whether unsatisfied but fixable constraints are to be recursively fixed."
 :long "Specify whether unsatisfied but fixable constraints are to be
  recursively fixed. The resulting solution substitutions are stacked in the
  reverse order. 
  By default this parameter is set to <tt>t</tt>.
   "
 :guard (booleanp value))

(add-acl2s-parameter 
 defdata-aliasing-enabled t
 :short "Enable Defdata aliasing"
 :long
" <p>Defdata will try and determine if proposed data definitions are
  equivalent to existing data definitions and if so, Defdata will
  create alias types. The advantage is that any existing theorems can
  be used to reason about the new type. Defdata will generate macros
  for the recognizers and enumerators, which means that during proofs,
  you will see the recognizer for the base type. If you turn this off,
  then you can still use defdata-alias to explicitly tell ACL2s to
  alias types.</p>
 <code> Usage:
   (acl2s-defaults :get defdata-aliasing-enabled)
   (acl2s-defaults :set defdata-aliasing-enabled t)
   :doc defdata-aliasing-enabled
  </code>
   "
 :guard (booleanp value))

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
  (and (mem-tree 'ACL2::TEST-CHECKPOINT ;check if random testing is enabled
                 (override-hints (w state)))
       T))
      

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

(defun get-acl2s-defaults (param wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp param) (plist-worldp wrld))))
  (b* ((kparam (keywordify param))
       (param-rec-pair (assoc-eq kparam (table-alist 'ACL2S-DEFAULTS-TABLE wrld)))
       ((unless (consp param-rec-pair))
        (er hard 'acl2s-defaults 
            "~|Parameter ~x0 not found in acl2s defaults!~%" param))
       (r (cdr param-rec-pair))
       (val (acl2::access acl2s-param-info% r :value)))
    val))

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
        `(get-acl2s-defaults ',param (w state))

;get the guard and value at the runtime
;since we need access to state
;and set the new value v
     `(with-output
       :off summary
       (make-event
        (b* ((param-rec-pair
             (assoc-eq ',(keywordify param)
                      (table-alist 'ACL2S-DEFAULTS-TABLE (w state))))
             ((unless (consp param-rec-pair))
                 (er hard 'acl2s-defaults 
                     "~|Parameter ~x0 not found in acl2s-defaults!~%"
                     ',param))
;guard is fixed once it is initialized INVARIANT
             (r (cdr param-rec-pair))
             (guard (acl2::access acl2s-param-info% r :guard))
             (setter (acl2::access acl2s-param-info% r :setter))
             (v (third ',rst)))
        `(make-event ;state changing event 
           (if (not ,(subst v 'value guard))
               (er soft 'acl2s-defaults-table
                 "Guard ~x0 for ~x1 in table failed for VALUE ~x2" 
                 ',guard ',',param ',v)
             (if ',setter
                 (let ((table-update-form
                        `(table acl2s-defaults-table 
                                  ',',',(keywordify param)
                                  ',(acl2::change acl2s-param-info% ',r :value ',v))))
;;; setter is a macro, so dont quote the args to it whereas the above
;;; table macro needs quoted args because its 3rd parameter is &rest rst
                  (value `(,',setter ,',v (,table-update-form));embedded event
                        ))
                           
             (value `(progn
                      (table acl2s-defaults-table 
                             ',',',(keywordify param)
                             ',(acl2::change acl2s-param-info% ',r :value ',v))
                      (value-triple ',',v))))))))))))






(defun assoc-eq/pkg-agnostic (s al)
  "If symbol name of s equals a key, return that entry in al"
  (declare (xargs :guard (and (symbolp s) (symbol-alistp al))))
  (if (endp al)
      '()
    (if (equal (symbol-name (caar al)) (symbol-name s))
        (car al)
      (assoc-eq/pkg-agnostic s (cdr al)))))

; some useful utility functions used in main and in this file
(defun acl2s-defaults-value-alist. (defaults override-alist ans.)
  (declare (xargs :verify-guards nil
                  :guard (and (symbol-alistp defaults)
                              (symbol-alistp override-alist)
                              (symbol-alistp ans.))))
  (if (endp defaults)
      ans.
    (b* (((cons param rec-val) (car defaults))
         (val (acl2::access acl2s-param-info% rec-val :value))
         (override (assoc-eq/pkg-agnostic param override-alist))
         (val (if override (cdr override) val)))
      (acl2s-defaults-value-alist. (cdr defaults) 
                                   override-alist 
                                   (cons (cons param val) ans.)))))

(defmacro acl2s-defaults-alist (&optional override-alist)
  "return alist mapping acl2s-parameters to their default values
overridden by entries in override-alist"
  `(acl2s-defaults-value-alist. (table-alist 'ACL2S-DEFAULTS-TABLE (w state))
                                ,override-alist '()))

(defun acl2s-parameter-p (key)
  (declare (xargs :guard t))
  (and (symbolp key)
       (member-eq (keywordify key) *acl2s-parameters*)))




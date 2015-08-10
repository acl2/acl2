;;; This is a supporting file for Chapter 11, "Using Macros to Mimic
;;; VHDL", by Dominique Borrione, Philippe Georgelin, and Vanderlei
;;; Rodrigues, in "Computer-Aided Reasoning: ACL2 Case Studies",
;;; edited by M. Kaufmann, P. Manolios, J Moore (Kluwer, 2000,
;;; p.167-182).

;;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;; Book vhdl.lisp
;;;
;;; Inside the VHDL macro, we represent VHDL entities and
;;; architectures using the following syntax:
;;;
;;; ENTITY ::=  (_entity NAME :port (PORT ...))
;;; PORT  ::=  NAME :in TYPE
;;;            NAME :out TYPE
;;; ARCHITECTURE ::= (_architecture NAME :of NAME
;;;                   :is (DEC-SIGNAL ...)
;;;                   :begin (PROCESS ...))
;;; DEC-SIGNAL  ::=  (_signal NAME :type TYPE)
;;;                  (_signal NAME :type TYPE := EXP)
;;; PROCESS  ::=  (_process NAME
;;;                   :is (DEC-VAR ...)
;;;                   :begin ((_wait :until COND)
;;;                           CMD ...))
;;; DEC-VAR  ::=  (_variable NAME :type TYPE)
;;;               (_variable NAME :type TYPE := EXP)
;;; CMD  ::=  (_<= NAME EXP)
;;;           (_<- NAME EXP)
;;;           (_if COND :then (CMD ...) :else (CMD ...))
;;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")


;;; ==============
;;; Miscellaneous
;;; ==============

;;; Find value associated to a keyword in a keyword-value list

(defun keyword-value (key list) (cadr (assoc-keyword key list)))

;;; Find value associated to a symbol in an assoc-list

(defun assoc-value (key list) (cdr (assoc-equal key list)))

;;; Convert a natural number to a string

(defun digit-to-string (n)
  (if (and (<= 0 n) (< n 10))
      (nth n '("0" "1" "2" "3" "4" "5" "6" "7" "8" "9"))
      "*"))

(defun natural-to-string (arg)
  (let* ((n (nfix arg))
	 (quot (nonnegative-integer-quotient n 10))
	 (rest (- n (* quot 10))))
    (if (< n 10)
	(digit-to-string n)
        (concatenate 'string (natural-to-string quot)
		             (digit-to-string rest)))))

;;;; ==================
;;;; Naming Conventions
;;;; ==================

;;; Make an event name (a symbol) from a component name, adding
;;; a prefix and a suffix

(defun make-name (prefix name suffix)
    (intern (string-upcase (concatenate 'string (string prefix)
					        (string name)
						(string suffix)))
	    "ACL2"))

;;; Add prefix to a program name to make it unique in a global context.

(defun prefix-name (prefix name)
  (make-name prefix "." name))

;;; Generate name of variable holding next value of a signal

(defun make-name-next (name)
   (make-name "" name "+"))

;;; Generate name of variable holding current value of a signal from
;;; name of variable holding its next value

(defun make-base-name (name)
  (let ((s (string name)))
    (make-name "" (subseq s 0 (1- (length s))) "")))

;;; Generate intermediate state name from a given number

(defun make-state-name (n)
  (make-name "" "state-" (natural-to-string n)))

;;;; =====================
;;;; Environment Functions
;;;; =====================

;;; A component environment is an assoc-list describing signals
;;; and variables of an entity or architecture.  The descriptor
;;; for each identifier indicates its kind, type, initial value,
;;; and offset in state record.  The possible identifier kinds
;;; are input (input signal), output (output signal), signal
;;; (local signal), next (next value of signals), and var (local
;;; variable).

(defun make-ident-desc (kind typ init offset)
  (list kind typ init offset))
(defun ident-desc-kind (desc) (car desc))
(defun ident-desc-type (desc) (cadr desc))
(defun ident-desc-init (desc) (caddr desc))
(defun ident-desc-offset (desc) (cadddr desc))

;;; A program environment is an assoc-list describing program
;;; components.  The descriptor for each identifier indicates
;;; its kind and its environment.  The possible component kinds
;;; are entity and architecture.

(defun make-comp-desc (kind env) (list kind env))
(defun comp-desc-kind (desc) (car desc))
(defun comp-desc-env (desc) (cadr desc))

;;; Prefix names in environment to make then unique in global context

(defun prefix-env (prefix env)
  (if (consp env)
      (acons (prefix-name prefix (caar env))
	     (cdar env)
	     (prefix-env prefix (cdr env)))
      nil))

;;;; ==================
;;;; Entity Environment
;;;; ==================

;;; Extract the environment from the port list of an entity
;;; declaration.

(defun build-port-env (ports)
  (if (consp ports)
      (let ((name (car ports))
	    (kind (if (eql (cadr ports) :in) 'input 'output))
	    (typ (caddr ports))
            (other-ports (cdddr ports)))
	(acons name
	       (make-ident-desc kind typ nil 0)
	       (build-port-env other-ports)))
      nil))

;;;; ===================
;;;; Process Environment
;;;; ===================

;;; Build environment describing variables local to a process.

(defun build-var-env (prefix decs)
  (if (consp decs)
      (let* ((dec (car decs))
	     (name (prefix-name prefix (cadr dec)))
	     (typ (keyword-value :type (cddr dec)))
	     (init (keyword-value := (cddr dec)))
	     (other-decs (cdr decs)))
	(acons name
	       (make-ident-desc 'var typ init 0)
	       (build-var-env prefix other-decs)))
      nil))

;;; Build environment describing process list

(defun build-process-env (processes)
  (if (consp processes)
      (let* ((proc (car processes))
	     (name (cadr proc))
	     (local-vars (keyword-value :is (cddr proc)))
	     (var-env (build-var-env name local-vars))
	     (other-procs (cdr processes)))
	(append var-env
		(build-process-env other-procs)))
      nil))

;;;; ========================
;;;; Architecture Environment
;;;; ========================

;;; Build environment describing local signals.

(defun build-signal-env (decs)
  (if (consp decs)
      (let* ((dec (car decs))
	     (name (cadr dec))
	     (typ (keyword-value :type (cddr dec)))
	     (init (keyword-value := (cddr dec)))
	     (other-decs (cdr decs)))
	(acons name
	       (make-ident-desc 'signal typ init 0)
	       (build-signal-env other-decs)))
      nil))

;;; Create environment with next value (for signals)

(defun build-next-env (env)
  (if (consp env)
      (let ((name (caar env))
	    (desc (cdar env))
	    (rest-env (cdr env)))
	(acons (make-name-next name)
	       (make-ident-desc 'next
				(ident-desc-type desc)
				(ident-desc-init desc)
				0)
	       (build-next-env rest-env)))
      nil))

;;; Extract environment elements of a given kind

(defun extract-env-kind (env kind)
  (if (consp env)
      (let ((name (caar env))
	    (desc (cdar env))
	    (tail (extract-env-kind (cdr env) kind )))
	(if (equal (ident-desc-kind desc) kind)
	    (acons name desc tail)
	    tail))
    nil))

;;; Allocate offset in state record for environment elements

(defun alloc-env (env offset)
  (if (consp env)
      (let ((name (caar env))
	    (desc (cdar env))
	    (rest-env (cdr env)))
	(acons name
	       (make-ident-desc (ident-desc-kind desc)
				(ident-desc-type desc)
				(ident-desc-init desc)
				offset)
		   (alloc-env rest-env (1+ offset))))
      nil))

;;; Sort entries in architecture environment and assigns offsets

(defun sort-architecture-env (entity-env signal-env process-env)
  (let* ((input-env (extract-env-kind entity-env 'input))
	 (output-env (extract-env-kind entity-env 'output))
	 (next-output-env (build-next-env output-env))
	 (next-signal-env (build-next-env signal-env)))
    (alloc-env (append input-env
		       output-env
		       signal-env
		       next-output-env
		       next-signal-env
		       process-env)
	       0)))

;;; Build environment describing an architecture.  It includes
;;; the entity identifiers, local signals and local process
;;; variables.

(defun build-architecture-env (arch env)
  (let* ((arch-body (cddr arch))
	 (entity-name (keyword-value :of arch-body))
	 (local-signals (keyword-value :is arch-body))
	 (process-list (keyword-value :begin arch-body))
	 (entity-env (comp-desc-env (assoc-value entity-name env)))
	 (signal-env (build-signal-env local-signals))
	 (process-env (build-process-env process-list)))
    (sort-architecture-env entity-env signal-env process-env)))

;;;; ===================
;;;; Program Environment
;;;; ===================

;;; Build environment describing a program component.  It gets
;;; a program environment describing previously known program
;;; components.

(defun build-component-env (comp env)
  (case (car comp)
    (_entity (make-comp-desc 'entity
			     (build-port-env (keyword-value :port (cddr comp)))))
    (_architecture (make-comp-desc 'architecture
				   (build-architecture-env comp env)))
    (t nil)))

;;; Build program environment composed of the environment of each
;;; program component

(defun build-prog-env-iter (prog env)
  (if (consp prog)
      (let* ((comp (car prog))
	     (comp-name (cadr comp))
	     (comp-env (build-component-env comp env))
	     (new-env (if (null comp-env)
			  env
			  (acons comp-name comp-env env))))
	(build-prog-env-iter (cdr prog) new-env))
      env))
(defun build-prog-env (prog)
  (build-prog-env-iter prog nil))

;;;; ============
;;;; Master Macro
;;;; ============

;;; Insert program environment in inner macros, and remove
;;; _entity macros

(defun insert-prog-env (prog env)
  (if (consp prog)
      (if (equal (caar prog) '_entity)
	  (insert-prog-env (cdr prog) env)
	  `((,@(car prog) :env ,env)
	    ,@(insert-prog-env (cdr prog) env)))
      nil))

;;; Generate ACL2 representation of a VHDl program, through the
;;; expansion of inner macros.  Generates:
;;; - constant *prog*: program text;
;;; - constant *env*: program environment;
;;; - plus expansion of program components.

(defmacro vhdl (&body prog)
  (let ((env (build-prog-env prog)))
    `(progn
       (defconst *prog* (quote (vhdl ,@prog)))
       (defconst *env* (quote ,env))
       ,@(insert-prog-env prog env)
       )))

;;;; ====================
;;;; State Representation
;;;; ====================

;;; Standard function to replace one element of a list.  It is called
;;; by the expansion of macro-functions

(defun insert-value (offset new-value st)
  (if (and (integerp offset) (<= 0 offset) (consp st))
      (if (equal offset 0)
	  (cons new-value (cdr st))
	  (cons (car st) (insert-value (1- offset) new-value (cdr st))))
      st))

;;; Generate names for state related ACL2 events

(defun name-state-size (arch) (make-name "*" arch "-state-size*"))
(defun name-var-p (arch) (make-name "" arch "-var-p"))
(defun name-get-nth (arch) (make-name "" arch "-get-nth"))
(defun name-get-var (arch) (make-name "" arch "-get"))
(defun name-put-var (arch) (make-name "" arch "-put"))
(defun name-update-signals (arch) (make-name "" arch "-update-signals"))
(defun name-param-var (var) (make-name "" var "-p"))
(defun name-make-state-const (arch) (make-name "*" arch "-make-state*"))
(defun name-make-state (arch) (make-name "" arch "-make-state"))

;;; Make predicate body recognizing variable and signal names.

(defun make-var-p (env)
  (if (consp env)
      `((equal var (quote ,(caar env))) ,@(make-var-p (cdr env)))
      nil))

;;; Make function body mapping local names to offset in state record.

(defun make-get-nth (env)
  (if (consp env)
      (let ((name (caar env))
	    (desc (cdar env))
	    (rest-env (cdr env)))
      `(((equal var (quote ,name)) ,(ident-desc-offset desc))
	,@(make-get-nth rest-env)))
      `((t 0))))

;;; Make function body updating current value of signals with
;;; corresponding next value.


(defun make-update-signals (arch env)
  (if (consp env)
      (let ((name (caar env))
	     (desc (cdar env))
	     (rest-env (cdr env)))

       (case (ident-desc-kind desc)
             ((signal output)
                `(,(name-put-var arch)
                                (,(name-get-var arch)
                                      st
                                     (quote ,(make-name-next name)))
                               (quote ,name)
                               ,(make-update-signals arch rest-env)))
              (t (make-update-signals arch rest-env))))
      'st))



;;; Find initial value of a variable.  If no initial value was declared,
;;; the initial value comes from the type declaration.

(defun init-var-value (desc)
  (let ((init (ident-desc-init desc))
	(typ (ident-desc-type desc)))
    (if (null init)
	(cond ((equal typ 'natural) 0)
	      ((equal typ 'integer) 0)
	      ((equal typ 'boolean) nil)
	      ((equal typ 'bit) 0)
	      (t ))  ; user type
        init)))

;;; Make key-word parameter list for macro creating a state.  The default
;;; value for each variable comes from its declaration.  For the next
;;; value of signals, we need to know if some value was actually supplied.

(defun make-param-state (env)
  (if (consp env)
      (let* ((name (caar env))
	     (desc (cdar env))
	     (rest-param (make-param-state (cdr env))))
	(if (equal (ident-desc-kind desc) 'next)
	    `((,name
	       (quote ,(init-var-value desc))
	       ,(name-param-var name))
	      ,@rest-param)
	    `((,name
	       (quote ,(init-var-value desc)))
	      ,@rest-param)))
      nil))

;;; Make body for macro creating a state.  The initial value comes
;;; from the parameter list, except for variables holding the next
;;; value of signals.  For these variables, it comes from the value
;;; of the variable holding the current value of signal.

(defun make-body-state (env)
  (if (consp env)
      (let* ((name (caar env))
	     (desc (cdar env))
	     (rest-body (make-body-state (cdr env))))
	(if (equal (ident-desc-kind desc) 'next)
	    (cons `(if ,(name-param-var name)
		       ,name
		       ,(make-base-name name))
		  rest-body)
	    (cons name rest-body)))
      nil))

;;; Make declaration of macro to create a state

(defun make-decl-state (arch env)
  `(defmacro ,(name-make-state arch)
             (&key ,@(make-param-state env))
     (list 'quote (list ,@(make-body-state env)))))

;;; Maps architecture environment into a state, generating:
;;; - constant *<arch>-state-size*: number of elements in state record;
;;; - function <arch>-var-p: recognizer for local names;
;;; - function <arch>-get-nth: mapping of local names to corresponding
;;;   offset in state record;
;;; - function <arch>-get-var: fetch value of variable in state;
;;; - function <arch>-set-var: update value of variable in state;
;;; - function *<arch>-update*: text defining next function;
;;; - function <arch>-update: update signals;
;;; - function <arch>-make-state: macro creating a state.

(defun expand-env (arch env)
  (let ((macro-mk-state (make-decl-state arch env)))
    `((defconst ,(name-state-size arch)
	,(length env))
      (defun ,(name-var-p arch) (var)
	(or ,@(make-var-p env)))
      (defun ,(name-get-nth arch) (var)
	(cond ,@(make-get-nth env)))
      (defun ,(name-get-var arch) (st var)
	(nth (,(name-get-nth arch) var) st))
      (defun ,(name-put-var arch) (new var st)
	(insert-value (,(name-get-nth arch) var) new st))
      (defconst ,(make-name "*" (name-update-signals arch) "*")
	(quote (defun ,(name-update-signals arch) (st)
		,(make-update-signals arch env))))
      (defun ,(name-update-signals arch) (st)
	  ,(make-update-signals arch env))
      (defconst ,(name-make-state-const arch)
	(quote ,macro-mk-state))
      ,macro-mk-state
      )))

;;;; =============
;;;; Process Macro
;;;; =============

;;; Generate names for process related ACL2 events

(defun name-proc-cycle-const (proc ) (make-name "*" proc "-cycle*"))
(defun name-proc-cycle (proc ) (make-name "" proc "-cycle"))

;;; Expand name ocurring in an expression into a signal or a variable
;;; name.  For variable names, it prefixes the process name.

(defun expand-var-signal (proc-name env name)
  (let ((var-name (prefix-name proc-name (string name))))
    (if (null (assoc-value var-name env))
	name        ; signal name or undeclared variable
        var-name))) ; variable name

;;; The functions bellow expand commands.  They always take the
;;; following arguments:
;;; - st: state where the command begins its evaluation; it is
;;;    declared globally, outside the command;
;;; - proc-name: name of process to be added in front of local vars;
;;; - arch-name: name of architecture to be added in front of functions
;;;   getting and setting variables and values;
;;; - env: to find if symbols are variables or signals;
;;; These functions map a command to an expression that evaluates
;;; to the resulting state of command execution.
;;; WARNING: it does not handle backquotes.

(mutual-recursion
  (defun expand-exp (st proc-name arch-name env e)
    (cond ((or (stringp e) (symbolp e))
	   `(,(name-get-var arch-name)
             ,(make-state-name st)
	     (quote ,(expand-var-signal proc-name env e))))
	  ((consp e)
	   (if (eql (car e) 'quote)
	       e
	       (cons (car e)
		     (expand-exp-list st proc-name arch-name
				      env (cdr e)))))
	  (t e)))
  (defun expand-exp-list (st proc-name arch-name env list)
    (if (consp list)
	(cons (expand-exp st proc-name arch-name env (car list))
	      (expand-exp-list st proc-name arch-name env (cdr list)))
        nil)))

;;; Generate variable assignment

(defun make-var-assign (st proc-name arch-name env var exp)
  `(,(name-put-var arch-name)
    ,(expand-exp st proc-name arch-name env exp)
    (quote ,(expand-var-signal proc-name env var))
    ,(make-state-name st)))

;;; Generate signal assignment

(defun make-signal-assign (st proc-name arch-name env signal exp)
  `(,(name-put-var arch-name)
    ,(expand-exp st proc-name arch-name env exp)
    (quote ,(make-name-next (expand-var-signal proc-name env signal)))
    ,(make-state-name st)))

;;; Generate conditional command

(defun make-if-cmd (st proc-name arch-name env cond then else)
  `(if ,(expand-exp st proc-name arch-name env cond)
       ,then
       ,else))

;;; Generate command sequences.  The argument is a list of pairs
;;; where the cadr is a command expansion, and the car is the
;;; name of the state it should be bounded to.  The next command
;;; in the sequence uses this name as the beginning state.
;;; The argument st is the beginning state for the first
;;; command.

(defun make-seq-cmd (st list)
  (cond ((and (consp list) (null (cdr list))) ; unitary seq.
	  (cadar list))
	((consp list) ; sequence with more than one element
	  `(let* ,list ,(caar (last list))))
	(t ; empty sequence
	  (make-state-name st))))

;;; Expand commands and command lists

(mutual-recursion
  (defun expand-cmd-list (st proc-name arch-name env cmd-list)
    (if (consp cmd-list)
	(cons (list (make-state-name (1+ st))
		    (expand-cmd st proc-name arch-name env
				(car cmd-list)))
	      (expand-cmd-list (1+ st) proc-name arch-name env
			       (cdr cmd-list)))
        nil))
  (defun expand-cmd (st proc-name arch-name env cmd)
    (case (car cmd)
      (_<- (make-var-assign st proc-name arch-name env
			    (cadr cmd) (caddr cmd)))
      (_<= (make-signal-assign st proc-name arch-name env
			       (cadr cmd) (caddr cmd)))
      (_if (make-if-cmd st proc-name arch-name env (cadr cmd)
	       (make-seq-cmd st
			     (expand-cmd-list st proc-name arch-name env
					      (cadddr cmd)))
	       (make-seq-cmd st
			     (expand-cmd-list st proc-name arch-name env
					      (caddr (cdddr cmd))))))
      (t (make-state-name st)))))

;;; Expand sequence of commands

(defun expand-cmd-seq (st proc-name arch-name env cmd-seq)
  (make-seq-cmd st
                (expand-cmd-list st proc-name arch-name env cmd-seq)))

;;; Expand process body into function parameter list and body

(defun expand-process-body (proc-name arch-name env body)
  (let* ((init-st 1)
	 (init-st-name (make-state-name init-st)))
    `((,init-st-name)
       ,(expand-cmd-seq init-st proc-name arch-name env body))))

;;; Process macro generating:
;;; - constant *<proc>-cycle*: body of process representation
;;; - function <proc>-cycle: process representation

(defmacro _process (name &key is begin arch env)
  (declare (ignore is))
  (let* ((expansion (expand-process-body name arch env (cdr begin)))
	 (full-name (prefix-name arch name))
	 (name-proc-fun (make-name "" full-name "")))
    `(progn
       (defconst ,(name-proc-cycle-const full-name)
	 (quote (defun ,name-proc-fun ,@expansion)))
       (defun ,(name-proc-cycle full-name)
	 ,@expansion))))

;;;; ==================
;;;; Architecture Macro
;;;; ==================

;;; Generate names for process related ACL2 events

(defun name-arch-cycle-const (arch) (make-name "*" arch "-cycle*"))
(defun name-arch-cycle (arch) (make-name "" arch "-cycle"))
(defun name-arch-simul-const (arch) (make-name "*" arch "-simul*"))
(defun name-arch-simul (arch) (make-name "" arch "-simul"))

;;; Insert architecture name and environment in processes macros,
;;; expand the process macros.

(defun expand-architecture-body (processes arch env)
  (if (consp processes)
      (let ((proc (car processes))
	    (rest-proc (cdr processes)))
	`((,@proc :arch ,arch :env ,env)
	  ,@(expand-architecture-body rest-proc arch env)))
      nil))

;;; Collect names of processes

(defun collect-proc-names (arch processes)
  (if (consp processes)
      (cons (prefix-name arch (cadar processes))
	    (collect-proc-names arch (cdr processes)))
      nil))

;;; Make body of function performing the simulation cycle for an
;;; architecture.  It calls each process cycle and then update signals.

(defun make-arch-cycle (proc-names)
  (if (consp proc-names)
      `(,(name-arch-cycle (car proc-names))
	,(make-arch-cycle (cdr proc-names)))
      'st))

;;; Architecure macro generating:
;;; - state representation;
;;; - expansion of processes;
;;; - cycle and simulation function for architecture.

(defmacro _architecture (name &key of is begin env)
  (declare (ignore of is))
  (let ((env (comp-desc-env (assoc-value name env)))
	(cycle-fun
	   `(defun ,(name-arch-cycle name) (st)
	      (,(name-update-signals name)
	       ,(make-arch-cycle (collect-proc-names name begin)))))
	(simul-fun
	   `(defun ,(name-arch-simul name) (n st)
	      (if (zp n) st
		  (,(name-arch-simul name)
		   (1- n)
		   (,(name-arch-cycle name) st))
		  ))))
    `(progn
       ,@(expand-env name env)
       ,@(expand-architecture-body begin name env)
       (defconst ,(name-arch-cycle-const name)
         (quote ,cycle-fun))
       ,cycle-fun
       (defconst ,(name-arch-simul-const name)
         (quote ,simul-fun))
       ,simul-fun
       )))



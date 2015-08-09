;;;***************************************************************
;;;Proof of Correctness of a Floating Point Multiplier

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1999
;;;***************************************************************

(in-package "ACL2")

;;COMPILE-PIPELINE generates an executable ACL2 representation of a
;;pipeline that computes the value of a specified output signal as a
;;function of inputs.  If the output of the RTL-ACL2 translator is
;;the file "<fname>.trans", then the executable version is written to
;;"<fname>.lisp".

;;A second file, "<fname>-star.lisp", is also generated.  This file
;;implements a scheme for proving theorems about the executable version.
;;This file contains a definition of a constant function SIG*
;;corresponding to each noninput signal SIG, and a theorem that allows
;;these functions to be used in place of the executable model.  Before
;;the file can be loaded, a constant function symbol IN* corresponding
;;to each input signal IN must be introduced and appropriately
;;constrained (via ENCAPSULATE) by the user.

;;In the following definitions, the parameter defs represents a list
;;of all the forms read from the input file "<fname>.trans".


;;a list of the names of all defined signals:

(defun get-sig-names (defs)
  (if (consp defs)
      (cons (cadar defs) (get-sig-names (cdr defs)))
    ()))

;;list of all input names:

(defun get-input-names (defs)
  (if (consp defs)
      (if (eql (caar defs) 'definput)
	  (cons (cadar defs) (get-input-names (cdr defs)))
	(get-input-names (cdr defs)))
    ()))

;;the signal definition for a given name:

(defun find-signal (name defs)
  (if (consp defs)
      (if (eql name (cadar defs))
	  (car defs)
	(find-signal name (cdr defs)))
    ()))

;;a list of all the signal names that occur in a term:

(mutual-recursion

 (defun signals-occurring-in-term (term defs)
   (declare (xargs :mode :program))
   (cond ((not (consp term))
	  ())
	 ((consp (car term))
	  (signals-occurring-in-term-list term defs))
	 ((find-signal (car term) defs)
	  (union-eq (list (car term))
		    (signals-occurring-in-term-list (cdr term) defs)))
	 (t
	  (signals-occurring-in-term-list (cdr term) defs))))

 (defun signals-occurring-in-term-list (terms defs)
   (declare (xargs :mode :program))
   (if (consp terms)
       (union-eq (signals-occurring-in-term (car terms) defs)
		 (signals-occurring-in-term-list (cdr terms) defs))
     ())))

;;a direct supporter of a signal is a signal that occurs in its definition:

(defun direct-supporters (name defs)
  (declare (xargs :mode :program))
  (signals-occurring-in-term (cadddr (find-signal name defs)) defs))

(defun direct-supporters-list (names defs)
  (declare (xargs :mode :program))
  (if (consp names)
      (cons (direct-supporters (car names) defs)
	    (direct-supporters-list (cdr names) defs))
    ()))

;;A supporter of a signal is a direct supporter or a supporter of a
;;direct supporter.  The function CHECK-CIRCUIT determines whether
;;there exists a signal that supports itself.  Its definition depends
;;a function FIND-CYCLE, which takes a signal and a set of signals and
;;looks for a path of direct support from the signal that either contains
;;a cycle or leads to some member of the set:

(mutual-recursion

 (defun find-cycle (sig set checked defs)
   ;;Look for
   (declare (xargs :mode :program))
   (cond ((member sig checked)
	  ())
	 ((member sig set)
	  (cons sig set))
	 (t
	  (find-cycle-list (direct-supporters sig defs)
			   (cons sig set)
			   checked
			   defs))))

 (defun find-cycle-list (list set checked defs)
   (declare (xargs :mode :program))
   (and (consp list)
	(or (find-cycle (car list) set checked defs)
	    (find-cycle-list (cdr list) set (cons (car list) checked) defs)))))

;;EXTRACT-CYCLE returns the cycle found by FIND-CYCLE:

(defun extract-cycle (new base old)
  (declare (xargs :mode :program))
  (if (consp new)
      (if (eql (car new) base)
	  (cons (car new) old)
	(extract-cycle (cdr new) base (cons (car new) old)))
    ()))

;;CHECK-CIRCUIT returns either a cycle or the symbol NIL:

(defun check-circuit (defs)
  (declare (xargs :mode :program))
  (let ((cycle (find-cycle-list (get-sig-names defs) () () defs)))
    (and cycle
	 (extract-cycle (cdr cycle)
			(car cycle)
			(list (car cycle))))))

;;Once a circuit is known to be acyclic, we may order its signals in
;;such a way that each signal is preceded by all of its supporters:

(defun ordered-signals-aux (names defs list)
  (declare (xargs :mode :program))
  (cond ((not (consp names))
	 list)
	((member (car names) list)
	 (ordered-signals-aux (cdr names) defs list))
	(t
	 (ordered-signals-aux (cdr names)
			      defs
			      (cons (car names)
				    (ordered-signals-aux
				      (direct-supporters (car names) defs)
				      defs
				      list))))))

(defun ordered-signals (defs)
  (declare (xargs :mode :program))
  (reverse (ordered-signals-aux (get-sig-names defs) defs ())))

;;a pipeline is a circuit in which every signal may be assigned a "cycle
;;number" such that (a) all inputs have cycle number 0, (b) a wire with
;;cycle number k is directly supported only by signals with cycle
;;number k, and (c) a register with cycle number n is directly supported
;;only be signals with cycle number n-1.  CYCLE-NUMBERS attempts to compute
;;a cycle number for each signal of a circuit:

(defun consistent-cycle-numbers (names num alist)
  (if (consp names)
      (and (= num (cdr (assoc (car names) alist)))
	   (consistent-cycle-numbers (cdr names) num alist))
    t))

(defun collect-cycle-numbers (names defs alist)
  (declare (xargs :mode :program))
  (if (consp names)
      (if (assoc (car names) alist)
	  (collect-cycle-numbers (cdr names) defs alist)
	(let ((supporters (direct-supporters (car names) defs)))
	  (if (null supporters)
	      (collect-cycle-numbers (cdr names)
				     defs
				     (cons (cons (car names) 1) alist))
	    (let ((num (cdr (assoc (car supporters) alist))))
	      (and (consistent-cycle-numbers (cdr supporters)
					     num
					     alist)
		   (case (car (find-signal (car names) defs))
		     (defwire
			 (collect-cycle-numbers (cdr names)
						defs
						(cons (cons (car names) num)
						      alist)))
		     (defreg
			 (collect-cycle-numbers (cdr names)
						defs
						(cons (cons (car names)
							    (1+ num))
						      alist)))))))))
    alist))

(defun cycle-numbers (defs)
  (declare (xargs :mode :program))
  (reverse (collect-cycle-numbers (ordered-signals defs) defs ())))

;;PIPELINEP recognizes pipelines:

(defun pipelinep (defs)
  (declare (xargs :mode :program))
  (and (cycle-numbers defs) t))


(mutual-recursion

 (defun remove-parentheses (term names)
   (declare (xargs :mode :program))
   (cond ((not (consp term))
	  term)
	 ((consp (car term))
	  (remove-parentheses-list term names))
	 ((member (car term) names)
	  (car term))
	 (t
	  (cons (car term)
		(remove-parentheses-list (cdr term) names)))))

 (defun remove-parentheses-list (terms names)
   (declare (xargs :mode :program))
   (if (consp terms)
       (cons (remove-parentheses (car terms) names)
	     (remove-parentheses-list (cdr terms) names))
     ())))

(defun get-sig-bodies (names defs)
  (if (consp names)
      (cons (cadddr (find-signal (car names) defs))
	    (get-sig-bodies (cdr names) defs))
    ()))

(defun gen-defuns (names args bodies)
  (if (consp names)
      `((defun ,(car names) ,(car args) ,(car bodies))
	,@(gen-defuns (cdr names) (cdr args) (cdr bodies)))
    ()))

(defun bindings (names args)
  (if (consp names)
      `((,(car names) (,(car names) ,@(car args)))
	,@(bindings (cdr names) (cdr args))) ()))

(defun name* (name)
  (intern (string-append (symbol-name name) "*") "ACL2"))

(defun names* (names)
  (if (consp names)
      (cons (name* (car names))
	    (names* (cdr names)))
    ()))

(defun list-names* (names)
  (if (consp names)
      (cons (list (name* (car names)))
	    (list-names* (cdr names)))
    ()))

(defun exec-names* (names)
  (if (consp names)
      (cons (list :executable-counterpart (name* (car names)))
	    (exec-names* (cdr names)))
    ()))

(defun gen-defuns* (names args)
  (if (consp names)
      `((defun ,(name* (car names)) ()
	  (,(car names) ,@(list-names* (car args))))
	,@(gen-defuns* (cdr names) (cdr args)))
    ()))

(set-state-ok t)

(defun collect-objects (list channel state)
  (declare (xargs :mode :program))
  (mv-let (eofp obj state)
	  (read-object channel state)
	  (if eofp
	      (mv (reverse list) state)
	    (collect-objects (cons obj list) channel state))))

(defun read-list (fname state)
  (declare (xargs :mode :program))
  (mv-let (channel state)
	  (open-input-channel fname :object state)
	  (mv-let (result state)
		  (collect-objects () channel state)
		  (let ((state (close-input-channel channel state)))
		    (mv result state)))))

(defun pprint-object (obj channel state)
  (declare (xargs :mode :program))
  (let ((str (if (consp obj) "~xx~%" "~sx~%")))
    (mv-let (col state)
	    (fmt str `((#\x . ,obj))  channel state ())
	    (declare (ignore col))
	    state)))

(defun write-objects (list channel state)
  (declare (xargs :mode :program))
  (if (consp list)
      (let ((state (pprint-object (car list) channel state)))
	(let ((state (write-objects (cdr list) channel state)))
	  state))
    state))

(defun write-list (list fname state)
  (declare (xargs :mode :program))
  (mv-let (channel state)
	  (open-output-channel fname :character state)
	  (let ((state (write-objects list channel state)))
	    (close-output-channel channel state))))

(defun compile-pipeline-fn (name output state)
  (declare (xargs :mode :program))
  (let ((path (if (eql (char name 0) #\/) name (string-append (cbd) name))))
    (mv-let
     (defs state)
     (read-list (string-append path ".trans") state)
     (let ((cycle (check-circuit defs)))
       (cond (cycle
	      (value cycle))
	     ((not (pipelinep defs))
	      (value ()))
	     (t
	      (let* ((names (ordered-signals defs))
		     (inputs (get-input-names defs))
		     (noninputs (set-difference-equal names inputs))
		     (args (direct-supporters-list noninputs defs))
		     (bodies (remove-parentheses-list
			      (get-sig-bodies noninputs defs) names))
		     (list `((in-package "ACL2")
                             (include-book
                              "rtl")
			     ,@(gen-defuns noninputs args bodies)
			     (set-ignore-ok t)
			     (defun ,(intern (string-upcase name) "ACL2") ,inputs
			       (let* ,(bindings noninputs args) ,output))))
		     (list* `((in-package "ACL2")
                              (include-book
                               "spec")
			      ,@(gen-defuns* noninputs args)
			      (in-theory (disable ,@noninputs))
			      (in-theory (disable ,@(exec-names* noninputs)))
			      (defthm ,(intern (string-append (string-upcase name)
							      "-STAR-EQUIVALENCE")
					       "ACL2")
				  (equal ,(list (name* output))
					 (,(intern (string-upcase name) "ACL2")
					  ,@(list-names* inputs)))
				:rule-classes ())
			      (in-theory (disable ,@(names* noninputs)))
			      (in-theory (enable ,@noninputs)))))
		(pprogn (write-list list (string-append path ".lisp") state)
			(write-list list* (string-append path "-star.lisp") state)
			(value t)))))))))

(defmacro compile-pipeline (name output)
  (let ((symbol (if (and (consp output) (eql (car output) 'quote))
		    (cadr output)
		  output)))
    `(compile-pipeline-fn ,name ',symbol state)))


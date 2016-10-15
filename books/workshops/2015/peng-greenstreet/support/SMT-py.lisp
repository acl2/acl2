;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "./helper")
(include-book "./config")
(include-book "./SMT-run")
(include-book "./SMT-interpreter")
(include-book "./SMT-function")
(include-book "./SMT-translator")
(include-book "./SMT-names")
(include-book "./ACL22SMT")
(defttag :tshell)
(value-triple (tshell-ensure))
(set-state-ok t)
(set-ignore-ok t)
(program)

(mutual-recursion
;; lisp-code-print-help
(defun lisp-code-print-help (lisp-code-list indent)
  "lisp-code-print-help: make a printable lisp code list"
  (if (endp lisp-code-list)
      nil
    (list #\Space
	  (lisp-code-print (car lisp-code-list) indent)
	  (lisp-code-print-help (cdr lisp-code-list) indent))))
 
;; lisp-code-print: make printable lisp list
(defun lisp-code-print (lisp-code indent)
  "lisp-code-print: make a printable lisp code list"
  (cond ((equal lisp-code 'nil) "nil") ;; 
	((equal lisp-code 'quote) "'") ;; quote
	((atom lisp-code) lisp-code)
	((and (equal 2 (length lisp-code))
	      (equal (car lisp-code) 'quote))
	 (cons "'"
	       (lisp-code-print (cadr lisp-code)
	 			(cons #\Space
				      (cons #\Space indent)))))
	(t
	 (list #\Newline indent '\(
         (cons (lisp-code-print (car lisp-code)
                                (cons #\Space
                                      (cons #\Space indent)))
               (lisp-code-print-help (cdr lisp-code)
                                     (cons #\Space
                                           (cons #\Space indent))))
         '\) ))))
)

;; my-prove-SMT-formula
(defun my-prove-SMT-formula (term uninterpreted)
  "my-prove-SMT-formula: check if term is a valid SMT formula"
  (b* ( ( (mv decl-list hypo concl)
          (SMT-extract term) ))
      (SMT-formula decl-list hypo concl uninterpreted)))

;; create-uninterpreted-formula
(defun create-uninterpreted-formula (uninterpreted)
  (if (endp uninterpreted)
      nil
    (cons (list (caar uninterpreted)
                (caar uninterpreted)
                (caddar uninterpreted))
          (create-uninterpreted-formula (cdr uninterpreted)))))

;; my-prove-write-file
(defun my-prove-write-file (term fdir smt-config uninterpreted custom-config state)
  "my-prove-write-file: write translated term into a file"
  (b* ( ( (mv decl-list hypotheses concl)
          (my-prove-SMT-formula term (create-uninterpreted-formula uninterpreted)) )
        ( translated-formula (translate-SMT-formula decl-list hypotheses concl uninterpreted) )
        )
      (if (or (equal (smt-cnf) (default-smtlink-config))
              (equal custom-config nil))
          (write-SMT-file fdir (ACL22SMT) translated-formula smt-config custom-config state)
        (write-SMT-file fdir '() translated-formula smt-config custom-config state))
      ))

;; my-prove-write-expander-file
(defun my-prove-write-expander-file (expanded-term fdir state)
  "my-prove-write-expander-file: write expanded term into a log file"
  (if (equal fdir nil)
      state
    (write-expander-file fdir expanded-term state)))

;; create-level
(defun create-level (level index)
  "create-level: creates a name for a level"
  (intern-in-package-of-symbol
   (concatenate 'string level (str::natstr index)) 'ACL2))

;; my-prove-build-log-file
(defun my-prove-build-log-file (expanded-term-list index)
  "my-prove-build-log-file: write the log file for expanding the functions"
  (if (endp expanded-term-list)
      nil
      (cons (list (create-level "level " index) '\:
		  (lisp-code-print
		   (car expanded-term-list) '())
		  #\Newline #\Newline)
	    (my-prove-build-log-file
	     (cdr expanded-term-list) (1+ index)))))

;; translate added hypothesis to underling representation
(defun translate-hypo (hypo state)
  "translate-hypo: translate added hypothesis to underling representation"
  (if (endp hypo)
      (mv nil state)
      (mv-let (res1 state)
	      (translate-hypo (cdr hypo) state)
	      (mv-let (erp res state)
		      (translate (car hypo) t nil t nil (w state) state)
		      (if (endp res)
			  (mv (cons (car hypo) res1) state)
			  (mv (cons res res1) state)))
	      )))

;; translate a let binding for added hypothesis
(defun translate-let (let-expr state)
  "translate-let: translate a let binding for added hypo"
  (if (endp let-expr)
      (mv nil state)
      (mv-let (res1 state)
	      (translate-let (cdr let-expr) state)
	      (mv-let (erp res state)
		      (translate (cadar let-expr) t nil t nil (w state) state)
		      (if (endp res)
			  (mv (cons (list (caar let-expr) (cadar let-expr) (caddar let-expr)) res1) state)
			  (mv (cons (list (caar let-expr) res (caddar let-expr)) res1) state)))
	      )))

;; get-hint-formula
(defun get-hint-formula (name state)
  "get-hint-formula: get the formula by a hint's name"
  (formula name t (w state)))

;; add-hints
(defun add-hints (hints clause state)
  "add-hints: add a list of hints to a clause, in the form of ((not hint3) ((not hint2) ((not hint1) clause)))"
  (if (endp hints)
      clause
      (add-hints (cdr hints)
		 (cons (list 'not (get-hint-formula (car hints) state)) clause)
		 state)))

;; construct augmented result
(defun augment-hypothesis-helper (rewritten-term let-expr orig-param main-hints state)
  "augment-hypothesis: augment the returned clause with \
new hypothesis in lambda expression"
  (cond ((and (endp let-expr) (endp main-hints))
	 (list (list 'not rewritten-term)))
	((and (endp main-hints) (not (endp let-expr)))
	 (list (list 'not
		(cons (list 'lambda (append (assoc-get-key let-expr) orig-param) rewritten-term)
		      (append (assoc-get-value let-expr) orig-param)))))
	((and (not (endp main-hints)) (endp let-expr))
	 (add-hints main-hints (list (list 'not rewritten-term)) state))
	(t
	 (add-hints main-hints
		    (list (list 'not
				(cons (list 'lambda (append (assoc-get-key let-expr) orig-param) rewritten-term)
				      (append (assoc-get-value let-expr) orig-param))))
		    state))
	))

(defun add-aux (clause aux-thms)
  (if (endp aux-thms)
      clause
      (add-aux (let ((thm (car aux-thms)))
		 (cons (list 'not
			     (list 'implies (cadar thm) (cadr thm)))
		       clause))
	       (cdr aux-thms)
	       )))

(defun augment-hypothesis (rewritten-term let-expr orig-param main-hints aux-thms state)
  (let ((res (augment-hypothesis-helper rewritten-term let-expr orig-param main-hints state)))
    (add-aux res aux-thms)))

;;separate-type
(defun separate-type (let-expr)
  "separate-type: separate let expression types from let expression, I do it in this way for convenience. I might want to use them as a whole in the future."
  (if (endp let-expr)
      (mv nil nil)
      (mv-let (res-let-expr res-let-type)
	      (separate-type (cdr let-expr))
	      (mv (cons (list (caar let-expr) (cadar let-expr))
			res-let-expr)
		  (cons (caddar let-expr)
			res-let-type)))))

(defun create-type-theorem-helper-no-hints (decl-hypo-list let-expr let-type)
  (if (endp let-expr)
      nil
      (cons (list (list 'not
			(list 'if (cadr decl-hypo-list)
			      (append-and-hypo (caddr decl-hypo-list)
					       (list (list 'equal (caar let-expr) (cadar let-expr))))
			      ''nil))
		  (list (car let-type) (caar let-expr)))
	    (create-type-theorem-helper-no-hints decl-hypo-list (cdr let-expr) (cdr let-type)))))

(defun create-type-theorem-helper-with-hints (decl-hypo-list let-expr let-type let-hints state)
  (if (endp let-expr)
      nil
      (cons (add-hints (car let-hints)
		       (list (list 'not
				   (list 'if (cadr decl-hypo-list)
					 (append-and-hypo (caddr decl-hypo-list)
							  (list (list 'equal (caar let-expr) (cadar let-expr))))
					 ''nil))
			     (list (car let-type) (caar let-expr)))
		       state)
	    (create-type-theorem-helper-with-hints decl-hypo-list (cdr let-expr) (cdr let-type) (cdr let-hints) state))))


;; create-type-theorem
(defun create-type-theorem (decl-hypo-list let-expr let-type let-hints state)
  "create-type-theorem"
  (if (endp let-hints)
      (create-type-theorem-helper-no-hints decl-hypo-list let-expr let-type)
      (create-type-theorem-helper-with-hints decl-hypo-list let-expr let-type let-hints state)))

(defun create-hypo-theorem-helper-no-hints (decl-hypo-list let-expr hypo-expr orig-param)
  (if (endp hypo-expr)
      nil
      (cons (list (list 'not decl-hypo-list)
		  (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) (car hypo-expr))
			(append (assoc-get-value let-expr) orig-param)))
	    (create-hypo-theorem-helper-no-hints decl-hypo-list let-expr (cdr hypo-expr) orig-param))))

(defun create-hypo-theorem-helper-with-hints (decl-hypo-list let-expr hypo-expr orig-param hypo-hints state)
  (if (endp hypo-expr)
      nil
      (cons (add-hints (car hypo-hints)
	     (list (list 'not decl-hypo-list)
		   (cons (list 'lambda (append (assoc-get-key let-expr) orig-param) (car hypo-expr))
			 (append (assoc-get-value let-expr) orig-param)))
	     state)
	    (create-hypo-theorem-helper-with-hints decl-hypo-list let-expr (cdr hypo-expr) orig-param (cdr hypo-hints) state))))

;; create-hypo-theorem
(defun create-hypo-theorem (decl-hypo-list let-expr hypo-expr orig-param hypo-hints state)
  "create-hypo-theorem: create a theorem for proving user added hypothesis"
  (if (endp hypo-hints)
      (create-hypo-theorem-helper-no-hints decl-hypo-list let-expr hypo-expr orig-param)
      (create-hypo-theorem-helper-with-hints decl-hypo-list let-expr hypo-expr orig-param hypo-hints state)))

;;create-fn-type-theorem
(defun create-fn-type-theorem (decl-hypo-list fn-var-decl)
  ""
  (if (endp fn-var-decl)
      nil
      (cons (list (list 'not
			(list 'if (cadr decl-hypo-list)
			      (append-and-hypo (caddr decl-hypo-list)
					       (list (list 'equal (caar fn-var-decl) (cadar fn-var-decl))))
			      ''nil))
		  (list (caddar fn-var-decl) (caar fn-var-decl)))
	    (create-fn-type-theorem decl-hypo-list (cdr fn-var-decl)))))

;;add-fn-var-decl-helper
(defun add-fn-var-decl-helper (decl-term fn-var-decl)
  ""
  (if (endp fn-var-decl)
      decl-term
      (list 'if
	    (list (caddar fn-var-decl) (caar fn-var-decl))
	    (add-fn-var-decl-helper decl-term (cdr fn-var-decl))
	    ''nil)))

;;add-fn-var-decl
(defun add-fn-var-decl (term fn-var-decl)
  ""
  (if (endp fn-var-decl)
      term
    (list (car term)
          (list (caadr term)
                (add-fn-var-decl-helper (cadadr term) fn-var-decl)
                (caddr (cadr term))
                (cadddr (cadr term)))
          (caddr term))))

;; mk-fname make a file name for the z3 file
;; if fname is nil, it will generate a python file with the name smtlink_XXXXX.py
;; if fname is not nil, it will use that user provided name
(defun mk-fname (fname-LISP smt-config suffix flag)
  (let ((dir (if (equal flag nil)
                 (if (equal (smtlink-config->dir-files smt-config) nil)
                     "/tmp/py_file"
                   (smtlink-config->dir-files smt-config))
               (smtlink-config->dir-expanded smt-config))))
  (cond ((equal fname-LISP nil)
         (let ((cmd (concatenate 'string "mkdir -p " dir " && "
                                 "mktemp " dir "/smtlink" suffix ".XXXXX")))
           (mv-let (exit-status lines)
                   (time$ (tshell-call cmd
                                       :print t
                                       :save t)
                          :msg "; mktemp: `~s0`: ~st sec, ~sa bytes~%"
                          :args (list cmd))
                   (if (equal exit-status 0)
                       (car lines)
                     (er hard? 'top-level "Error(SMT-py): Generate file error.")))))
        ((stringp fname-LISP)
         (concatenate 'string dir "/" (string (lisp-to-python-names fname-LISP)) suffix))
        (t (er hard? 'top-level "Error(SMT-py): fname should either be a string or nil.")))))

;; create-uninterpreted-item
(defun create-uninterpreted-item (item)
  (cons (car item)
        (cons (head (cdr item))
              (end (cdr item)))))

;; uninterpreted-type-&-name: processing the list of uninterpreted functions
;; produces an associate list. Key is the function name, value is a 2 element
;; list. First element is a list of input argument type, second element is the
;; return type.
(defun uninterpreted-type-&-name (uninterpreted)
  (if (endp uninterpreted)
      nil
    (cons (create-uninterpreted-item (car uninterpreted))
          (uninterpreted-type-&-name (cdr uninterpreted))))
  )

;; create-proc-name
;; given name "XXX", create name "_SMT_.XXX"
;; User defined uninterpreted functions are assumed to be all in lower case
(defun create-proc-name (name)
  (concatenate 'string "_SMT_." (string-downcase (string name))))

;; create-uninterpreted-oprt-item
;; By default, using the same name in ACL2.
(defun create-uninterpreted-oprt-item (item)
  (list (car item)
        (create-proc-name (car item))
        (length (cadr item))))

;; uninterpreted-operator
(defun uninterpreted-operator (uninterpreted-assoc)
  (if (endp uninterpreted-assoc)
      nil
    (cons (create-uninterpreted-oprt-item (car uninterpreted-assoc))
          (uninterpreted-operator (cdr uninterpreted-assoc)))))

;; mk-expander-fname
(defun mk-expander-fname (fname smt-config)
  (cond ((equal (smtlink-config->dir-expanded smt-config) nil) nil)
        ((stringp (smtlink-config->dir-expanded smt-config)) (mk-fname fname smt-config ".log" t))
        (t (er hard? 'top-level "Error(SMT-py): expansion log directory should either by a string or nil."))))

;; my-prove
(defun my-prove (term fn-lst fn-level uninterpreted fname let-expr new-hypo
                 let-hints hypo-hints main-hints smt-config custom-config state)
  "my-prove: return the result of calling SMT procedure"
  (b*
   ( ((mv decl-list hypo-list concl) (SMT-extract term))
     (type-or-original (list (and-list-logic decl-list) term))
     (decl-and-hypo (and-list-logic (append decl-list (list hypo-list))))
     (- (cw "testtesttest: ~q0~%" decl-and-hypo))
     (file-dir (mk-fname fname smt-config ".py" nil))
     (expand-dir (mk-expander-fname fname smt-config))
     (uninterpreted-func (uninterpreted-operator (uninterpreted-type-&-name uninterpreted)))
     ((mv hypo-translated state) (translate-hypo new-hypo state))
     ((mv let-expr-translated-with-type state) (translate-let let-expr state))
     ((mv let-expr-translated let-type) (separate-type let-expr-translated-with-type))
     ( (mv expanded-term-list-1 expanded-term-list-2 num orig-param fn-var-decl)
       (expand-fn term fn-lst fn-level let-expr-translated let-type hypo-translated state))
     (expanded-term-list (add-fn-var-decl expanded-term-list-1 fn-var-decl))
     ( - (cw "Expanded(SMT-py): ~q0 Final index number: ~q1" expanded-term-list-1 num))
     (state (my-prove-write-expander-file (my-prove-build-log-file (cons term expanded-term-list) 0)
                                          expand-dir state))
     (state (my-prove-write-file expanded-term-list file-dir smt-config uninterpreted-func custom-config state))
     (type-theorem (create-type-theorem decl-and-hypo let-expr-translated let-type let-hints state))
     (hypo-theorem (create-hypo-theorem decl-and-hypo let-expr-translated hypo-translated orig-param hypo-hints state))
     (fn-type-theorem (create-fn-type-theorem decl-and-hypo fn-var-decl))
     (aug-theorem (augment-hypothesis expanded-term-list-2 let-expr-translated orig-param main-hints
                                      (append fn-type-theorem (append hypo-theorem (append type-theorem)))
                                      state)))
   (if (car (SMT-interpreter file-dir smt-config))
       (mv t aug-theorem type-theorem hypo-theorem fn-type-theorem type-or-original state)
     (mv nil aug-theorem type-theorem hypo-theorem fn-type-theorem type-or-original state))))


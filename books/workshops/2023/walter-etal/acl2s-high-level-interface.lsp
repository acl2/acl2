;; required but already loaded in prover.lisp
;;(load "interface/acl2s-interface.lisp")

(load "util.lsp")

(in-package :acl2s-high-level-interface)

;; each entry should be a list:
;; (query kind time er?)
;; - query is an S-expression corresponding to the query
;; - kind is one of 'query, 'event, or 'compute
;; - time is a number with implementation-defined units representing the
;;   real time that the query took to execute
;; - er? is t if executing the query resulted in an error, and nil otherwise.
(defvar *QUERY-TIME-TABLE* nil)

;; This should be set to T if it's OK for the current query to fail.
(defvar *acl2s-interface-fail-ok* nil)

(defmacro acl2s-interface-wrapper (fn-name fn-label)
  (let ((regular-category (intern (concatenate 'string "QUERY." (symbol-name fn-label)) :keyword))
        (may-fail-category (intern (concatenate 'string "MAY-FAIL-QUERY." (symbol-name fn-label)) :keyword)))
  `(multiple-value-bind (fail-ok provided-fail-ok)
     (ACL2S-INTERFACE-INTERNAL::get-prop args :fail-ok)
     (v:debug (if (or fail-ok *acl2s-interface-fail-ok*)
                  ,may-fail-category
                ,regular-category)
              "~S" q)
     (let ((args (acl2s-interface-internal::remove-prop args :fail-ok))
           (start-time (get-internal-real-time)))
       (handler-case
           (apply ,fn-name q args)
         (error (sig)
           (push (list (- (get-internal-real-time) start-time) ',fn-label t (cons q args))
                 *QUERY-TIME-TABLE*)
           (signal sig))
         (:no-error (val)
           (push (list (- (get-internal-real-time) start-time) ',fn-label nil (cons q args))
                 *QUERY-TIME-TABLE*)
           val))))))

(defun acl2s-query (q &rest args &key &allow-other-keys)
  (acl2s-interface-wrapper #'acl2s-interface::acl2s-query query))

(defun acl2s-event (q &rest args &key &allow-other-keys)
  (acl2s-interface-wrapper #'acl2s-interface::acl2s-event event))

(defun acl2s-compute (q &rest args &key &allow-other-keys)
  (acl2s-interface-wrapper #'acl2s-interface::acl2s-compute compute))

(defun itest?-query (q &rest args &key &allow-other-keys)
  (multiple-value-bind (fail-ok provided-fail-ok)
    (ACL2S-INTERFACE-INTERNAL::get-prop args :fail-ok)
    (v:debug (if (or fail-ok *acl2s-interface-fail-ok*)
                 :may-fail-query.test?
               :query.test?)
             "~S" (list 'acl2s::test? q))
    (let ((args (acl2s-interface-internal::remove-prop args :fail-ok))
          (start-time (get-internal-real-time)))
      (handler-case
          (apply #'acl2s-interface-extras::itest?-query q args)
        (error (sig)
               (push (list (- (get-internal-real-time) start-time) 'test t (cons q args))
                     *QUERY-TIME-TABLE*))
        (:no-error (val)
                   (push (list (- (get-internal-real-time) start-time) 'test nil (cons q args))
                         *QUERY-TIME-TABLE*)
                   ;; TODO: remove this compatibility shim and update consumers
                   ;; to handle itest?-query's updated output format
                   (list (car val) (second (second val))))))))

(defmacro is-one-of (options arg)
  `(or ,@(mapcar #'(lambda (option) `(equal ,arg ,option)) options)))

(defmacro is-op? (op arg)
  (let ((res-name (gensym)))
    `(let ((,res-name ,arg))
       ,(ecase op
          (if `(equal ,arg 'if))
          (and `(is-one-of ('and '^) ,res-name))
          (or `(is-one-of ('or 'v) ,res-name))
          (implies `(is-one-of ('implies '=> '->) ,res-name))
          (not `(is-one-of ('not '!) ,res-name))))))

(trivia:defpattern is-op? (op)
                   (let ((it (gensym)))
                     `(trivia:guard1 (,it :type symbol) (is-op? ,op ,it))))

(defun conjunction-to-list (term)
  "Convert a term to a list of conjuncts.
If the term is an and, this will return a list containing the arguments to that and.
Otherwise a list containing only the given term is returned."
  (if (and (consp term) (or (equal 'and (car term)) (equal '^ (car term))))
      (cdr term)
    (list term)))

(defun get-hyps (expr)
  "Get the hypotheses of an implication, returning nil if the given expression
is not an implication"
  (if (and (consp expr) (is-op? implies (car expr)))
      (conjunction-to-list (second expr))
    nil))

(assert (equal (get-hyps '(implies (and x y) z)) '(x y)))
(assert (equal (get-hyps '(and x y)) nil))
(assert (equal (get-hyps '(=> (and x y (and z w)) q)) '(x y (and z w))))

(defun get-conc (expr)
  "Get the conclusion of an implication, returning the expression if
the given expression is not an implication"
  (if (and (consp expr) (is-op? implies (car expr)))
      (third expr)
    expr))

(assert (equal (get-conc '(implies (and x y) z)) 'z))
(assert (equal (get-conc '(and x y)) '(and x y)))
(assert (equal (get-conc '(=> (and x y) (implies (and z w) q))) '(implies (and z w) q)))

;; Error conditions

(define-condition acl2s-query-error (error)
  ((desc :initarg :desc :reader acl2s-query-error/desc)
   (query :initarg :query :reader acl2s-query-error/query)
   (err :initarg :err :reader acl2s-query-error/err))
  (:report
   (lambda (condition stream)
     (format
      stream
      "Error occurred when running acl2s query:~% error ~a ~% for query: ~a ~% ~S"
      (acl2s-query-error/err  condition)
      (acl2s-query-error/query condition)
      (acl2s-query-error/desc condition)))))

(define-condition rguard-obligations-error (error)
  ((expr :initarg :expr :reader rguard-obligations-error/expr)
   (err :initarg :err :reader rguard-obligations-error/err))
  (:report (lambda (condition stream)
             (format stream "Error getting guard obligations: ~a ~% for expression: ~a"
                     (rguard-obligations-error/err condition)
                     (rguard-obligations-error/expr condition)))))

(define-condition test-found-ctrex-error (error)
  ((msg :initarg :msg :reader test-found-ctrex-error/msg :initform "")
   (cxs :initarg :cxs :reader test-found-ctrex-error/cxs)
   (query :initarg :query :reader test-found-ctrex-error/query))
  (:report (lambda (condition stream)
             (format stream "Found counterexample(s) when ~a: ~% ~a ~% ~a"
                     (test-found-ctrex-error/msg condition)
                     (test-found-ctrex-error/cxs condition)
                     (test-found-ctrex-error/query condition)))))

#|
(define-condition thm-failed-error (error)
((msg :initarg :msg :reader thm-failed-error/msg)
(theory :initarg :theory :reader thm-failed-error/theory)
(query :initarg :query :reader thm-failed-error/query))
(:report (lambda (condition stream)
(format stream "Thm in ~a theory failed: ~a"
(thm-failed-error/theory condition)
(thm-failed-error/msg condition)))))
|#


(define-condition full-thm-failed-error (error)
  ((msg :initarg :msg :reader full-thm-failed-error/msg :initform "")
   (query :initarg :query :reader full-thm-failed-error/query))
  (:report (lambda (condition stream)
             (format stream "Thm in full theory failed: ~a"
                     (full-thm-failed-error/msg condition)))))

(define-condition min-thm-failed-error (error)
  ((msg :initarg :msg :reader min-thm-failed-error/msg :initform "")
   (query :initarg :query :reader min-thm-failed-error/query))
  (:report (lambda (condition stream)
             (format stream "Thm in minimal theory failed: ~a"
                     (min-thm-failed-error/msg condition)))))

(define-condition prover-warning (warning)
  ((msg :initarg :msg :reader prover-warning/msg))
  (:report (lambda (condition stream)
             (format stream (prover-warning/msg condition)))))

(define-condition used-full-theory (prover-warning)
  ((query :initarg :query :reader used-full-theory/query))
  (:report (lambda (condition stream)
             (format stream "Used full theory when proving:~% ~a"
                     (used-full-theory/query condition)))))

(define-condition obligation-thm-failed (prover-warning)
  ((obligation :initarg :obligation :reader obligation-thm-failed/obligation)
   (debug-info :initarg :debug-info :reader obligation-thm-failed/debug-info))
  (:report (lambda (condition stream)
             (format stream "Failed to prove obligation:~%  ~a~% Debug: ~a"
                     (obligation-thm-failed/obligation condition)
                     (obligation-thm-failed/debug-info condition)))))

(define-condition ld-internal-error (error)
  ((query :initarg :query :reader ld-internal-error/query))
  (:report (lambda (condition stream)
             (format stream "LD failed for an unknown reason on query ~S" (ld-internal-error/query condition)))))
   
(define-condition ld-execution-error (error)
  ((query :initarg :query :reader ld-execution-error/query))
  (:report (lambda (condition stream)
             (format stream "The query ~S returned an error" (ld-execution-error/query condition)))))

(define-condition internal-query-error (error)
  ((query :initarg :query :reader internal-query-error/query))
    (:report (lambda (condition stream)
               (format stream "Internal error occurred when running query ~S" (internal-query-error/query condition)))))

(define-condition unexpected-response-error (error)
  ((query :initarg :query :reader unexpected-response-error/query))
    (:report (lambda (condition stream)
             (format stream "Internal error occurred when running query ~S" (unexpected-response-error/query condition)))))

(defun test? (q &key fail-ok)
  (let* ((test-res (itest?-query q :fail-ok fail-ok))
         (found-cx? (car test-res))
         (cxs (second test-res)))
    (if (not found-cx?)
        nil
      cxs)))

;; Run a thm on the given statement in the minimal theory (plus tau system)
(defun thm-min-theory (q &key rules goal-hints fail-ok)
  (when (car (acl2s-event `(in-theory (union-theories (theory 'min-theory) '(,@acl2s-high-level-interface::rules)))))
    (error 'acl2s-query-error
           :err nil
           :query `(in-theory (union-theories (theory 'min-theory) '(,@acl2s-high-level-interface::rules)))
           :desc "in-theory didn't work"))
  (unwind-protect
      (acl2s-query
       `acl2s::(thm ,acl2s-high-level-interface::q
                 :hints (("Goal" ,@acl2s-high-level-interface::goal-hints)))
       :fail-ok fail-ok)
    (acl2::ld '(:u))
    (v:debug :query.query "~S" :u)))

;; Run a thm on the given statement in the current theory
(defun thm-full-theory (q &key rules goal-hints fail-ok)
  (acl2s-query
   `acl2s::(thm ,acl2s-high-level-interface::q
                :hints (("Goal"
                         :in-theory (e/d ,acl2s-high-level-interface::rules nil)
                         ,@acl2s-high-level-interface::goal-hints)))
   :fail-ok fail-ok))

(defun thm-min-theory-with-contracts (q &key rules goal-hints fail-ok)
  (when (car (acl2s-event `(in-theory (union-theories (theory 'contract-theory)
                                                      '(,@acl2s-high-level-interface::rules)))))
    (error 'acl2s-query-error
           :err nil
           :query `(in-theory (union-theories (theory 'min-theory) '(,@acl2s-high-level-interface::rules)))
           :desc "in-theory didn't work"))
  (unwind-protect
      (acl2s-query
       `acl2s::(thm ,acl2s-high-level-interface::q
                 :hints (("Goal" ,@acl2s-high-level-interface::goal-hints)))
       :fail-ok fail-ok)
    (acl2::ld '(:u))
    (v:debug :query.query "~S" :u)))

;; This function:
;; 1. runs test? on the given query. If a counterexample is found, errors.
;;    Otherwise, if no counterexample is found,
;; 2. runs thm in minimal theory. If this succeeds then t is returned.
;;    Otherwise, if thm in minimal theory fails,
;; 3. runs thm in current theory. If this succeeds then t is returned. Otherwise, errors.
(defun test-thm-min-then-full (q &key fail-ok)
  (let* ((test-res (itest?-query q :fail-ok fail-ok))
         (found-cx? (car test-res))
         (cxs (second test-res)))
    (if found-cx?
        (error 'test-found-ctrex-error :cxs cxs :query q)
      (let* ((min-thm-res (thm-min-theory q :fail-ok t))
             (min-thm-err (thm-query-error? min-thm-res)))
        (if (not min-thm-err)
            t
          (let* ((full-thm-res (thm-full-theory q :fail-ok fail-ok))
                 (full-thm-err (thm-query-error? full-thm-res)))
            (if (not full-thm-err)
                (progn (signal 'used-full-theory :query q) t)
              (error 'full-thm-failed-error :query q))))))))

;; Run test? on the given statement, and if no ctrex is found, run a thm in minimal theory.
;; Errors if either a ctrex is found, or the thm in minimal theory fails.
;; Otherwise returns t
;; (defun test-thm-min (q)
;;   (let* ((test-res (itest?-query q))
;;          (found-cx? (car test-res))
;;          (cxs (second test-res)))
;;     (if found-cx?
;;         (error 'test-found-ctrex-error :cxs cxs :query q)
;;       (let* ((min-thm-res (thm-min-theory q))
;;              (min-thm-err (thm-query-error? min-thm-res)))
;;         (if (not min-thm-err)
;;             t
;;           (error 'min-thm-failed-error :query q))))))

;; Run test? on the given statement, and if no ctrex is found, run a
;; thm in minimal theory plus the given rules, and the given goal hints.
;; Errors if either a ctrex is found, or the thm in minimal theory fails.
;; Otherwise returns t
(defun test-thm-min (q &key rules goal-hints fail-ok)
  (let* ((test-res (itest?-query q :fail-ok fail-ok))
         (found-cx? (car test-res))
         (cxs (second test-res)))
    (if found-cx?
        (error 'test-found-ctrex-error :cxs cxs :query q)
      (let* ((min-thm-res (thm-min-theory q :rules rules :goal-hints goal-hints :fail-ok fail-ok))
             (min-thm-err (thm-query-error? min-thm-res)))
        (if (not min-thm-err)
            t
          (error 'min-thm-failed-error :query q))))))

;; Run test? on the given statement, and if no ctrex is found, run a
;; thm in minimal theory plus the given rules, and the given goal hints.
;; Errors if either a ctrex is found, or the thm in minimal theory + contracts fails.
;; Otherwise returns t
(defun test-thm-min-with-contracts (q &key rules goal-hints fail-ok)
  (let* ((test-res (itest?-query q :fail-ok fail-ok))
         (found-cx? (car test-res))
         (cxs (second test-res)))
    (if found-cx?
        (error 'test-found-ctrex-error :cxs cxs :query q)
      (let* ((min-thm-res (thm-min-theory-with-contracts q :rules rules :goal-hints goal-hints :fail-ok fail-ok))
             (min-thm-err (thm-query-error? min-thm-res)))
        (if (not min-thm-err)
            t
          (error 'min-thm-failed-error :query q))))))

;; Run test? on the given statement, and if no ctrex is found, run a thm in current theory.
;; Errors if either a ctrex is found, or the thm in current theory fails.
;; Otherwise returns t
(defun test-thm-full (q &key rules goal-hints fail-ok)
  (let* ((test-res (itest?-query q :fail-ok fail-ok))
         (found-cx? (car test-res))
         (cxs (second test-res)))
    (if found-cx?
        (error 'test-found-ctrex-error :cxs cxs :query q)
      (let* ((full-thm-res (thm-full-theory q :rules rules :goal-hints goal-hints :fail-ok fail-ok))
             (full-thm-err (thm-query-error? full-thm-res)))
        (if (not full-thm-err)
            t
          (error 'full-thm-failed-error :query q))))))

;; This returns nil if neither test? nor thm fail on the given statement
;; Otherwise it either returns a list containing the counterexamples (if test? fails)
;; or t if thm fails.
(defun test-then-thm-min-fails? (q &key fail-ok)
  (handler-case (test-thm-min q :fail-ok fail-ok)
    (:no-error (_) nil)
    (test-found-ctrex-error (condition) (test-found-ctrex-error/cxs condition))
    (min-thm-failed-error (_) t)))

;; need to redefine this so we can log it
(defun guard-obligations-query (expr &key (debug nil) (simplify t))
  "Get the guard obligations for the given expression, possibly with debug info (depending on debug argument)
This will return a CNF of the guard obligations
This will error if the internal acl2s-query returns an unexpected value, or if an error is detected"
  (v:debug :status "Getting guard obligations for ~S" expr)
  (let ((res (acl2s-query `acl2s::(mv-let
			           (erp val)
			           (guard-obligation ',acl2s-high-level-interface::expr nil ,acl2s-high-level-interface::debug ,acl2s-high-level-interface::simplify 'ctx state)
			           (mv erp val state)))))
    (cond ((not (guard-obligations-query-res-ok? res))
           (error "acl2s-query returned an unexpected response in guard-obligations-query: ~a" res))
	  ((or (car res) (equal (car res) 'acl2s::ctx))
	   (error "Error when computing guard obligations for the expression ~S:~%~S" expr res))
	  (t (second (second res))))))

;; Get the guard obligations of the given expression, with debug info
;; This returns a list containing lists where:
;; the first element is the debug info (describing where the obligation came from)
;; the second element is a statement describing the obligations themselves
;; Obligations are converted to ors here so that they can be directly run in ACL2
;; ACL2-numberp is replaced by rationalp inside of obligations
(defun rguard-obligations-debug (expr)
  (let ((val (guard-obligations-query expr :debug t)))
    (mapcar (lambda (x)
              (list (second (car x))
                    (replace-in (cnf-disjunct-to-or (cdr x))
                                'acl2::acl2-numberp
                                'acl2s::rationalp)))
            val)))

;; Get the guard obligations of the given expression
;; This returns a list containing statements describing the obligations themselves
;; Obligations are converted to ors here so that they can be directly run in ACL2
;; ACL2-numberp is replaced by rationalp inside of obligations
(defun rguard-obligations (expr)
  (let ((val (guard-obligations-query expr)))
    (mapcar (lambda (x) (replace-in (cnf-disjunct-to-or x)
                                    'acl2::acl2-numberp
                                    'acl2s::rationalp))
            val)))

(defun redefine-theories ()
  (when (acl2s-query-error? (acl2s-event
                             'acl2s::(deftheory type-prescription-theory
                                       (acl2::rules-of-type :type-prescription (current-theory :here)))
                             :ld-redefinition-action ''(:doit . :overwrite)))
    (error "query error"))
  (when (acl2s-query-error? (acl2s-event
                             'acl2s::(deftheory contract-theory
                                       (union-theories (theory 'min-theory)
                                                       (union-theories
                                                        (contract-theorems (current-theory :here))
                                                        (theory 'type-prescription-theory))))
                             :ld-redefinition-action ''(:doit . :overwrite)))
      (error "query error"))
  (when (acl2s-query-error? (acl2s-event
                             'acl2s::(deftheory executable-theory
                                       (union-theories '((:executable-counterpart acl2::tau-system))
                                                       (acl2::rules-of-type :EXECUTABLE-COUNTERPART (current-theory :here))))
                             :ld-redefinition-action ''(:doit . :overwrite)))
    (error "query error"))
  (when (acl2s-query-error? (acl2s-event
                             'acl2s::(deftheory min-executable-theory
                                       '(min-theory executable-theory))
                             :ld-redefinition-action ''(:doit . :overwrite)))
    (error "query error")))

;; first check syntactic equality, then check using thm-prover, because
;; thm-prover sometimes doesn't equate equal terms
(declaim (ftype (function (t t) (cons boolean t)) find-equiv-term))
(defun find-equiv-term (term1 terms)
  (v:debug :status "find-equiv-term ~S ~S" term1 terms)
  (if (endp terms)
      nil
    (let ((first-term (car terms))
          (term  (acl2s-untranslate term1))
          (*acl2s-interface-fail-ok* t))
      (cond ((equal term first-term) (cons t first-term))
            ((and (consp term) (is-op? implies (car term)))
             (find-equiv-bi-term term terms 'acl2::implies))
            ((and (consp term) (equal (car term) 'acl2::equal))
             (find-equiv-bi-term term terms 'acl2::equal))
            ((and (consp term)
                  (or (is-op? and (car term))
                      (is-op? or (car term))))
             (find-equiv-mono-term term terms (car term)))
            ((test-then-thm-min-fails? `(acl2::equal ,term ,first-term))
             (progn
               ;;(v:debug :status "  Didn't match ~a with ~b" term first-term)
               ;;(print2 (format nil "  Didn't match ~a with ~b" term first-term))
               (find-equiv-term term (cdr terms))))
            (t (cons t first-term))))))

(defun check-term-bijection (student-terms our-terms)
  (v:debug :status "check-term-bijection ~S ~S" student-terms our-terms)
  (cond ((and (endp student-terms) (endp our-terms)) t)
        ((endp our-terms) nil)
        ((endp student-terms) nil)
        (t (let ((equiv-term (find-equiv-term (car student-terms) our-terms)))
             (and (car equiv-term)
                  (check-term-bijection (cdr student-terms) (remove (cdr equiv-term) our-terms) ))))))

;; Given a term with "two sides", determine if there exists a term in the provided list of terms
;; such that a bijection exists between that term's "left side" and this term's, and similar
;; with the "right side".
(declaim (ftype (function (t t t) (cons boolean t)) find-equiv-bi-term))
(defun find-equiv-bi-term (term terms op)
  (cond ((endp terms) (cons nil nil))
        ((and (consp (car terms)) (equal (caar terms) op)) ;; have we found a term that starts with the given op?
         (let* ((first-term (car terms))
                (left  (list (cadr first-term)))
                (right (list (caddr first-term))))
           (if (equal op 'acl2::equal)
               ;; TODO: improve efficiency
               ;; in this case we need to check the 2 different combinations
               ;; because (find-equiv-bi-term '(equal a b) '((equal b a)) 'equal) should be true.
               (let ((left-equiv-1 (find-equiv-term (cadr term) left))
                     (right-equiv-1 (find-equiv-term (caddr term) right))
                     (left-equiv-2 (find-equiv-term (caddr term) left))
                     (right-equiv-2 (find-equiv-term (cadr term) right)))
                 (if (or (and (car left-equiv-1) (car right-equiv-1))
                         (and (car left-equiv-2) (car right-equiv-2)))
                     (cons t (car terms))
                   (find-equiv-bi-term term (cdr terms) op)))
             (let ((left-equiv (find-equiv-term (cadr term) left))
                   (right-equiv (find-equiv-term (caddr term) right)))
               (if (and (car left-equiv) (car right-equiv))
                   (cons t (car terms))
                 (find-equiv-bi-term term (cdr terms) op))))))
        (t (find-equiv-bi-term term (cdr terms) op))))

(declaim (ftype (function (t t t) (cons boolean t)) find-equiv-mono-term))
(defun find-equiv-mono-term (term terms op)
  (cond ((endp terms) (cons nil nil))
        ((and (consp (car terms)) (equal (caar terms) op))
         (let* ((first-term (car terms))
                (args  (cdr first-term)))
           (if (check-term-bijection (cdr term) args)
               (cons t first-term)
             (find-equiv-mono-term term (cdr terms) op))))
        (t (find-equiv-mono-term term (cdr terms) op))))

;;(find-equiv-term 'acl2s::(natp n) 'acl2s::(x (natp n)))
;;(check-term-bijection '(x (natp n)) '((natp n) x))
;;(find-equiv-mono-term '(or x (natp n)) '((or (natp n) x)) 'or)

(defun eval-in-acl2 (stmt)
  (v:debug :query.eval "~S" stmt)
  (let ((*package* (find-package "ACL2S")))
    (acl2::mv-let (erp val _state)
                  (acl2::ld (list acl2s-high-level-interface::stmt))
                  (cond (erp
                         (error 'acl2s-high-level-interface::ld-internal-error :query acl2s-high-level-interface::stmt))
                        ((not (equal val :eof))
                         (error 'acl2s-high-level-interface::ld-execution-error :query acl2s-high-level-interface::stmt))
                        (t t)))))

;; Include a book in the world
(defun include-book-event (book)
  (acl2s-event `acl2s::(include-book ,acl2s-high-level-interface::book)))

(defun get-free-vars (form)
  (second (acl2s-query `(cgen::get-free-vars ',form))))

(defun is-theorem-namep (name)
  (let ((res (acl2s-compute `(acl2::getpropc ',name 'acl2::theorem 0 (acl2::w acl2::state)))))
    (and (not (car res))
         (not (equal (second res) 0)))))

(defun is-type-predicate (fn-name)
  (let ((res (acl2s-compute `(defdata::is-type-predicate ',fn-name (acl2::w acl2::state)))))
    (and (not (car res))
         (not (equal (second res) nil)))))

(defun get-induction-obligations (term scheme)
  (let* ((query `acl2::(mv-let (erp state-stack state)
                             (state-stack-from-instructions
                              ',acl2s-high-level-interface::term ;; raw term
                              'foo ;; event name
                              nil ;; rule-classes
                              ;; needed to add the :then ... :pro-or-skip for examples/ind-examples/pass/subset.proof
                              '((:do-all-no-prompt :pro-or-skip (:then (:induct ,acl2s-high-level-interface::scheme) :pro-or-skip))) ;; instructions
                              t ;; replay flag
                              '(exit signal) ;; quit conditions
                              state)
                             (mv erp (goals t) state)))
         (res (acl2s-query query)))
    (if (car res)
        (error "Failed to get the induction obligations for term ~S with scheme ~S" term scheme)
      (loop for goal in (second res)
            collect  (let ((conc (first goal))
                           (hyps (car (third goal)))
                           (goal-name (fourth goal)))
                       (cons goal-name (cons conc (mapcar #'acl2s-untranslate hyps))))))))

(defun is-acl2-macro (name)
  (let ((res (acl2s-compute `acl2::(getpropc ',acl2s-high-level-interface::name 'macro-args nil (w state)))))
    (and (not (car res)) (second res))))

(defun is-rule-name-designator (name)
  (let ((res (acl2s-compute `acl2s::(acl2::rule-name-designatorp ',acl2s-high-level-interface::name (acl2::macro-aliases (w state)) (w state)))))
    (and (not (car res)) (second res))))

(defun is-function (fn-name)
  (let* ((macro-alias-query `acl2::(deref-macro-name ',acl2s-high-level-interface::fn-name (macro-aliases (w state))))
         (macro-alias-res (acl2s-compute macro-alias-query)))
    (if (car macro-alias-res)
        (error "Failed to determine if ~a is a function name" fn-name)
      (let* ((symbolp-query `acl2::(function-symbolp ',(second acl2s-high-level-interface::macro-alias-res) (w state)))
             (symbolp-res (acl2s-compute symbolp-query)))
        (if (car symbolp-res)
            (error "Failed to determine if ~a is a function name" fn-name)
          (second symbolp-res))))))

(defun is-var (val)
  (let* ((query `acl2s::(varp ',acl2s-high-level-interface::val))
         (res (acl2s-compute query)))
    (if (car res)
        (error "Failed to determine if ~a is a var" val)
      (second res))))

(defun is-acl2s-term (val)
  (let ((res (acl2s-query `acl2s::(valid-acl2s-termp ',acl2s-high-level-interface::val state))))
    (and (not (car res)) (second res))))

(defun is-acl2s-term-capture-error (val)
  (let ((res (acl2s-compute
              ;; I'd rather use b* here but ran into issues doing so
              `acl2s::(mv-let (ctx msg)
                             (acl2::translate-cmp ',acl2s-high-level-interface::val t nil t 'ctx (w state) (default-state-vars t))
                             (declare (ignore ctx))
                             (mv-let (col str)
                                     (acl2::fmt-to-string (car msg) (cdr msg))
                                     (declare (ignore col))
                                     str)))))
    (second res)))

(defun get-predicate-name (ty-name)
  (let* ((query `acl2::(let ((defdata::wrld (w state)))
                         (defdata::predicate-name ',acl2s-high-level-interface::ty-name)))
         (res (acl2s-compute query)))
    (if (car res)
        (error "Failed to get the predicate name for type ~a" ty-name)
      (second res))))

(defun get-aliased-defdata-recognizer (name)
  (let* ((query `acl2s::(defdata::is-type-predicate-current ',acl2s-high-level-interface::name (w state)))
         (res (acl2s-compute query)))
    (when (and (not (car res)) (second res))
      (get-predicate-name (second res)))))

;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT

(in-package :z3)

;; TODO: integrate defdata's types where possible
;; e.g. automatically convert defdatas into "equivalent" Z3 sorts
;; but a fair amount of work is needed here to convert back and forth between z3 values and defdata values.

(defun make-var-decls (decls context)
  "Translate a user-provided list of variable and function
declarations into a variable sort alist for internal use."
  (loop for (var ty) on decls by #'cddr
        unless (and (consp ty) (equal (car ty) :fn))
        collect (cons var (make-instance 'z3-sort
                                         :handle (get-sort ty context)
                                         :context context))))

;;(make-var-decls '(x :int y :bool) *default-context*)

(defun make-fn-decls (decls context)
  "Translate a user-provided list of variable and function
declarations into a function declaration alist for internal use."
  (loop for (var ty) on decls by #'cddr
        when (and (consp ty) (equal (car ty) :fn))
        collect (list var (make-fn-decl var (second ty) (third ty) context) ty)))

;; TODO: we may want to use z3-mk-fresh-func-decl to avoid name
;; clashes with builtin functions. This would also require changes to
;; the model translation code.
(declaim (ftype (function (symbol list (or symbol cons) context) (values func-decl &optional)) make-fn-decl))
(defun make-fn-decl (name domain range context)
  "Given a name, a list of domain sort specifiers, and a range sort
specifier, create an uninterpreted func-decl with that name and
signature."
  (with-foreign-array (domain-sorts-array z3-c-types::Z3_sort domain :elt-fn #'(lambda (arg) (get-sort arg context)))
                      (make-instance 'func-decl
                                     :handle (z3-mk-func-decl context
                                                              (z3-mk-string-symbol context (symbol-name name))
                                                              (length domain)
                                                              domain-sorts-array
                                                              (get-sort range context))
                                     :context context)))

(cffi:defcallback error-handler :void ((ctx z3-c-types:Z3_context) (error-code z3-c-types:Z3_error_code))
  (match error-code
    (:OK (error "Z3: error handler called with error code OK - should not occur."))
    (:SORT_ERROR (error "Z3: tried to build an AST that is not well-sorted"))
    (:IOB (error "Z3: index out of bounds"))
    (:INVALID_ARG (error "Z3: Invalid argument was provided"))
    (:PARSER_ERROR (error "Z3: An error occurred when parsing a string or file: ~a" (z3-get-error-msg ctx error-code)))
    (:NO_PARSER (error "Z3: parser output is not available"))
    (:INVALID_PATTERN (error "Z3: invalid pattern used to build a quantifier"))
    (:MEMOUT_FAIL (error "Z3: unable to allocate memory"))
    (:FILE_ACCESS_ERROR (error "Z3: unable to access file"))
    (:INTERNAL_FATAL (error "Z3: internal error occurred"))
    (:INVALID_USAGE (error "Z3: API call is invalid in the current state: ~a" (z3-get-error-msg ctx error-code)))
    (:DEC_REF_ERROR (error "Z3: Tried to decrement the reference counter of an AST that was deleted or the reference counter was not initialized with Z3_inc_ref."))
    (:EXCEPTION (error "Z3: An exception occurred: ~a" (z3-get-error-msg ctx error-code)))
    (otherwise (error "Z3: an unknown error occurred with code ~S" error-code))))

(defun solver-init ()
  "Initialize the Z3 interface with a context and a solver."
  (setf *default-context* (make-instance 'context))
  (z3-set-error-handler *default-context* (cffi:callback error-handler))
  (setf *default-solver* (make-simple-solver *default-context*)))

(defgeneric solver-push-fn (solver)
  (:method ((solver solver))
           (let ((ctx (get-context solver)))
             (push '() (solver-assertion-stack solver))
             (env-push (solver-env solver))
             (z3-solver-push ctx solver)))
  (:method ((solver optimizer))
           (let ((ctx (get-context solver)))
             (push '() (solver-assertion-stack solver))
             (env-push (solver-env solver))
             (z3-optimize-push ctx solver))))

(defun solver-push (&optional solver)
  "Create a new scope. This is useful for incremental solving."
  (solver-push-fn (or solver *default-solver*)))

(defgeneric solver-pop-fn (solver n)
  (:method ((solver solver) n)
           (let ((ctx (get-context solver)))
             (unless (<= n (z3-solver-get-num-scopes ctx solver))
               (error "You can't pop ~S level(s) - the solver is currently at level ~S" n (z3-solver-get-num-scopes ctx solver)))
             (loop for i below n
                   do (progn
                        (pop (solver-assertion-stack solver))
                        (env-pop (solver-env solver))))
             (z3-solver-pop ctx solver n)))
  (:method ((solver optimizer) n)
           (let ((ctx (get-context solver)))
             (loop for i below n
                   do (progn
                        (pop (solver-assertion-stack solver))
                        (env-pop (solver-env solver))
                        (z3-optimize-pop ctx solver))))))

(defun solver-pop (&key (solver nil) (n 1))
  "Pop one or more scopes off the Z3 stack. This essentially undoes
any Z3 declarations or assertions that occurred between the relevant
'push' operation and this 'pop' operation."
  (solver-pop-fn (or solver *default-solver*) n))

(defun solver-reset (&optional solver)
  "Reset the solver, removing any assertions and emptying the stack."
  (solver-reset-fn (or solver *default-solver*)))

(defgeneric solver-reset-fn (slv)
  (:method ((slv solver))
    (setf (solver-assertion-stack slv) '(()))
    (setf (solver-env slv) (make-instance 'environment-stack))
    (z3-solver-reset (get-context slv) slv))
  (:method ((slv optimizer))
    (error "Z3 does not provide C API support for resetting an optimizer.")))

(defun print-solver (&optional solver)
  (let* ((slv (or solver *default-solver*)))
    (terpri)
    (print-scopes slv)
    nil))

(defun print-scopes (solver)
  (let ((*print-case* :downcase))
    (loop for scope in (solver-assertion-stack solver)
          do (loop for assertion in scope
                   do (format t "~S~%" assertion)))))

;; Take in a set of var-specs (akin to what definec and property
;; allow) and translate into pairs of (var . ty)
;; A list of var-specs is something like:
;; `(x y :int z :bool w (:seq :int) p (:fn (:int) :string))`
;; This means that both x and y have sort :int, z has sort :bool, w
;; has sort (:seq :int), and p has the sort (:int) -> :string.
(defun process-var-specs (var-specs)
  (let ((res nil)
        (acc nil))
    (loop for elt in var-specs
          do (cond ((and (or (keywordp elt) (consp elt))
                         (consp acc))
                    (setf res (append (mapcar #'(lambda (n) (cons n elt)) acc) res))
                    (setf acc nil))
                   ((or (keywordp elt) (consp elt))
                    (error "Type ~a given without without any variables to apply it to!" elt))
                   (t (push elt acc))))
    (check-processed-var-specs res)
    res))

;; Check that no var occurs more than once in the given processed var
;; specs.
(defun check-processed-var-specs (processed-var-specs)
  (let ((ht (make-hash-table)))
    (loop for (var-name . nil) in processed-var-specs
          do (multiple-value-bind (entry exists?)
               (gethash var-name ht)
               (declare (ignore entry))
               (when exists?
                 (error "Variable ~a specified multiple times in the same assert form!" var-name))
               (setf (gethash var-name ht) t)))
    t))

;; Convert a type specifier to the appropriate Z3 value: a function
;; declaration (for function type specifiers) or a sort (for
;; non-function type specifiers).
(defun convert-type-spec (name ty context)
  (if (and (consp ty) (equal (car ty) :fn))
      (make-fn-decl name (second ty) (third ty) context)
    (make-instance 'z3-sort
                   :handle (get-sort ty context)
                   :context context)))

(defun setup-env (processed-var-specs env ctx)
  (loop for (name . ty) in processed-var-specs
        when (multiple-value-bind
               (existing-ty exists?)
               (env-get name env)
               (cond ((not exists?)
                      (env-set name (cons ty (convert-type-spec name ty ctx)) env)
                      name)
                     ;; We allow a variable to be specified again so
                     ;; long as the sort is exactly the same as
                     ;; before.
                     ((equal ty (car existing-ty)) nil)
                     (t (error "Variable ~a was previously specified with a different sort: ~a!" name (car existing-ty)))))
        collect it))

(defun declare-const-fn (name sort &optional solver)
  (let* ((slv (or solver *default-solver*))
         (ctx (get-context slv))
         (new-vars (setup-env `((,name . ,sort)) (solver-env slv) ctx)))
    (unless new-vars
      (warn "Variable ~a was already declared with sort ~a." name (env-get name (solver-env slv))))
    name))

(defmacro declare-const (name sort)
  "Declare a Z3 constant with the given name and sort."
  `(declare-const-fn ',name ',sort))

(defun declare-fun-fn (name param-sorts res-sort &optional solver)
  (let ((slv (or solver *default-solver*)))
    (if (endp param-sorts)
        (declare-const-fn name res-sort slv)
      (let* ((ctx (get-context slv))
             (new-vars (setup-env `((,name . (:fn ,param-sorts ,res-sort))) (solver-env slv) ctx)))
        (unless new-vars
          (warn "Variable ~a was already declared with sort ~a." name (env-get name (solver-env slv))))
        name))))

(defmacro declare-fun (name param-sorts res-sort)
  "Declare a Z3 function taking in parameters of the given sorts and
returning values of the given sort."
  (unless (listp param-sorts)
    (error "The second argument of declare-fun must be a list of parameter sorts."))
  `(declare-fun-fn ',name ',param-sorts ',res-sort))

(defun z3-assert-fn (var-specs stmt &optional solver)
  (let* ((slv (or solver *default-solver*))
         (ctx (get-context slv))
         (processed-var-specs (process-var-specs var-specs))
         (added-vars (setup-env processed-var-specs (solver-env slv) ctx)))
    ;; If an error occurs, revert the changes to the environment
    (handler-case
        (prog1
            (solver-assert slv (convert-to-ast stmt (solver-env slv) ctx))
          (push `(assert ,var-specs ,stmt) (car (solver-assertion-stack slv))))
      (error (c) (loop for name in added-vars do (env-remove name (solver-env slv))) (error c)))))

(defmacro z3-assert (var-specs &optional (stmt nil stmt-provided?) solver)
  "Assert that the given statement holds in Z3. Any free variable
occurring in the statement must be declared with its sort in
`var-specs`, or have been declared in a previous `z3-assert*`,
`declare-const`, or `declare-fun` that is still on the assertion
stack.`var-specs` may be omitted in the case where no variables need
to be declared."
  (if stmt-provided?
      `(z3-assert-fn ',var-specs ',stmt ,solver)
    `(z3-assert-fn nil ',var-specs ,solver)))

(defun z3-assert-soft-fn (var-specs stmt weight &optional solver)
  (let* ((slv (or solver *default-solver*))
         (ctx (get-context slv))
         (processed-var-specs (process-var-specs var-specs))
         (added-vars (setup-env processed-var-specs (solver-env slv) ctx)))
    ;; If an error occurs, revert the changes to the environment
    (handler-case
        (prog1
            (solver-assert-soft slv (convert-to-ast stmt (solver-env slv) ctx) weight)
          (push `(assert ,var-specs ,stmt) (car (solver-assertion-stack slv))))
      (error (c) (loop for name in added-vars do (env-remove name (solver-env slv))) (error c)))))

(defmacro z3-assert-soft (var-specs stmt weight &optional solver)
  "Assert that the given statement holds in Z3. Any free variable
occurring in the statement must be declared with its sort in
`var-specs`, or have been declared in a previous `z3-assert*`,
`declare-const`, or `declare-fun` that is still on the assertion stack.
`weight` should be a positive number representing the penalty for
violating this constraint."
  `(z3-assert-soft-fn ',var-specs ',stmt ',weight ,solver))

(defun z3-optimize-minimize-fn (var-specs stmt &optional solver)
  (let* ((slv (or solver *default-solver*))
         (ctx (get-context slv))
         (processed-var-specs (process-var-specs var-specs))
         (added-vars (setup-env processed-var-specs (solver-env slv) ctx)))
    ;; If an error occurs, revert the changes to the environment
    (handler-case
        (prog1
            (z3-optimize-minimize ctx slv (convert-to-ast stmt (solver-env slv) ctx))
          (push `(minimize ,var-specs ,stmt) (car (solver-assertion-stack slv))))
      (error (c) (loop for name in added-vars do (env-remove name (solver-env slv))) (error c)))))

(defmacro optimize-minimize (var-specs stmt &optional solver)
  "Add an objective function to be minimized."
  `(z3-optimize-minimize-fn ',var-specs ',stmt ,solver))

(defun z3-optimize-maximize-fn (var-specs stmt &optional solver)
  (let* ((slv (or solver *default-solver*))
         (ctx (get-context slv))
         (processed-var-specs (process-var-specs var-specs))
         (added-vars (setup-env processed-var-specs (solver-env slv) ctx)))
    ;; If an error occurs, revert the changes to the environment
    (handler-case
        (prog1
            (z3-optimize-maximize ctx slv (convert-to-ast stmt (solver-env slv) ctx))
          (push `(maximize ,var-specs ,stmt) (car (solver-assertion-stack slv))))
      (error (c) (loop for name in added-vars do (env-remove name (solver-env slv))) (error c)))))

(defmacro optimize-maximize (var-specs stmt &optional solver)
  "Add an objective function to be maximized."
  `(z3-optimize-maximize-fn ',var-specs ',stmt ,solver))

(defgeneric get-model-fn (solver)
  (:method ((solver solver))
           (let ((ctx (get-context solver)))
             (make-instance 'model
                            :handle (z3-solver-get-model ctx solver)
                            :context ctx)))
  (:method ((solver optimizer))
           (let ((ctx (get-context solver)))
             (make-instance 'model
                            :handle (z3-optimize-get-model ctx solver)
                            :context ctx))))

(defun get-model (&optional solver)
  "Get the Z3 model object for the last `check-sat` call. If that call
indicated that Z3 determined satisfiability, then the model will
contain a satisfying assignment for the assertions in the global
assertion stack.  If `check-sat` determined `:UNKNOWN` then a model
may be available, but the provided assignment may not satisfy the
assertions on the stack. Will invoke the error handler if no model is
available."
  ;; TODO: in the unknown case we may want to get the model and see if
  ;; the assignment satisfies the assertions.
  (get-model-fn (or solver *default-solver*)))

(defun get-model-as-assignment (&optional solver)
  "If Z3 has determined that the global assertion stack is satisfiable,
get a satisfying assignment. Returns a (possibly empty) list of
bindings corresponding to the model that Z3 generated. Will invoke the
error handler if no model is available. If check-sat determined
`:UNKNOWN` then a model may be available, but the provided assignment
may not satisfy the assertions on the stack. Will invoke the error
handler if no model is available."
  (let* ((solver (or solver *default-solver*))
         (model (get-model solver)))
    (append (model-constants model)
            (model-functions model))))

(defgeneric solver-check (solver)
  (:method ((solver solver)) (z3-solver-check (get-context solver) solver))
  (:method ((solver optimizer)) (z3-optimize-check (get-context solver) solver 0 (cffi:null-pointer))))

(declaim (ftype (function (&optional (or solver optimizer)) (values (member :sat :unsat :unknown) &optional)) check-sat))
(defun check-sat (&optional solver)
  "Ask Z3 to check satisfiability of the global assertion stack.
Returns either `:SAT`, `:UNSAT` or `:UNKNOWN`."
  (let ((slv (or solver *default-solver*)))
    (match (solver-check slv)
      (:L_TRUE :SAT) ;; assertions are satisfiable (a model may be generated)
      (:L_FALSE :UNSAT) ;; assertions are not satisfiable (a proof may be generated)
      (:L_UNDEF :UNKNOWN) ;; get_model may succeed but the model may not satisfy the assertions
      (otherwise (error "Unexpected result of solver-check: ~a" (solver-check slv))))))

(defun eval-under-model-fn (stmt model solver completion)
  (let* ((ctx (get-context solver))
         (ast (convert-to-ast stmt (solver-env solver) ctx)))
    (cffi:with-foreign-object (res-ptr 'z3-c-types::Z3_ast)
      (let ((success? (z3-model-eval ctx model ast completion res-ptr)))
        (if success?
            (ast-to-value (make-instance 'ast :handle (cffi:mem-ref res-ptr 'z3-c-types::Z3_ast) :context ctx) ctx)
            (error "Evaluating the given statement under the given model failed for some reason."))))))

(defmacro eval-under-model (stmt &optional model solver (completion t))
  "Evaluate the given statement in the given model, under Z3 semantics.
If no model is provided, will use the model produced by `get-model`.
If no solver is provided, will use `*default-solver*`."
  `(eval-under-model-fn ',stmt (or ,model (get-model)) (or ,solver *default-solver*) ,completion))

;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(import 'z3-c-types::Z3_ast)

(defun env-has-fn? (name env)
  (multiple-value-bind
    (fn-entry exists?)
    (env-get name env)
    (and exists? (consp (car fn-entry)) (equal (caar fn-entry) :fn))))

(defun make-fn-call (name args ctx env)
  (multiple-value-bind
    (fn-entry exists?)
    (env-get name env)
    (unless (and exists? (consp (car fn-entry)) (equal (caar fn-entry) :fn))
      (error "No function with name ~S is known" name))
    (let* ((decl (cdr fn-entry))
           (arg-sorts-debug (second (car fn-entry))))
           ;;(return-sort-debug (third (car fn-entry))))
      (unless (equal (length arg-sorts-debug) (length args)) (error "Incorrect number of arguments given for function ~S of type ~S" name (car fn-entry)))
      (with-foreign-array (array z3-c-types::Z3_ast args :elt-fn #'(lambda (arg) (convert-to-ast-fn ctx arg env)))
                          (z3-mk-app ctx decl (length args) array)))))

(defun convert-to-ast-fn (context stmt env)
  (match stmt
         ((or t (sym-name true)) (z3-mk-true context))
         ((or nil (sym-name false)) (z3-mk-false context))
         ((satisfies integerp) (z3-mk-numeral context (write-to-string stmt) (z3-mk-int-sort context)))
         ((type symbol)
          (multiple-value-bind
            (ty-entry exists?)
            (env-get stmt env)
            (if exists?
                (z3-mk-const context (z3-mk-string-symbol context (symbol-name stmt)) (cdr ty-entry))
              (error "You must provide types for all variables. You did not for the variable ~S." stmt))))
         ((type string) (z3-mk-string context stmt))
         ((list (sym-name unescaped-string) str)
          (assert (stringp str))
          (z3-mk-lstring context (length str) str))
         ((list (sym-name enumval) name val)
          (enum-value-to-ast name val context))
         ((list* (sym-name tuple-val) tuple-name field-values)
          (construct-tuple-fn tuple-name (mapcar (lambda (value) (convert-to-ast-fn context value env)) field-values) context))
         ((list (sym-name tuple-get) tuple-name field-name value)
          (construct-tuple-field-accessor-fn tuple-name field-name
                                             (convert-to-ast-fn context value env) context))
         ((list* (sym-name bv) args)
          (let ((args
                 (cond ((every #'(lambda (arg) (typep arg 'boolean)) args)
                        args)
                       ((every #'(lambda (arg) (or (eql arg 0) (eql arg 1))) args)
                        (mapcar #'(lambda (arg) (= arg 1)) args))
                       (t (error "You must provide either a list of booleans or a list of (0,1)s to bv.")))))
            (with-foreign-array (array :bool args)
                                (z3-mk-bv-numeral context (length args) array))))
         ((list* (sym-name seq) args)
          (assert (plusp (length args)))
          (with-foreign-array (array z3-c-types::Z3_ast args
                                     :elt-fn #'(lambda (arg) (z3-mk-seq-unit context (convert-to-ast-fn context arg env))))
                              (z3-mk-seq-concat context (length args) array)))
         ((list (sym-name seq.unit) x)
          (z3-mk-seq-unit context (convert-to-ast-fn context x env)))
         ((list (sym-name re.empty) sort)
          (z3-mk-re-empty context (get-sort sort context)))
         ((list (sym-name re.full) sort)
          (z3-mk-re-full context (get-sort sort context)))
         ((list* (sym-name set) sort args)
          (mk-set (get-sort sort context) args context env))
         ((list (sym-name forall) bound-vars body)
          (mk-quantifier t bound-vars body context env))
         ((list (sym-name exists) bound-vars body)
          (mk-quantifier nil bound-vars body context env))
         ((type list) (convert-funccall-to-ast context stmt env))
         (otherwise (error "Value ~S is of an unsupported type." stmt))))

;; Given a list of bound variables (e.g. a list consisting of
;; variables, each followed by a type), return (values consts new-env)
;; where:
;; - consts is a list containing a Z3 constant for each bound variable
;; - new-env the given environment env after pushing a new layer and adding a mapping for each bound variable to its Z3 sort
(defun process-bound-vars (bound-vars context env)
  (let ((new-env (env-flat-copy env))
        (processed-var-specs (process-var-specs bound-vars)))
    (check-processed-var-specs processed-var-specs)
    ;; Remove any occurrences of bound-vars from the new copy of the
    ;; environment
    (loop for (name . nil) in processed-var-specs
          do (env-remove-top name new-env))
    ;; Now we can set up the environment as usual
    (setup-env processed-var-specs new-env context)
    ;; Finally we need to produce a const for each bound var. The
    ;; environment already contains the appropriate sort, so we'll
    ;; just pull the sort from there.
    (let ((consts (loop for (name . nil) in processed-var-specs
                        collect (let ((sort (cdr (env-get name new-env))))
                                  (z3-mk-const context (z3-mk-string-symbol context (symbol-name name)) sort)))))
    (values consts new-env))))

;; Make a quantifier, given its body and a list of bound variables.
(defun mk-quantifier (is-forall bound-vars body context env)
  ;; create a constant for each bound variable
  (multiple-value-bind
    (bound-var-consts bound-env)
    (process-bound-vars bound-vars context env)
    ;; move the constants into a C array
    (with-foreign-array (bound-vars z3-c-types::Z3_ast bound-var-consts)
                        (z3-mk-quantifier-const context
                                                is-forall
                                                0 ;; weight
                                                (length bound-var-consts)
                                                bound-vars
                                                0 ;; no patterns
                                                (cffi:null-pointer)
                                                ;; make sure we use bound-env, as it allows access
                                                ;; to the variables quantified over.
                                                (convert-to-ast-fn context body bound-env)))))

(defun mk-set (sort values ctx env)
  (if (endp values)
      (z3-mk-empty-set ctx sort)
    (z3-mk-set-add ctx
                   (mk-set sort (cdr values) ctx env)
                   (convert-to-ast-fn ctx (car values) env))))

(defun convert-to-ast (stmt &optional (env (make-instance 'environment-stack)) context)
  "Convert a Common Lisp S-expression into a Z3 AST, with respect to
the given environment."
  (let ((ctx (or context *default-context*)))
    (make-instance 'ast
                   :handle (convert-to-ast-fn ctx stmt env)
                   :context ctx)))

;; A partial list of built-in functions.
;; Each entry should have the following form:
;; (<name/loname> &key :arity :ctor)
;; - <name/loname> is either a symbol or a nonempty list of symbols
;;   corresponding to the symbols that should be translated into this
;;   operator. If :ctor is not provided, the first name is used to
;;   generate the name of the CFFI'ed Z3 function to use to construct
;;   an application AST for this operator, by appending Z3-MK- to the
;;   name and replacing any periods with dashes.
;; - If :arity is provided, it should either be a positive integer
;;   describing the number of arguments this operator takes, or -
;;   indicating that this operator has arbitrary arity >=1.
;; - If :arity is -, one can also provide :enforce-arity and a number.
;;   This will call the underlying Z3 constructor as though it is
;;   designed for arbitrary arity, but will check that the arity of any
;;   given call is equal to the given :enforce-arity value.
;; - If :ctor is provided, it should be a symbol corresponding to the
;;   CFFI'ed Z3 function that constructs an application AST for this
;;   operator.
;; These operator specs will be used to generate lambdas for each
;; operator that take in an S-expression of the appropriate form,
;; convert all arguments into Z3 ASTs recursively, and apply the
;; relevant constructor to those arguments.
(defvar *builtin-ops*
  '(;; core theory
    ;; true special
    ;; false special
    (not :arity 1)
    ((implies =>) :arity 2)
    (and :arity -)
    (or :arity -)
    (xor :arity 2)
    ((= == equal) :ctor z3-mk-eq :arity 2)
    (distinct :arity -)
    ((ite if) :arity 3)
    ;; end of core theory
    (iff :arity 2)
    (+ :ctor z3-mk-add :arity -)
    (- :ctor z3-mk-sub :arity -)
    ;; note that we special-case unary - by adding a case for it in convert-funccall-to-ast.
    (* :ctor z3-mk-mul :arity -)
    (/ :ctor z3-mk-div :arity 2)
    ;; div special
    (mod :arity 2)
    (rem :arity 2)
    (power :arity 2)
    (to_real :ctor z3-mk-int2real :arity 1)
    (to_int :ctor z3-mk-real2int :arity 1)
    ;;(divides :arity 2)
    (< :ctor z3-mk-lt :arity 2)
    (<= :ctor z3-mk-le :arity 2)
    (> :ctor z3-mk-gt :arity 2)
    (>= :ctor z3-mk-ge :arity 2)
    (is_int :arity 1)
    ;; Bitvector functions
    (bvnot :arity 1)
    (bvredand :arity 1)
    (bvredor :arity 1)
    (bvand :arity 2)
    (bvor :arity 2)
    (bvxor :arity 2)
    (bvnand :arity 2)
    (bvnor :arity 2)
    (bvxnor :arity 2)
    (bvneg :arity 1)
    (bvadd :arity 2)
    (bvsub :arity 2)
    (bvmul :arity 2)
    (bvudiv :arity 2)
    (bvsdiv :arity 2)
    (bvurem :arity 2)
    (bvsmod :arity 2)
    (bvult :arity 2)
    (bvslt :arity 2)
    (bvule :arity 2)
    (bvsle :arity 2)
    (bvugt :arity 2)
    (bvsgt :arity 2)
    (bvuge :arity 2)
    (bvsge :arity 2)
    (concat :arity 2)
    ;; extract special
    ;; sign-ext special
    ;; zero-ext special
    ;; repeat special
    (bvshl :arity 2)
    (bvlshr :arity 2)
    (bvashr :arity 2)
    ;; int2bv special
    ;; bv2int special
    ;;; Array functions
    (select :arity 2)
    ;; select_n special
    (store :arity 3)
    ;; store_n special
    ;; const_array special
    ;; map special
    (array-default :arity 1)
    ;; as_array special
    ;;(set-has-size :arity 2) deprecated
    ;;; Set functions
    ;; mk-empty-set special
    ;; mk-full-set special
    ;;(set-add :arity 2)
    ;;(set-del :arity 2)
    ;; (as set.empty <sort>) special
    ;; (as set.universe <sort>) special
    ;; set.singleton special
    ;; set.insert special
    (set.union :arity - :enforce-arity 2)
    (set.inter :ctor z3-mk-set-intersect :arity - :enforce-arity 2)
    (set.minus :ctor z3-mk-set-difference :arity 2)
    (set.complement :arity 1)
    (set.member :arity 2)
    (set.subset :arity 2)
    (array-ext :arity 2)
    ;;; Sequence functions
    ;; seq_empty special
    (seq.unit :arity 1)
    ((seq.++ str.++) :ctor z3-mk-seq-concat :arity -)
    ((seq.prefixof str.prefixof) :ctor z3-mk-seq-prefix :arity 2)
    ((seq.contains str.contains) :arity 2)
    (str.< :ctor z3-mk-str-lt :arity 2)
    (str.<= :ctor z3-mk-str-le :arity 2)
    (seq.extract :arity 3)
    ((seq.replace str.replace) :arity 3)
    ((seq.at str.at) :arity 2)
    (seq.nth :arity 2)
    ((seq.len str.len) :ctor z3-mk-seq-length :arity 1)
    ((seq.indexof str.indexof) :ctor z3-mk-seq-index :arity 3)
    (seq-last-index :arity 2)
    (str.to.int :arity 1)
    (int.to.str :arity 1)
    ;;; Regular expression functions
    ((seq-to-re seq.to.re) :arity 1)
    ((seq-in-re seq.in.re) :arity 2)
    (re.+ :ctor z3-mk-re-plus :arity 1)
    (re.* :ctor z3-mk-re-star :arity 1)
    (re.opt :ctor z3-mk-re-option :arity 1)
    (re.union :arity -)
    (re.++ :ctor z3-mk-re-concat :arity -)
    (re.range :arity 2)
    ;; re-loop special
    (re.inter :ctor z3-mk-re-intersect :arity -)
    (re.comp :ctor z3-mk-re-complement :arity 1)
    ((re.empty re.none) :arity 1)
    ((re.full re.all) :arity 1)
    ;;; Special relations
    ;; these are all special, and not supported
    ;; linear order
    ;; partial order
    ;; piecewise linear order
    ;; tree order
    ;; transitive closure
    ))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defmacro mk-op-fn (op)
  (let* ((names (if (consp (car op)) (car op) (list (car op))))
         (name (car names))
         (z3-name (or (get-key :ctor (cdr op))
                      (intern (concatenate 'string "Z3-MK-" (substitute #\- #\_ (substitute #\- #\. (symbol-name name)))) :z3)))
         (arity (get-key :arity (cdr op)))
         (enforce-arity (get-key :enforce-arity (cdr op))))
    (if (equal arity '-)
        `(lambda (context env op &rest args)
           ,@(when enforce-arity
               `((when (not (equal (length args) ,enforce-arity))
                   (error "The function ~S must be called with exactly ~a arguments, but it is not in this case.~%Error in statement ~a" op ,enforce-arity (cons op args)))))
           (when (endp args)
             (error "The function ~S must be called with at least one argument." op))
           (with-foreign-array (array
                                z3-c-types::Z3_ast
                                args
                                :elt-fn #'(lambda (arg) (convert-to-ast-fn context arg env)))
             (,z3-name context (length args) array)))
      (let ((arg-names (loop for i below arity collect (gensym))))
        `(lambda (context env op ,@arg-names)
           (declare (ignore op))
           (,z3-name context . ,(mapcar (lambda (arg-name) `(convert-to-ast-fn context ,arg-name env)) arg-names)))))))

(defvar *ops-hash* (make-hash-table :test 'equal))
(loop for op in *builtin-ops*
      for names = (if (consp (car op)) (car op) (list (car op)))
      do (loop for name in names
               do (setf (gethash (symbol-name name) *ops-hash*)
                        (eval `(mk-op-fn ,op)))))

;; Handle (as <stmt> <sort-spec>), given stmt and sort-spec
(defun convert-as-to-ast (context stmt sort-spec env)
  (match stmt
    ((sym-name seq.empty)
     (unless (and (consp sort-spec) (sort-names-match? (car sort-spec) :seq))
       (error "You must provide a sequence sort when using (as seq.empty <sort>)"))
     (z3-mk-seq-empty context (get-sort sort-spec context)))
    ((sym-name set.empty)
     (unless (and (consp sort-spec) (sort-names-match? (car sort-spec) :set))
       (error "You must provide a set sort when using (as set.empty <sort>)"))
     (z3-mk-empty-set context (get-sort (second sort-spec) context)))
    ((sym-name set.universe)
     (unless (and (consp sort-spec) (sort-names-match? (car sort-spec) :set))
       (error "You must provide a set sort when using (as set.universe <sort>)"))
     (z3-mk-full-set context (get-sort (second sort-spec) context)))
    (otherwise (error "Unable to convert (as ~a ~a) to an AST!" stmt sort-spec))))

(defun convert-funccall-to-ast (context stmt env)
  (match stmt
         ((list (sym-name !=) x y)
          (convert-funccall-to-ast context `(not (equal ,x ,y)) env))
         ;; Unary subtraction, binary is taken care of thru *builtin-ops*
         ((list (sym-name -) arg)
          (z3-mk-unary-minus context (convert-to-ast-fn context arg env)))
         ((list (sym-name div) x y)
          (let* ((x-ast (convert-to-ast-fn context x env))
                 (y-ast (convert-to-ast-fn context y env))
                 (x-ast-sort-kind (z3-get-sort-kind context (z3-get-sort context x-ast)))
                 (y-ast-sort-kind (z3-get-sort-kind context (z3-get-sort context y-ast))))
            (unless (and (equal x-ast-sort-kind :INT_SORT)
                         (equal y-ast-sort-kind :INT_SORT))
              (error "Arguments to div should have the same sort!~%This is not the case for statement ~a, where the arguments have sort kinds ~a and ~a." stmt x-ast-sort-kind y-ast-sort-kind))
            (z3-mk-div context x-ast y-ast)))
         ((list (list (sym-name _) (sym-name extract) hi lo) x)
          (unless (and (integerp hi) (integerp lo))
            (error "(_ extract hi lo) requires that hi and lo are both integers!~%This is not the case in statement ~a" stmt))
          (z3-mk-extract context
                         hi
                         lo
                         (convert-to-ast-fn context x env)))
         ((list (list (sym-name _) (sym-name sign_extend) len) x)
          (z3-mk-sign-ext context
                          len
                          (convert-to-ast-fn context x env)))
         ((list (list (sym-name _) (sym-name zero_extend) len) x)
          (z3-mk-zero-ext context
                          len
                          (convert-to-ast-fn context x env)))
         ((list (list (sym-name _) (sym-name repeat) ntimes) x)
          (unless (integerp ntimes)
            (error "(_ repeat ntimes) requires that ntimes is an integer!~%This is not the case in statement ~a" stmt))
          (z3-mk-repeat context
                        ntimes
                        (convert-to-ast-fn context x env)))
         ((list (list (sym-name _) (sym-name int2bv) nbits) x)
          (unless (integerp nbits)
            (error "(_ int2bv nbits) requires that nbits is an integer!~%This is not the case in statement ~a" stmt))
          (z3-mk-int2bv context
                        nbits
                        (convert-to-ast-fn context x env)))
         ((list (sym-name bv2int) x signed?)
          (z3-mk-bv2int context
                        (convert-to-ast-fn context x env)
                        signed?))
         ((list (or (sym-name re-loop)
                    (sym-name re.loop))
                r lo hi)
          (assert (and (numberp lo) (>= lo 0)))
          (assert (and (numberp hi) (>= hi 0)))
          (z3-mk-re-loop context
                         (convert-to-ast-fn context r env)
                         lo hi))
         ;; pseudoboolean constraints
         ((list* (list (sym-name _) (sym-name at-most) k) args)
          (unless (integerp k)
            (error "(_ at-most x) expects that x is an integer."))
          (with-foreign-array (array z3-c-types::Z3_ast args :elt-fn #'(lambda (arg) (convert-to-ast-fn context arg env)))
            (z3-mk-atmost context (length args) array k)))
         ((list* (list (sym-name _) (sym-name at-least) k) args)
          (unless (integerp k)
            (error "(_ at-least x) expects that x is an integer."))
          (with-foreign-array (array z3-c-types::Z3_ast args :elt-fn #'(lambda (arg) (convert-to-ast-fn context arg env)))
            (z3-mk-atleast context (length args) array k)))
         ((list (sym-name set.singleton) x)
          (let ((x-ast (convert-to-ast-fn context x env)))
            (z3-mk-set-add context (z3-mk-empty-set context (z3-get-sort context x-ast)) x-ast)))
         ((list* (sym-name set.insert) args)
          (unless (and (consp args) (consp (cdr args)))
            (error "set.insert requires at least two arguments!"))
          (let* ((arg-asts (mapcar #'(lambda (arg) (convert-to-ast-fn context arg env)) args))
                 (set-ast (convert-to-ast-fn context (car (last args)) env)))
            (loop for arg-ast in (butlast arg-asts)
                  do (setf set-ast (z3-mk-set-add context set-ast arg-ast)))
            set-ast))
         ((list (sym-name as) as-stmt sort-spec)
          (convert-as-to-ast context as-stmt sort-spec env))
         ((list* op args)
          (multiple-value-bind (op-fn exists?)
              (gethash (symbol-name op) *ops-hash*)
              (cond (exists? (apply op-fn context env op args))
                    ((env-has-fn? op env) (make-fn-call op args context env))
                    (t (error "The expression ~S looks like a function call, but we don't know how to handle the function with name ~a. You may be trying to use an operator that we do not yet support, or you are trying to call an uninterpreted function with a name that we don't know. Please check the spelling of the operator name." stmt op)))))
         (otherwise (error "We currently do not support translation of the following expression into Z3.~%~S" stmt))))

(defun app-ast-args-to-list (ast ctx)
  "Get the arguments of an application AST as a list of Z3 AST values."
  (assert (equal (z3-get-ast-kind ctx ast) :app_ast))
  (loop for i below (z3-get-app-num-args ctx ast)
        collect (z3-get-app-arg ctx ast i)))

(defun seq-ast-to-value (ast ctx)
  "Translate a sequence AST into a Lisp list value"
  (assert (equal (z3-get-ast-kind ctx ast) :app_ast))
  (assert (equal (z3-get-sort-kind ctx (z3-get-sort ctx ast)) :seq_sort))
  (let* ((decl (z3-get-app-decl ctx ast))
         (decl-kind (z3-get-decl-kind ctx decl)))
    (match decl-kind
           (:OP_SEQ_EMPTY nil)
           (:OP_SEQ_UNIT (list (ast-to-value (z3-get-app-arg ctx ast 0) ctx)))
           (:OP_SEQ_CONCAT
            (loop for arg in (app-ast-args-to-list ast ctx)
                  append (seq-ast-to-value arg ctx)))
           ;; TODO: do something better here. For example, this AST
           ;; may represent a string variable.
           (:OP_UNINTERPRETED
            (warn "Handling of OP_UNINTERPRETED is currently a work in progress.")
            (z3-ast-to-string ctx ast))
           (otherwise (error "Unsupported operation when trying to convert sequence AST to value: ~S" decl-kind)))))

(defun array-ast-to-value (ast ctx)
  "Translate an array AST into a Lisp alist value"
  (assert (equal (z3-get-ast-kind ctx ast) :app_ast))
  (assert (equal (z3-get-sort-kind ctx (z3-get-sort ctx ast)) :array_sort))
  (let* ((decl (z3-get-app-decl ctx ast))
         (decl-kind (z3-get-decl-kind ctx decl)))
    (match decl-kind
      (:OP_STORE (cons (cons (ast-to-value (z3-get-app-arg ctx ast 1) ctx)
                             (ast-to-value (z3-get-app-arg ctx ast 2) ctx))
                       (array-ast-to-value (z3-get-app-arg ctx ast 0) ctx)))
      (:OP_CONST_ARRAY `((:default . ,(ast-to-value (z3-get-app-arg ctx ast 0) ctx))))
      ;;(:OP_ARRAY_MAP)
      (otherwise (error "Unsupported operation when trying to convert array AST to value: ~S" decl-kind)))))


;; TODO: this is an experimental feature, don't rely on this switch
;; existing.
(defvar *STRING-REP* :string
  "EXPERIMENTAL.
Controls how strings are represented when converting from the Z3 model
into lisp. Currently there are two modes: `:string` (the default) and
`:list` (convert into list of uint8 values)")

(defun get-lstring (context ast)
  (assert (z3-is-string context ast))
  (cffi:with-foreign-object
   (size-ptr :uint 1)
   (let* ((str-ptr (z3-get-lstring context ast size-ptr))
          (size (cffi:mem-ref size-ptr :uint))
          (res-vec (make-array (list size) :element-type '(unsigned-byte 8))))
     (loop for i below size
           do (setf (aref res-vec i) (cffi:mem-aref str-ptr :unsigned-char i)))
     (match *STRING-REP*
            (:string (octets-to-string res-vec :external-format :UTF-8))
            (:list (coerce res-vec 'list))
            (otherwise (error "Unknown string representation mode ~S" *STRING-REP*))))))

(defparameter *ALGEBRAIC-NUMBER-CONVERT-MODE* :float
  "Controls how algebraic numbers are converted to Lisp values. Default
is `:float`.

 - `:float` will produce a floating-point approximation of the algebraic
   number.
 - `:decimal` will produce a string corresponding to a floating-point
   approximation of the algebraic number.
 - `:root` will produce a string corresponding to the polynomial root
   representation of the algebraic number.
 - `:agnum` will leave the algebraic number as an algebraic-number type.

Note that `:float` and `:precision` will first have Z3 produce a
string representation of the number with less than or equal to
`*ALGEBRAIC-NUMBER-CONVERT-DECIMAL-PRECISION*` decimal places. That
string representation will then be turned into a floating point
value. For very small or very large values, the default value may be
insufficient, so in such cases one is advised to change the precision
value.")

(defparameter *ALGEBRAIC-NUMBER-CONVERT-DECIMAL-PRECISION* 15
  "The number of decimal places to include when converting algebraic
numbers to floats.")

;; For now, we simply turn the algebraic number into a double. It would
;; be more convenient to use z3-get-numeral-double, but this seems to
;; produce an invalid argument error whenever the value wouldn't fit
;; precisely in a double. This is fair behavior, but probably not what
;; we want here (as the value may be irrational).
(defmethod algebraic-number-to-float ((obj algebraic-number))
  (with-slots (handle context) obj
    (let* ((res (z3-get-numeral-decimal-string context handle *ALGEBRAIC-NUMBER-CONVERT-DECIMAL-PRECISION*))
           (len (length res)))
      (values (parse-float::parse-float res :end (- len 2))))))

(defun algebraic-number-to-value (val)
  (ecase *ALGEBRAIC-NUMBER-CONVERT-MODE*
    (:float (algebraic-number-to-float val))
    (:decimal
     (with-slots (handle context) val
       (z3-get-numeral-decimal-string context handle *ALGEBRAIC-NUMBER-CONVERT-DECIMAL-PRECISION*)))
    (:root
     (with-slots (handle context) val
       (z3-ast-to-string context handle)))
    (:agnum val)))

(defun assert-app-decl-kind (ctx ast kind)
  (assert (equal (z3-get-ast-kind ctx ast) :app_ast))
  (let* ((decl (z3-get-app-decl ctx (z3-to-app ctx ast)))
         (decl-kind (z3-get-decl-kind ctx decl)))
    (assert (equal decl-kind kind))))

(defun app-ast-to-value (ast ctx)
  (assert (equal (z3-get-ast-kind ctx ast) :app_ast))
  (let* ((decl (z3-get-app-decl ctx (z3-to-app ctx ast))))
    (match (z3-get-decl-kind ctx decl)
      (:OP_TRUE t)
      (:OP_FALSE nil)
      (:OP_DT_CONSTRUCTOR
       (let* ((sort (z3-get-sort ctx ast)))
         (cond ((enum-sort? sort ctx) (get-enum-value sort decl ctx))
               ((tuple-sort? sort ctx)
                (list 'quote (cons (cons :type (sort-name sort ctx))
                                   (loop for field in (get-tuple-fields sort (z3-to-app ctx ast) ctx)
                                         collect (cons (car field) (ast-to-value (cdr field) ctx))))))
               (t (error "We don't support custom datatypes like ~S yet." (sort-name sort ctx))))))
      ;; TODO: do something better here. For example, this AST
      ;; may represent a string variable.
      (:OP_UNINTERPRETED
       (warn "Handling of OP_UNINTERPRETED is currently a work in progress.")
       (z3-ast-to-string ctx ast))
      ((or :OP_SEQ_CONCAT :OP_SEQ_UNIT :OP_SEQ_EMPTY)
       ;; Sometimes string literal values are represented using
       ;; concatenation/sequence operations for some reason. An
       ;; example of this is when the string is an argument in the
       ;; function map for an uninterpreted function; see the example
       ;; from examples/uninterpreted-fns.lisp using 3 functions, f g
       ;; and h.
       (if (z3-is-string-sort ctx (z3-get-sort ctx ast))
           (coerce (seq-ast-to-value ast ctx) 'string)
         (seq-ast-to-value ast ctx)))
      ((or :OP_STORE :OP_CONST_ARRAY :OP_ARRAY_MAP)
       (array-ast-to-value ast ctx))
      (:OP_ADD
       (cons '+ (mapcar #'(lambda (arg) (ast-to-value arg ctx)) (app-ast-args-to-list ast ctx))))
      (:OP_ITE
       (cons 'if (mapcar #'(lambda (arg) (ast-to-value arg ctx)) (app-ast-args-to-list ast ctx))))
      (:OP_EQ
       (cons '= (mapcar #'(lambda (arg) (ast-to-value arg ctx)) (app-ast-args-to-list ast ctx))))
      (:OP_OR
       (cons 'or (mapcar #'(lambda (arg) (ast-to-value arg ctx)) (app-ast-args-to-list ast ctx))))
      ;; Algebraic number
      (:OP_AGNUM
       (algebraic-number-to-value (make-algebraic-number ctx ast)))
      ;;(:OP_ARRAY_DEFAULT)
      ;;(:OP_SELECT)
      (:OP_CHAR_CONST
       (code-char (z3-get-decl-int-parameter ctx decl 0)))
      (otherwise
       ;; TODO fix this ugly special-case
       (if (z3-is-string ctx ast)
           ;; TODO: do we want to use get-lstring or get-string here?
           ;; benefits to using get-lstring: interface
           ;;   can roundtrip strings, more accurate
           ;;   representation of model
           ;; downsides: more annoying to use in a
           ;;   REPL, unclear how different lisps handle
           ;;   printing strings with "unprintable"
           ;;   characters like control codes
           (get-lstring ctx ast)
         (error "Translation of application ASTs for functions with decl-kind ~S is not currently supported." (z3-get-decl-kind ctx decl)))))))


;; Attempt to translate an AST into a Lisp value.
(defun ast-to-value (ast ctx)
  "Attempt to translate a Z3 AST into a Lisp value."
  (let* ((ast-kind (z3-get-ast-kind ctx ast))
         (sort (z3-get-sort ctx ast))
         (sort-kind (z3-get-sort-kind ctx sort)))
    (match ast-kind
      (:app_ast
       (app-ast-to-value ast ctx))
      (:numeral_ast
       (match sort-kind
         ((or :int_sort :finite_domain_sort :bv_sort) (values (parse-integer (z3-get-numeral-string ctx ast))))
         (:real_sort (/ (ast-to-value (z3-get-numerator ctx ast) ctx) (ast-to-value (z3-get-denominator ctx ast) ctx)))
         (otherwise (error "Translation of numeric values with sort kind ~S is not currently supported." sort-kind))))
      (:var_ast
       (cons :arg (z3-get-index-value ctx ast)))
      (otherwise (error "Translation of ASTs of kind ~S are not currently supported.~%AST that triggered this: ~S" ast-kind (z3-ast-to-string ctx ast))))))


;; TODO these two functions are very similar - should factor common code into a macro or something.
(defun parse-smt2-string (filename &key sorts decls context)
  "Parse the given string using the SMT-LIB2 parser.
It returns an ast-vector comprising of the conjunction of assertions in the scope
(up to push/pop) at the end of the string."
  (let ((ctx (or context *default-context*)))
    (make-instance 'ast-vector
                   :handle
                   (with-foreign-arrays ((sort-names z3-c-types::Z3_symbol sorts :elt-fn #'(lambda (arg) (z3-get-sort-name ctx arg)))
                                         (z3-sorts z3-c-types::Z3_sort sorts)
                                         (decl-names z3-c-types::Z3_symbol decls :elt-fn #'(lambda (arg) (z3-get-decl-name ctx arg)))
                                         (z3-decls z3-c-types::Z3_func_decl decls))
                                        (z3-parse-smtlib2-string ctx filename
                                                               (length sorts) sort-names z3-sorts
                                                               (length decls) decl-names z3-decls))
                   :context ctx)))

;; TODO: use lisp file functions to produce an absolute path here? I
;; have a gut feeling that Z3's file access will not work the same as
;; lisp's in all cases, and that may result in confusion...
(defun parse-smt2-file (filename &key sorts decls context)
  "Parse the file with the given filename using the SMT-LIB2 parser.
It returns an ast-vector comprising of the conjunction of assertions in the scope
(up to push/pop) at the end of the file.
Calls the error handler if the file does not exist or cannot be accessed."
  (let ((ctx (or context *default-context*)))
    (make-instance 'ast-vector
                   :handle
                   (with-foreign-arrays ((sort-names z3-c-types::Z3_symbol sorts :elt-fn #'(lambda (arg) (z3-get-sort-name ctx arg)))
                                         (z3-sorts z3-c-types::Z3_sort sorts)
                                         (decl-names z3-c-types::Z3_symbol decls :elt-fn #'(lambda (arg) (z3-get-decl-name ctx arg)))
                                         (z3-decls z3-c-types::Z3_func_decl decls))
                                        (z3-parse-smtlib2-file ctx filename
                                                               (length sorts) sort-names z3-sorts
                                                               (length decls) decl-names z3-decls))
                   :context ctx)))

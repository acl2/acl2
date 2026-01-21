;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defvar *sorts* (make-hash-table))

#|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  A short discussion on "sort specifiers"
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The user will often use what I call "sort specifiers" to refer to
sorts when interacting with the Z3 interface.

These are symbols (or S-expressions) that fully specify a concrete Z3 sort.
For example:
- :int is the sort specifier for the unbounded integer sort produced
  by (z3-mk-int-sort ctx)
- (:seq :int) is the sort specifier for the sequence sort produced by
  (z3-mk-seq-sort ctx (z3-mk-int-sort ctx))
- (_ :bv 5) is the sort specifier for 5-bit bitvector sort produced by
  (z3-mk-bv-sort ctx 5)

Note that the :seq sort is a parametric sort - it takes in a single
parameter, which corresponds to the sort of the elements that the
sequence exists over.

The :bv sort is an indexed sort - it takes in a single argument, which
corresponds to the length of the bitvector that the sort
represents. Indexed sorts must be denoted using the _ operator,
followed by the name of the type and any arguments.

Sort specifiers are (or contain) symbols in the keyword
package. Internally we name sorts with symbols in the z3-sort
package. We strip the package info from any sort name symbol that is
passed into a function here; that is what the normalize-sort-name
function does. This means that whenever sorts are printed, one doesn't
see the keyword package business (the colon) that otherwise would be
included.

Also note that the sort specifiers correspond to Z3 calls that include
a context value. This is because Z3 sort values are managed by the
context that created them, and are tied to that context. One of the
benefits of using sort specifiers is that the interface can handle
creating the relevant sorts in the current context for the user, who
does not have to worry about whether or not they are in the same
context that a sort was created in.

There is one special sort specifier that is handled in api.lisp:
the (:fn (domain...) range) specifier. This corresponds to an
uninterpreted function that takes in parameters of sorts described by
the list `domain` and produces a value of sort described by
`range`. These are not handled the same as sorts because they behave
differently - the interface needs to create a function declaration
whenever a user specifies that some variable name should be
represented as an uninterpreted function.

|#

(defun normalize-sort-name (name)
  (intern (symbol-name name) :z3-sort))

(defun sort-names-match? (name1 name2)
  (equal (normalize-sort-name name1) (normalize-sort-name name2)))

(defun register-sort (name sort-producer)
  "Register a sort.
   The first argument is either a symbol or a list of symbols. If a single symbol, the name of the sort to register. If a list of symbols, this sort will be registered under each symbol.
   The second argument should be a function object that takes in a single argument (context) and produces a sort."
  (when (null name)
    (error "At least one name must be provided to register-sort!"))
  (let ((name-list (if (consp name) name (list name))))
    (loop for name in name-list
          do (setf (gethash (normalize-sort-name name) *sorts*) sort-producer)))
  name)

;; TODO: currently storing these in a separate hash table, but there's
;; really no reason why we can't have a unified hash table of objects
;; that contain the neccesary metadata for each kind of sort that
;; needs it.
(defvar *parametric-sorts* (make-hash-table))

(defun register-parametric-sort (name parametric-sort-producer)
  "Register a sort.
   The first argument is either a symbol or a list of symbols. If a single symbol, the name of the parametric sort to register. If a list of symbols, this parameteric sort will be registered under each symbol.
   The second argument should be a function object that takes in two arguments (context, list of user-provided arguments) and produces a sort."
  (when (null name)
    (error "At least one name must be provided to register-parametric-sort!"))
  (let ((name-list (if (consp name) name (list name))))
    (loop for name in name-list
          do (setf (gethash (normalize-sort-name name) *parametric-sorts*) parametric-sort-producer)))
  name)

;; TODO unclear how important it is to make the distinction between
;; indexed and parametric sorts, but it is needed to ensure compliance
;; with SMT-LIB2.
(defvar *indexed-sorts* (make-hash-table))

(defun register-indexed-sort (name indexed-sort-producer)
  "Register a sort.
   The first argument is either a symbol or a list of symbols. If a single symbol, the name of the indexed sort to register. If a list of symbols, this indexed sort will be registered under each symbol.
   The second argument should be a function object that takes in two arguments (context, list of user-provided arguments) and produces a sort."
  (when (null name)
    (error "At least one name must be provided to register-indexed-sort!"))
  (let ((name-list (if (consp name) name (list name))))
    (loop for name in name-list
          do (setf (gethash (normalize-sort-name name) *indexed-sorts*) indexed-sort-producer)))
  name)

;; TODO: optimization - memoize calls within a context
;; i.e. (z3-mk-int-sort ctx) will always return the same value for the same value of ctx (AFAIK unless ctx is reset)
;; (but in that case all pointers that we have into Z3 are invalid so ¯\_(ツ)_/¯)
(defun get-sort (name context)
  "Get the sort associated with the given name."
  (match name
    ((type symbol)
     (multiple-value-bind (fn exists?)
         (gethash (normalize-sort-name name) *sorts*)
       (if exists?
           (funcall fn context)
         (error "No known sort with name ~a" name))))
    ;; Indexed identifier
    ((list* (sym-name _) name args)
     (multiple-value-bind (idxed-fn idxed-exists?)
         (gethash (normalize-sort-name name) *indexed-sorts*)
       (if idxed-exists?
           (funcall idxed-fn context args)
         (error "No known indexed sort with name ~a" name))))
    ;; Parametric type application
    ((list* name args)
     (multiple-value-bind (para-fn para-exists?)
         (gethash (normalize-sort-name name) *parametric-sorts*)
       (if para-exists?
           (funcall para-fn context args)
         (error "No known parametric sort with name ~a" name))))
    (otherwise (error "~S is not a valid sort specifier." name))))

;; Some built-in sorts
(register-sort :int #'z3-mk-int-sort)
(register-sort :bool #'z3-mk-bool-sort)
(register-sort :string #'z3-mk-string-sort)
(register-sort :real #'z3-mk-real-sort)

(register-indexed-sort :bitvec
                       #'(lambda (ctx args)
                           (cond ((not (equal (length args) 1)) (error "bitvec sort only takes a single argument."))
                                 ((or (not (numberp (car args))) (minusp (car args))) (error "bitvec sort must have a positive integer size"))
                                 (t (z3-mk-bv-sort ctx (car args))))))

(register-parametric-sort :seq
                          #'(lambda (ctx args)
                              (if (not (equal (length args) 1))
                                  (error "seq sort only takes a single argument.")
                                (z3-mk-seq-sort ctx (get-sort (car args) ctx)))))

(register-parametric-sort :set
                          #'(lambda (ctx args)
                              (if (not (equal (length args) 1))
                                  (error "set sort only takes a single argument.")
                                (z3-mk-set-sort ctx (get-sort (car args) ctx)))))

(register-parametric-sort :regex
                          #'(lambda (ctx args)
                              (unless (equal (length args) 1)
                                (error "regex sort only takes a single argument."))
                              (let ((sort (get-sort (car args) ctx)))
                                (unless (z3-is-seq-sort ctx sort) (error "Regex sort must be over a sequence sort."))
                                (z3-mk-re-sort ctx sort))))

(register-parametric-sort :array
                          #'(lambda (ctx args)
                              (unless (equal (length args) 2) (error "array sort takes two arguments: domain and range sorts"))
                              (z3-mk-array-sort ctx (get-sort (car args) ctx) (get-sort (second args) ctx))))



;;;; Enum types

;; WARNING/TODO: When a new context is created after register-enum-sort has been called, the enum sorts will NOT exist in the new context.
;; One must make the relevant register-enum-sort calls again.
;; I've tried to check for incorrect usage in a few places, but I'm sure I missed something.

(defstruct enum-sort-metadata
  (sort)
  (names)
  (consts)
  (testers))

(defvar *enum-sort-metadata* (make-hash-table))

(defun register-enum-sort-fn (name elements ctx)
  "Register an enum sort with the given name and elements in the given context."
  (cffi:with-foreign-objects
   ((elt-names 'z3-c-types::Z3_symbol (length elements)) ;; input
    (consts 'z3-c-types::Z3_func_decl (length elements)) ;; output
    (testers 'z3-c-types::Z3_func_decl (length elements))) ;; output
   (loop for elt in elements
         for i below (length elements)
         do (setf (cffi:mem-aref elt-names 'z3-c-types::Z3_symbol i)
                  (z3-mk-string-symbol ctx (write-to-string elt))))
   (let ((sort (z3-mk-enumeration-sort ctx (z3-mk-string-symbol ctx (symbol-name name))
                                       (length elements) elt-names consts testers)))
     (setf (gethash (normalize-sort-name name) *enum-sort-metadata*)
           (make-enum-sort-metadata :sort sort
                                    :names elements
                                    :consts (mapcar #'cons elements (foreign-array-to-list consts 'z3-c-types::Z3_func_decl (length elements)))
                                    :testers (mapcar #'cons elements (foreign-array-to-list testers 'z3-c-types::Z3_func_decl (length elements)))))))
  (register-sort name (lambda (context)
                        (if (not (equal context ctx))
                            (error "Attempting to use enumeration type ~a outside of the context in which it is defined.~%You need to call the relevant (register-enum-sort ...) form again in the current context." name)
                          (enum-sort-metadata-sort (gethash (normalize-sort-name name) *enum-sort-metadata*))))))

(defmacro register-enum-sort (name elements &optional context)
  "Register an enum sort with the given name and elements in the given context."
  `(let ((ctx (or ,context *default-context*)))
     (register-enum-sort-fn ',name ',elements ctx)
     ',name))

(defun sort-name (sort context)
  "Get the name of a sort."
  (z3-get-symbol-string context (z3-get-sort-name context sort)))

(defun enum-sort? (sort context)
  "Determine if the given sort corresponds to a registered enum sort."
  (let ((sort-name (intern (sort-name sort context) :z3-sort)))
    (multiple-value-bind (_ exists?)
        (gethash sort-name *enum-sort-metadata*)
      (declare (ignore _))
      exists?)))

(defun enum-value-func-def (name value)
  "Get the constant func-def corresponding to the given enum sort element."
  (multiple-value-bind (metadata exists?)
      (gethash (normalize-sort-name name) *enum-sort-metadata*)
    (cond ((not exists?) (error "~S does not name an enum sort." name))
          ((not (member value (enum-sort-metadata-names metadata)))
           (error "~S is not a member of enum sort ~a.~%Valid values of this sort are ~S." value name (enum-sort-metadata-names metadata)))
          (t (cdr (assoc value (enum-sort-metadata-consts metadata)))))))

(defun enum-value-to-ast (name value ctx)
  "Get an AST node corresponding to the given enum sort element."
  (z3-mk-app ctx (enum-value-func-def name value) 0 (cffi:null-pointer)))

(defun enum-tester-func-def (name value)
  "Get the tester func-def for the given enum sort element."
  (multiple-value-bind (metadata exists?)
      (gethash (normalize-sort-name name) *enum-sort-metadata*)
    (cond ((not exists?) (error "~a does not name an enum sort." name))
          ((not (member value (enum-sort-metadata-names metadata)))
           (error "~S is not a member of enum sort ~a.~%Valid values of this sort are ~S." value name (enum-sort-metadata-names metadata)))
          (t (cdr (assoc value (enum-sort-metadata-testers metadata)))))))

(defun get-enum-value (sort decl context)
  "Given a func-decl corresponding to an element of an enum sort, return the Lisp equivalent of the enum element."
  ;; decl must be a func-decl
  (let* ((sort-name (intern (sort-name sort context) :z3-sort)))
    (multiple-value-bind (metadata exists?)
        (gethash sort-name *enum-sort-metadata*)
      (if (not exists?)
          (error "Tried to get enum value of non-enum sort ~a" sort-name)
        (car (rassoc decl (enum-sort-metadata-consts metadata)))))))

;;;; Named tuple types

;; WARNING/TODO: When a new context is created after register-tuple-sort has been called, the tuple sorts will NOT exist in the new context.
;; One must make the relevant register-tuple-sort calls again.
;; I've tried to check for incorrect usage in a few places, but I'm sure I missed something.

(defstruct tuple-sort-metadata
  (sort)
  (field-names)
  (field-sorts)
  (constructor)
  (field-accessors))

(defvar *tuple-sort-metadata* (make-hash-table))

(defun register-tuple-sort-fn (name fields ctx)
  "Register a tuple sort with the given name and fields in the given context."
  ;; fields should be an alist of symbol->sortlike
  (let ((n-fields (length fields)))
    (cffi:with-foreign-objects
     ((field-names 'z3-c-types::Z3_symbol n-fields) ;; input
      (field-sorts 'z3-c-types::Z3_sort n-fields)
      (constructor-decl 'z3-c-types::Z3_func_decl) ;; output
      (projection-decls 'z3-c-types::Z3_func_decl n-fields)) ;; output
     (loop for (field-name . field-sort) in fields
           for i below n-fields
           do (setf (cffi:mem-aref field-names 'z3-c-types::Z3_symbol i)
                    (z3-mk-string-symbol ctx (write-to-string field-name))) ;; TODO maybe name the fields more like `,name/,field-name`
           do (setf (cffi:mem-aref field-sorts 'z3-c-types::Z3_sort i)
                    (get-sort field-sort ctx)))
     (let ((sort (z3-mk-tuple-sort ctx
                                   (z3-mk-string-symbol ctx (symbol-name name))
                                   n-fields
                                   field-names
                                   field-sorts
                                   constructor-decl
                                   projection-decls)))
       (setf (gethash (normalize-sort-name name) *tuple-sort-metadata*)
             (make-tuple-sort-metadata :sort sort
                                       :field-names (mapcar #'car fields)
                                       :field-sorts (foreign-array-to-list field-sorts 'z3-c-types::Z3_sort n-fields) ;; TODO why not just make this list earlier and use it to build the foreign array?
                                       :constructor (cffi:mem-ref constructor-decl 'z3-c-types::Z3_func_decl)
                                       :field-accessors (mapcar #'cons (mapcar #'car fields) (foreign-array-to-list projection-decls 'z3-c-types::Z3_func_decl n-fields)))))))
  (register-sort name (lambda (context)
                        (if (not (equal context ctx))
                            (error "Attempting to use tuple type ~a outside of the context in which it is defined.~%You need to call the relevant (register-tuple-sort ...) form again in the current context." name)
                          (tuple-sort-metadata-sort (gethash (normalize-sort-name name) *tuple-sort-metadata*))))))

(defmacro register-tuple-sort (name fields &optional context)
  "Register a tuple sort with the given name and fields in the given context."
  `(let ((ctx (or ,context *default-context*)))
     (register-tuple-sort-fn ',name ',fields ctx)
     ',name))

(defun tuple-sort? (sort context)
  "Determine if the given sort corresponds to a registered tuple sort."
  (let ((sort-name (intern (sort-name sort context) :z3-sort)))
    (multiple-value-bind (_ exists?)
        (gethash sort-name *tuple-sort-metadata*)
      (declare (ignore _))
      exists?)))

(defun get-tuple-fields (sort app context)
  "Given a application corresponding to the construction of a tuple value, return the AST values of the fields of the tuple."
  (let* ((sort-name (intern (sort-name sort context) :z3-sort)))
    (multiple-value-bind (metadata exists?)
        (gethash sort-name *tuple-sort-metadata*)
      (cond ((not exists?)
             (error "Tried to get tuple value of non-tuple sort ~a" sort-name))
            ((not (equal (length (tuple-sort-metadata-field-names metadata))
                         (z3-get-app-num-args context app))) (error "Incorrect number of arguments passed to tuple constructor."))
            (t (loop for name in (tuple-sort-metadata-field-names metadata)
                     for i below (length (tuple-sort-metadata-field-names metadata))
                     collect (cons name (z3-get-app-arg context app i))))))))

(defun construct-tuple-fn (tuple-name values context)
  "Make an AST node that constructs a value of the given tuple with the given field values.
   Field values must be provided in the same order as they were defined in the register-tuple-sort call for this tuple sort."
  ;; TODO: write a version of this function that takes in an alist of field-name -> field-value
  ;; such a function would be able to catch errors more effectively
  (multiple-value-bind (metadata exists?)
      (gethash (normalize-sort-name tuple-name) *tuple-sort-metadata*)
    (cond ((not exists?) (error "~a does not name a tuple sort." tuple-name))
          ((not (equal (length values) (length (tuple-sort-metadata-field-names metadata))))
           (error "Incorrect number of arguments provided to constructor for ~S: ~S provided, ~S required."
                  tuple-name (length values) (length (tuple-sort-metadata-field-names metadata))))
          (t (with-foreign-array (values-array z3-c-types::Z3_ast values)
               (z3-mk-app context (tuple-sort-metadata-constructor metadata) (length values) values-array))))))

;; TODO why do we take in context?
(defun get-tuple-field-accessor-decl-fn (tuple-name field-name context)
  (declare (ignore context))
  (multiple-value-bind (metadata exists?)
      (gethash (normalize-sort-name tuple-name) *tuple-sort-metadata*)
    (cond ((not exists?) (error "~a does not name a tuple sort." tuple-name))
          ((not (member field-name (tuple-sort-metadata-field-names metadata)))
           (error "Tuple ~a does not contain a field with name ~S.~%Valid field names are ~S." tuple-name field-name (tuple-sort-metadata-field-names metadata)))
          (t (cdr (assoc field-name (tuple-sort-metadata-field-accessors metadata)))))))

(defun construct-tuple-field-accessor-fn (tuple-name field-name tuple-value context)
  "Make an AST node that accesses the given field of the given tuple-value."
  (with-foreign-array (args-array z3-c-types::Z3_ast (list tuple-value))
    (z3-mk-app context (get-tuple-field-accessor-decl-fn tuple-name field-name context) 1 args-array)))

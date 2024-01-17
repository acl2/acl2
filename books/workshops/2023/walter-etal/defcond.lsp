(in-package :defcond)

;; these two functions are adapted from Ben's startup.lisp for inv game
(declaim (ftype (function (list) string) concat-syms))
(defun concat-syms (syms)
  (if (endp syms)
      ""
    (concatenate 'string (symbol-name (car syms))
                 (concat-syms (cdr syms)))))

;; Concatenate all of the symbols in syms together, and then intern them in the given package
(declaim (ftype (function (t list) symbol) concat-syms-in-package))
(defun concat-syms-in-package (pkg syms)
  (intern (concat-syms syms) pkg))

(defun proplist-get (proplist key)
  (cond
   ((endp (cdr proplist)) (values nil nil))
   ((equal (car proplist) key) (values (cadr proplist) t))
   (t (proplist-get (cddr proplist) key))))

(defmacro proplist-exists? (proplist key)
  (multiple-value-bind
    (_ exists?)
    (proplist-get proplist key)
    exists?))

(defun proplist-remove-key (proplist key)
  (cond
   ((endp (cdr proplist)) nil)
   ((equal (car proplist) key) (proplist-remove-key (cddr proplist) key))
   (t (cons (car proplist)
            (cons (cadr proplist)
                  (proplist-remove-key (cddr proplist) key))))))

(defun proplist-remove-keys (proplist keys)
  (if (endp keys)
      proplist
    (proplist-remove-keys
     (proplist-remove-key proplist (car keys))
     (cdr keys))))

;; The defcond macro

(defstruct (defcond-condition-metadata)
  (name nil :type symbol)
  (fields nil :type list)
  (parents nil :type list))

(defvar *defcond-known-conditions* nil)

(define-condition defcond-condition ()
  ())

;; By default just use the condition's reporter
(defgeneric long-report (condition)
  (:documentation "Takes a condition and produces a message string appropriate for display to the user.")
  (:method (obj) (format nil "Unexpected condition signalled: ~a" obj))
  (:method ((condition defcond-condition)) (format nil "~a" condition)))

(defgeneric short-report (condition)
  (:documentation "Takes a condition and produces a message string appropriate for display to the user.")
  (:method (obj) (format nil "Unexpected condition signalled: ~a" obj))
  (:method ((condition defcond-condition)) (long-report condition)))

(defun defcond-field-accessor-generated-name (cond-name field-name)
  (concat-syms-in-package (symbol-package cond-name) (list cond-name '/ field-name)))

(defun defcond-field-spec-to-name (field-spec)
  (if (consp field-spec)
      (car field-spec)
    field-spec))

(defun defcond-field-spec-to-accessor (cond-name field-spec)
  (concat-syms-in-package (symbol-package cond-name) (list cond-name '/ (defcond-field-spec-to-name field-spec))))

(defun get-arg-from-field-spec (field-spec key &optional default)
  (if (not (consp field-spec))
      default
    (multiple-value-bind (val found?)
      (proplist-get (cdr field-spec) key)
      (if found? val default))))

(defun defcond-fieldspec (cond-name field-spec)
  `(,(defcond-field-spec-to-name field-spec)
    :initform ,(get-arg-from-field-spec field-spec :initform)
    :initarg ,(get-arg-from-field-spec field-spec :initarg (intern (symbol-name (defcond-field-spec-to-name field-spec)) "KEYWORD"))
    :reader ,(get-arg-from-field-spec field-spec :reader (defcond-field-spec-to-accessor cond-name field-spec))
    ,@(proplist-remove-keys (when (consp field-spec) (cdr field-spec)) '(:initform :initarg :reader))))

(defun get-defcond-metadata (name)
  (loop for metadata in *defcond-known-conditions*
        when (equal name (defcond-condition-metadata-name metadata))
        do (return-from get-defcond-metadata metadata))
  nil)

(defun get-defcond-field-metadata (name)
  (let ((metadata (get-defcond-metadata name)))
    (when metadata
      (append (defcond-condition-metadata-fields metadata)
              (loop for parent in (defcond-condition-metadata-parents metadata)
                    append (get-defcond-field-metadata parent))))))

(defun deduplicate-fields-in-metadata (metadata)
  (let ((fields (fset:empty-map))
        (rev-metadata (reverse metadata)))
    (loop for (field-name . field-accessor) in rev-metadata
          do (setf fields (fset:with fields field-name field-accessor)))
    (fset:convert 'list fields)))

(defun get-defcond-bindings (name var)
  (let ((field-metadata (deduplicate-fields-in-metadata (get-defcond-field-metadata name))))
    (loop for (field-name . field-accessor) in field-metadata
          collect `(,field-name (,field-accessor ,var)))))

(defun defcond-reporter (cond-name field-specs reporter)
  (let ((report-str (car reporter))
        (bindings (get-defcond-bindings cond-name 'condition))
        #|
         (mapcar (lambda (field-spec)
                            (list field-spec (list (defcond-field-accessor cond-name field-specs) 'condition)))
        (remove-if-not #'symbolp field-specs)))
        |#
        (args (cdr reporter)))
    `(lambda (condition stream)
       (let ((*print-pretty* t))
         (let ,bindings
           (declare (ignorable ,@(mapcar #'car bindings)))
           (format stream ,report-str ,@args))))))

(defun define-defcond-reporter (reporter-name cond-name field-specs reporter-spec)
  (let ((report-str (car reporter-spec))
        (bindings (get-defcond-bindings cond-name 'condition))
        #|
        (bindings (mapcar (lambda (field-spec)
                            (list field-spec (list (defcond-field-accessor cond-name field-spec) 'condition)))
        (remove-if-not #'symbolp field-specs)))
        |#
        (args (cdr reporter-spec)))
    `(defmethod ,reporter-name ((condition ,cond-name))
       (let ((*print-pretty* t))
         (let ,bindings
           (declare (ignorable ,@(mapcar #'car bindings)))
           (format nil ,report-str ,@args))))))

;; post-hooks are functions that take in a condition-metadata struct
;; and any unknown keyword args passed to defcond and produce a list
;; of s-expressions to add to the end of the generated progn during a
;; defcond.
(defvar *defcond-post-hooks* nil)

(defun add-defcond-post-hook (name hook)
  (setf *defcond-post-hooks* (cons (cons name hook) (remove-if #'(lambda (hook-spec) (equal (car hook-spec) name)) *defcond-post-hooks*))))

;; field-hooks are functions that take in the defcond name, any parent
;; metadata, any unknown kwd args, and the list of field-specs before
;; processing, and return a new list of field-specs. These hooks may
;; be called in any order.
(defvar *defcond-field-hooks* nil)

(defun add-defcond-field-hook (name hook)
  (setf *defcond-field-hooks* (cons (cons name hook) (remove-if #'(lambda (hook-spec) (equal (car hook-spec) name)) *defcond-field-hooks*))))

(defmacro defcond (name parents-spec field-specs reporter &rest rest-args &key long-reporter short-reporter &allow-other-keys)
  (let ((parents (if (listp parents-spec) parents-spec (list parents-spec))))
    (when (get-defcond-metadata name)
      (error "A defcond with name ~S already exists!" name))
    (let ((unused-args (proplist-remove-keys rest-args '(:long-reporter :short-reporter))))
      (loop for (hook-name . hook) in *defcond-field-hooks*
            do (setf field-specs (funcall hook name parents unused-args field-specs)))
      (let* ((fields (mapcar #'(lambda (field-spec)
                                 (cons (defcond-field-spec-to-name field-spec)
                                       (defcond-field-spec-to-accessor name field-spec)))
                             field-specs))
             (metadata (make-defcond-condition-metadata
                        :name name
                        :fields fields
                        :parents parents)))
        (push metadata *defcond-known-conditions*)
        `(progn
           (define-condition ,name (,@parents defcond-condition)
             ,(mapcar (lambda (fname) (defcond-fieldspec name fname)) field-specs)
             ,@(when (not (equal reporter nil))
                 `((:report ,(defcond-reporter name field-specs reporter)))))
           ,@(when long-reporter (list (define-defcond-reporter 'long-report name field-specs long-reporter)))
           ,@(when short-reporter (list (define-defcond-reporter 'short-report name field-specs short-reporter)))
           ,@(loop for (hook-name . hook) in *defcond-post-hooks* append (funcall hook metadata unused-args)))))))

#|
(defcond foo ()
  (a b)
  ("A: ~S B: ~S" a b))

(defcond bar (foo)
  (c)
  ("A: ~S B: ~S C: ~S" a b c))

(error 'bar :a 1 :b 2 :c 3)
|#

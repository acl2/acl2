(load "defcond.lsp")
(in-package :prover)

(define-condition checker-condition-metadata ()
  ((ignorep :type bool :initform nil :initarg :step :reader checker-condition-metadata/ignorep)
   (target-id :type (or number list) :initform nil :initarg :target-id :reader checker-condition-metadata/target-id)
   (category :type (or string null) :initform nil :initarg :category :reader checker-condition-metadata/category)
   (kind :type (or string null) :initform nil :initarg :kind :reader checker-condition-metadata/kind)))

(define-condition checker-error (error checker-condition-metadata)
  ((category :initform "MISC_ERROR")
   (kind :initform "MISC_ERROR")))

(define-condition checker-warning (warning checker-condition-metadata)
  ((category :initform "MISC_WARNING")
   (kind :initform "MISC_WARNING")))

(define-condition checker-info (checker-condition-metadata)
  ((category :initform "MISC_INFO")
   (kind :initform "MISC_INFO")))

(setf defcond::*defcond-known-conditions*
      (append (list
               (make-defcond-condition-metadata
                :name 'checker-condition-metadata
                :fields '((ignorep . checker-condition-metadata/ignorep)
                          (target-id . checker-condition-metadata/target-id)
                          (category . checker-condition-metadata/category)
                          (kind . checker-condition-metadata/kind))
                :parents nil)
               (make-defcond-condition-metadata
                :name 'checker-error
                :parents '(checker-condition-metadata))
               (make-defcond-condition-metadata
                :name 'checker-warning
                :parents '(checker-condition-metadata))
               (make-defcond-condition-metadata
                :name 'checker-info
                :parents '(checker-condition-metadata)))
              defcond::*defcond-known-conditions*))

(defgeneric get-target-id (condition)
  (:documentation "Gets the XText node id associated with a condition, or nil if no such id is known.")
  (:method (obj) (declare (ignore obj)) nil)
  (:method ((condition checker-condition-metadata)) (checker-condition-metadata/target-id condition)))

(defgeneric get-condition-category (condition)
  (:documentation "Gets the XText category string associated with a condition, or nil if no such string is known.")
  (:method (obj) (declare (ignore obj)) nil)
  (:method ((condition checker-condition-metadata)) (checker-condition-metadata/category condition)))

(defgeneric get-condition-kind (condition)
  (:documentation "Gets the XText kind string associated with a condition, or nil if no such string is known.")
  (:method (obj) (declare (ignore obj)) nil)
  (:method ((condition checker-condition-metadata)) (checker-condition-metadata/kind condition)))

(defgeneric get-condition-severity (condition)
  (:documentation "Gets the severity associated with a condition.")
  (:method (obj) (declare (ignore obj)) nil)
  (:method ((condition error)) (declare (ignore condition)) :error)
  (:method ((condition warning)) (declare (ignore condition)) :warn)
  (:method ((condition checker-info)) (declare (ignore condition)) :info))

(add-defcond-field-hook :handle-kind
 #'(lambda (name parents args fields)
     (declare (ignore name parents))
     (multiple-value-bind
       (kind-arg exists?)
       (defcond::proplist-get args :kind)
       (cond ((and exists? (or (member 'kind fields :test #'equal)
                               (some #'(lambda (field) (and (consp field) (equal (car field) 'kind))) fields)))
              (error "Can't provide both the :kind keyword argument and a kind field!"))
             (exists? (cons `(kind :initform ,kind-arg) fields))
             (t fields)))))

(add-defcond-field-hook :handle-category
 #'(lambda (name parents args fields)
     (declare (ignore name parents))
     (multiple-value-bind
       (category-arg exists?)
       (defcond::proplist-get args :category)
       (cond ((and exists? (or (member 'category fields :test #'equal)
                               (some #'(lambda (field) (and (consp field) (equal (car field) 'category))) fields)))
              (error "Can't provide both the :category keyword argument and a category field!"))
             (exists? (cons `(category :initform ,category-arg) fields))
             (t fields)))))

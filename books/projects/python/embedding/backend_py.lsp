(load "package.lsp")
(in-package :wgdt)

(ql:quickload :cl-json)

(declaim (ftype (function (* symbol) symbol) intern-sym-in-package))
(defun intern-sym-in-package (pkg sym)
  (intern (symbol-name sym) pkg))

(declaim (ftype (function (list) string) concat-syms))
(defun concat-syms (syms)
  (if (endp syms)
      ""
    (concatenate 'string (symbol-name (car syms))
                 (concat-syms (cdr syms)))))

;; Concatenate all of the symbols in syms together, and then intern them in the given package
(declaim (ftype (function (* list) symbol) concat-syms-in-package))
(defun concat-syms-in-package (pkg syms)
  (intern (concat-syms syms) pkg))

(defconst *type-table* (make-hash-table :test #'equal))
#|
Entries in the type table are of one of the following forms:
'nonparametric': (:name <string> :kind "nonparametric" :defdata-ty <sexpr>  )
'parametric': (:name <string> :kind "parametric" :defdata-ty <arglist -> sexpr>)
'constant': (:name "constant" :kind "constant")
|#

(defconst *alias-table* (make-hash-table :test #'equal))

(defun add-alias-type (name alias-of)
  (let ((name (string-downcase name))
        (alias-of (string-downcase alias-of)))
    ;; TODO do a graph cyclicity check or something that can handle indirect circular references
    (when (equal (gethash alias-of *alias-table*) name) (error "It is illegal to set ~a as an alias for ~a because ~a is already an alias for ~a." name alias-of alias-of name))
    (setf (gethash name *alias-table*)
          alias-of)))

(defun add-nonparametric-type (name defdata-ty)
  (setf (gethash name *type-table*)
        `(:name ,name :kind "nonparametric" :defdata-ty ,defdata-ty)))

(defun add-parametric-type (name defdata-ty-lambda)
  (setf (gethash name *type-table*)
        `(:name ,name :kind "parametric" :defdata-ty ,defdata-ty-lambda)))

(defun get-type (name)
  ;;(print name)
  (let* ((name (string-downcase name))
         (alias (gethash name *alias-table*)))
    (if alias (get-type alias)
      (gethash name *type-table*))))

(defun alist-to-plist (alist)
  (loop for (key . val) in alist
        append (list key val)))

(defun init-types ()
  ;;(add-nonparametric-type "character" 'acl2s::character)
  ;;(add-alias-type "char" "character")
  (add-nonparametric-type "integer" 'acl2s::py-integer)
  (add-alias-type "int" "integer")
  (add-nonparametric-type "float" 'acl2s::py-float)
  (add-nonparametric-type "str" 'acl2s::py-str)
  (add-nonparametric-type "bool" 'acl2s::py-bool)
  (add-nonparametric-type "unicode-codepoint-string" 'acl2s::unicode-codepoint-string)
  (add-alias-type "unicode" "unicode-codepoint-string")
  (add-alias-type "string" "str")
  (add-alias-type "boolean" "bool")
  (add-parametric-type "list"
                       (lambda (el-ty)
                         (let ((elt-ty-sym (translate-type-to-defdata
                                             (if (stringp el-ty) el-ty (alist-to-plist el-ty)))))
                           `(acl2s::listof ,elt-ty-sym))))
  (add-parametric-type "dictionary"
                       (lambda (key-ty val-ty)
                         (let ((key-ty-sym (translate-type-to-defdata 
                                             (if (stringp key-ty) key-ty (alist-to-plist key-ty))))
                               (val-ty-sym (translate-type-to-defdata 
                                             (if (stringp val-ty) val-ty (alist-to-plist val-ty)))))
                           `(acl2s::map ,key-ty-sym ,val-ty-sym))))
  (add-parametric-type "fixedtuple"
                       (lambda (&rest types)
                         (let ((ty-syms (mapcar (lambda (ty)
                                                  (translate-type-to-defdata
                                                    (if (stringp ty) ty (alist-to-plist ty))))
                                                types)))
                           `(acl2s::list ,@ty-syms))))
  (add-nonparametric-type "nonetype" 'acl2s::py-none)
  (add-nonparametric-type "bytes" 'acl2s::py-bytes))
  ;;(add-nonparametric-type "string" 'acl2s::string))

(defmacro get-field (obj fieldname)
  `(cdr (assoc ,fieldname ,obj)))

(defun translate-type-to-defdata (ty)
  (format t "~a~%" ty)
  (if (stringp ty)
    (getf (get-type ty) ':defdata-ty)
    (match (getf ty :kind)
           ("constant" (error "Cannot translate a constant type to defdata."))
           ("parametric"
            (let ((entry (get-type (getf ty :name))))
              (unless entry (error "ERROR: No type found with name ~S" (getf ty :name)))
              (apply (getf entry :defdata-ty) (getf ty :args))))
           ("nonparametric"
            (let ((entry (get-type (getf ty :name))))
              (unless entry (error "ERROR: No type found with name ~S" (getf ty :name)))
              (getf entry :defdata-ty))))))

(defconst *define-type-cache* (make-hash-table :test #'equal))
(defun define-type (ty)
  (let* ((ty-defdata (translate-type-to-defdata ty)))
    (multiple-value-bind (cache-entry in-cache)
      (gethash ty-defdata *define-type-cache*)
      (if in-cache
          cache-entry
        (let* ((is-list (equal (getf ty :name) "list"))
               (fresh-name (intern-sym-in-package :ACL2s (gensym "TY")))
               (query `(acl2s::defdata ,fresh-name ,ty-defdata ,@(when is-list '(:do-not-alias t))))
               (res (acl2s-interface::acl2s-event query)))
          (format t "~a~%" query)
          (finish-output)
          (when (car res) (error "ERROR: Error occurred when running query ~S" query))
          ;; Attach the appropriate pylistof enumerator when needed
          (when is-list
            (let* ((attach-query (acl2s::attach-pylistof-wrap
                                  fresh-name
                                  (cadr ty-defdata)))
                   (res2 (progn (format t "~a~%" attach-query) (finish-output) (acl2s-interface::acl2s-event attach-query))))
              (when (car res2) (error "ERROR: Error occurred when running generate-attach-pylistof-enumerators query"))))
          (setf (gethash ty-defdata *define-type-cache*) fresh-name))))))

(defun get-unaliased-enumerator-name (ty-name)
  (let ((defdata::wrld (acl2s::w acl2s::state)))
    (defdata::enumerator-name ty-name)))

;;(defconst *get-enumerator-memo* (make-hash-table :test #'equal))
(defun get-enumerator (ty-name)
  ;; TODO: if this type is an alias, need to look in alias table and pull
  ;; out the actual type name so that we get a function instead of a macro.
  (fdefinition (get-unaliased-enumerator-name ty-name)))

(init-types)

(defconstant ENUM-MAX-INPUT (expt 2 31))
;; assume the input is either a string or a type definition object
(defun generate-examples (ty n random-state)
  (let* ((temporary-ty-name (if (stringp ty) (getf (get-type ty) ':defdata-ty) (define-type ty)))
         (enumerator (get-enumerator temporary-ty-name)))
    (print temporary-ty-name)
    (print enumerator)
    (loop for i below n
          collect (funcall enumerator (random ENUM-MAX-INPUT random-state)))))


;; Creates a new record type with the given name and the given fields.
;; The first argument is the name of the type and the second argument is an alist
;;  mapping the names of fields to the names of their respective types
;; ASSUMPTION: the types of the fields are all non-parametric
;; create-record-type : string (alistof string string) -> string
;; TODO: Have this function register aliases automatically for field types
(defun create-record-type (name fields)
  (let* ((defdata-name (intern-sym-in-package :ACL2s (read-from-string name)))
         (query `(acl2s::defdata 
                   ,defdata-name
                   (acl2s::record 
                     ,@(mapcar (lambda (x)
                                 (print (get-type (cdr x)))
                                `(,(read-from-string (car x)) 
                                   . 
                                   ,(getf (get-type (cdr x)) ':defdata-ty)))
                         fields))))
         (res (acl2s-interface::acl2s-event query)))
    (print query)
    (format t "~a~%" res)
    (finish-output)
    (when (car res) (error "ERROR: Error occurred when running query ~S" query))
    (add-nonparametric-type (string-downcase name) defdata-name)
    name))


;; Registers a type under a new name
;; The given type can either be a name of an existing type/type alias,
;;  or it can be a recognized non-parametric type or instantiated parametric type
;; register-alias : string (oneof string ty) -> string
(defun register-alias (alias ty)
  (cond
    ((stringp ty) 
     (progn
       (add-alias-type alias ty)
        alias)) ;; NOTE: this may fail silently if ty is not a defined type
    (t (let* ((fresh-name (define-type ty)))
              (progn 
                (add-nonparametric-type (string-downcase alias) fresh-name)
                alias)))))

;; Unbinds a name in the type and alias tables
;; unbind-type : string -> void
(defun unbind-type (name)
  (progn
    (remhash name *type-table*)
    (remhash name *alias-table*)))


;; Deduplicates a list
;; dedup : list -> list
(defun dedup (lst)
  (if (= (length lst) 0)
    lst
    (let ((deduped-rest (dedup (cdr lst))))
      (if (some (lambda (x) (equal x (car lst))) deduped-rest)
        deduped-rest
        (cons (car lst) deduped-rest)))))


;; Registers a union type
;; This function assumes that the arguments of the union are types that have been defined previously; i.e. they are keys in the table table
;; register-union : string list-of-strings -> string
(defun register-union (name args)
  (let* ((defdata-name (intern-sym-in-package :ACL2s (read-from-string name)))
         (defdata-union-args (dedup (mapcar (lambda (arg) 
                                       (getf (get-type arg) ':defdata-ty))
                                     args)))
         (query (if (> (length defdata-union-args) 1)
                `(acl2s::defdata
                   ,defdata-name
                   (acl2s::or ,@defdata-union-args))
                `(acl2s::defdata
                   ,defdata-name
                   ,@defdata-union-args)))
         (res (acl2s-interface::acl2s-event query)))
    (print defdata-union-args)
    (print query)
    (format t "~a~%" res)
    (finish-output)
    (if (car res)
      (error "ERROR: Error occurred when running query ~S" query)
      (progn
        (add-nonparametric-type (string-downcase name) defdata-name)
        name))))

(defun type-query (name)
  (let* ((ty (get-type name)))
    (if ty
      `((:name . ,(getf ty ':name)) (:kind . ,(getf ty ':kind)))
      nil)))


(defun make-cl-seed (val)
  (assert (< val (expt 2 32)))
  #+SBCL (let ((byte-array (make-array '(4) :element-type '(unsigned-byte 8))))
           (setf (aref byte-array 0) (ldb (byte 8 0) val))
           (setf (aref byte-array 1) (ldb (byte 8 8) val))
           (setf (aref byte-array 2) (ldb (byte 8 16) val))
           (setf (aref byte-array 3) (ldb (byte 8 24) val))
           (sb-ext:seed-random-state byte-array)))

#|
(defun flatten-alist (alist)
  (loop for (k . v) in alist
        append (list k v)))

(defparameter f (json::decode-json-from-string "{\"kind\":\"parametric\",\"name\":\"range\",\"args\":[\"integer\",0,10]}"))
(defparameter s (json::decode-json-from-string "{\"kind\":\"nonparametric\",\"name\":\"string\"}"))

(funcall (get-enumerator (define-type (flatten-alist f))) 0)
(funcall (get-enumerator (define-type (flatten-alist s))) 0)

(acl2s::quiet-mode-on)

(generate-examples (flatten-alist f) 100)
(generate-examples (flatten-alist s) 100)
|#
#|
(require :sb-sprof)
(sb-sprof:with-profiling (:mode :cpu :MAX-SAMPLES 10000 :sample-interval 0.001 :loop t) (progn (generate-examples (flatten-alist f) 100) nil))

(SB-SPROF:START-PROFILING :MODE :CPU :MAX-SAMPLES 10000
                          :SAMPLE-INTERVAL 0.001 :THREADS :ALL)
(loop (when (>= sb-sprof::trace-count 1000) (return))
      (progn (generate-examples (flatten-alist f) 1000) nil))

(sb-sprof:report)
(sb-sprof:reset)
(sb-sprof:stop-profiling)
|#
#|
(defun defdata-events (a1 wrld)
  (b* (((list D kwd-alist) a1) ;a1 is the result of parse-defdata
       (d-alist (cdar d))
       (name (get1 'name d-alist))
       (odef (get1 'odef (cdar d)))
       (pdef (get1 'pdef (cdar d)))
       (ndef (get1 'ndef (cdar d)))
       (record? (and (consp odef) (equal 'record (car odef))))
       (global-alias-off?
        (not (acl2s::get-acl2s-defaults :defdata-aliasing-enabled wrld)))
       (do-not-alias? (or record? global-alias-off? (get1 :do-not-alias kwd-alist)))
       (M (type-metadata-table wrld))
       (match-def (match-alist name :DEF odef M))
       (match-def (or match-def (match-alist name :PRETTYIFIED-DEF pdef M)))
       (match-def (or match-def (match-alist name :NORMALIZED-DEF ndef M))))
    (if (and match-def (not do-not-alias?))
        `(defdata-alias ,name ,match-def)
      (defdata-core-events a1 wrld))))
|#

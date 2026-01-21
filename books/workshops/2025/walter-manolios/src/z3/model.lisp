;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3)

(defun func-entry-to-string (entry context)
  (let ((s (make-string-output-stream)))
    ;; TODO surely this can be rewritten using format
    (write-string "(" s)
    (loop for i below (z3-func-entry-get-num-args context entry)
          do (progn
               (unless (equal i 0) (write-string " " s))
               (write-string (z3-ast-to-string context (z3-func-entry-get-arg context entry i)) s)))
    (write-string ") -> " s)
    (write-string (z3-ast-to-string context (z3-func-entry-get-value context entry)) s)
    (get-output-stream-string s)))

(defmethod model-const-decls ((model model))
  "Get a list of constant declarations from the given model."
  (let ((ctx (get-context model)))
    (loop for i below (z3-model-get-num-consts ctx model)
          collect (make-instance 'func-decl :handle (z3-model-get-const-decl ctx model i) :context ctx))))

(defun model-constants (model)
  "Retrieve constant interpretations from the given model."
  ;; This is a two step process:
  ;; 1. Get constant declarations (note that these are function declarations with 0 parameters) from the model
  ;; 2. Get the interpretations of each of the constant declarations from the model and convert into Lisp forms.
  (let ((ctx (get-context model))
        (const-decls (model-const-decls model)))
    (loop for decl in const-decls
          for name = (z3-get-symbol-string ctx (z3-get-decl-name ctx decl))
          for value = (z3-model-get-const-interp ctx model decl)
          ;; TODO: will this catch a null pointer? Need a test case...
          when (not (equal value 0)) ;; may return null if the model doesn't assign an interpretation for the func-decl.
          ;; TODO: what should we do if model doesn't assign an interpretation? Currently we silently skip.
          collect (list (intern name) (ast-to-value value ctx)))))

(defun convert-func-entry (entry ctx)
  "Convert a function interpretation entry into a cons pair."
  (z3-func-entry-inc-ref ctx entry)
  (let ((args
         (loop for i below (z3-func-entry-get-num-args ctx entry)
               collect (ast-to-value (z3-func-entry-get-arg ctx entry i) ctx)))
        (val (ast-to-value (z3-func-entry-get-value ctx entry) ctx)))
    (z3-func-entry-dec-ref ctx entry)
    (cons args val)))

(defun func-interp-to-alist (interp ctx)
  "Translate a function intepretation into an alist."
  (let ((num-entries (z3-func-interp-get-num-entries ctx interp)))
    (cons (cons :default (ast-to-value (z3-func-interp-get-else ctx interp) ctx))
          (loop for i below num-entries
                for entry = (z3-func-interp-get-entry ctx interp i)
                collect (convert-func-entry entry ctx)))))

(defmethod model-func-decls ((model model))
  "Get a list of function declarations from the given model."
  (let ((ctx (get-context model)))
    (loop for i below (z3-model-get-num-funcs ctx model)
          collect (make-instance 'func-decl :handle (z3-model-get-func-decl ctx model i) :context ctx))))

(defun model-functions (model)
  "Retrieve function interpretations from the given model."
  ;; Basically there are three steps:
  ;; 1. Get the function declarations from the model
  ;; 2. Use the function declarations to get the function interpretations from the model
  ;; 3. Convert the function interpretations into Lisp forms (we translate into alists)
  (let ((ctx (get-context model))
        (func-decls (model-func-decls model)))
    (loop for decl in func-decls
          for interp = (z3-model-get-func-interp ctx model decl)
          for name = (z3-get-symbol-string ctx (z3-get-decl-name ctx decl))
          collect (list (intern name)
                        (list 'quote (list :fn
                                           ;; TODO: it might be better to return the user-provided sort specifiers for this function. But this will work for now.
                                           (list (func-decl-domain decl ctx) (func-decl-range decl ctx))
                                           (func-interp-to-alist interp ctx)))))))

(defmethod model-get (name (model model))
  "Get the interpretation associated with the given name from the given model."
  (with-slots (context) model
    (let ((const-decl (loop for i below (z3-model-get-num-consts context model)
                            for decl = (z3-model-get-const-decl context model i)
                            if (string= (z3-get-symbol-string context (z3-get-decl-name context decl))
                                        (symbol-name name))
                            return decl)))
      (if const-decl
          (make-instance 'ast :handle (z3-model-get-const-interp context model const-decl) :context context)
        (let ((func-decl (loop for i below (z3-model-get-num-funcs context model)
                               for decl = (z3-model-get-func-decl context model i)
                               if (string= (z3-get-symbol-string context (z3-get-decl-name context decl))
                                           (symbol-name name))
                               return decl)))
          (if func-decl
              (make-instance 'func-interp :handle (z3-model-get-func-interp context model func-decl) :context context)
            (error "No assignment found for name ~a in the given model." name)))))))

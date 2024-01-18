(defpackage #:trivial-indent
  (:use #:cl)
  (:nicknames #:org.tymoonnext.radiance.lib.trivial-indent #:indent)
  (:export
   #:indentation
   #:define-indentation
   #:remove-indentation
   #:initialize-slime
   #:initialize-sly))

(in-package #:org.tymoonnext.radiance.lib.trivial-indent)

(defvar *indentation-hints* (make-hash-table :test #'eq))

(defmacro with-symbol ((name symbol package module) &body body)
  "Check if SYMBOL exists in PACKAGE when MODULE is loaded and bind it to NAME."
  (let ((pkg (gensym)))
    `(when (member ,module *modules* :test #'string=)
       (let* ((,pkg (find-package ,package))
              (,name (when ,pkg (find-symbol (string ,symbol) ,pkg))))
         (when ,name
           ,@body)))))

(defun indentation (symbol)
  "Returns the custom defined indentation of a symbol if there is any. SETF-able."
  (gethash symbol *indentation-hints*))

(defun (setf indentation) (rule-form symbol)
  "Sets the indentation hint for a symbol."
  (initialize-slime)
  (initialize-sly)
  (setf (gethash symbol *indentation-hints*) rule-form)
  (with-symbol (update '#:update-indentation-information :swank "SWANK-INDENTATION")
    (funcall (symbol-function update)))
  (with-symbol (update '#:update-indentation-information :slynk "SLYNK/INDENTATION")
    (funcall (symbol-function update)))
  rule-form)

(defmacro define-indentation (symbol rule-form)
  "Define an indentation hint for a symbol.

See the SLIME/SWANK documentation for more information on the rules.
Example: (define-indentation defmacro (4 &lambda &body))"
  (assert (symbolp symbol))
  (assert (listp rule-form))
  `(setf (indentation ',symbol) ',rule-form))

(defun remove-indentation (symbol)
  "Remove the indentation hint for a symbol."
  (initialize-slime)
  (initialize-sly)
  (remhash symbol *indentation-hints*)
  (with-symbol (update '#:update-indentation-information :swank "SWANK-INDENTATION")
    (funcall (symbol-function update)))
  (with-symbol (update '#:update-indentation-information :slynk "SLYNK/INDENTATION")
    (funcall (symbol-function update)))
  symbol)

(defun initialize-slime ()
  "Attempts to initialize slime with our indentation table.
If SWANK-INDENTATION is not loaded, this does nothing.
It should be safe to call this function regardless of whether
SWANK is loaded at all or not.

This is automatically called when TRIVIAL-INDENT is loaded."
  (with-symbol (tables '#:*application-hints-tables* :swank "SWANK-INDENTATION")
    (set tables (cons *indentation-hints* (remove *indentation-hints* (symbol-value tables))))
    t))

(defun initialize-sly ()
  "Attempts to initialize sly with our indentation table.
If SLYNK/INDENTATION is not loaded, this does nothing.
It should be safe to call this function regardless of whether
SLYNK is loaded at all or not.

This is automatically called when TRIVIAL-INDENT is loaded."
  (with-symbol (tables '#:*application-hints-tables* :slynk "SLYNK/INDENTATION")
    (set tables (cons *indentation-hints* (remove *indentation-hints* (symbol-value tables))))
    t))

(initialize-slime)
(initialize-sly)

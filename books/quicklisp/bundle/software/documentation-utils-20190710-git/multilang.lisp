#|
 This file is a part of documentation-utils
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.documentation-utils)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass multilang-formatter (documentation-formatter)
    ())

  (defmethod format-documentation ((formatter multilang-formatter) type var documentation)
    (let* ((documentation (etypecase documentation
                            (string (list (multilang-documentation:identifier multilang-documentation:*language*)
                                          documentation))
                            (cons documentation)))
           (docform (funcall (documentation-translator type) var))
           (default (loop for (lang docstring) on documentation by #'cddr
                          do (when (eq (multilang-documentation:language lang)
                                       multilang-documentation:*language*)
                               (return docstring))
                          finally (return (second docstring)))))
      (cond ((eq (first docform) 'documentation)
             `(progn
                ,@(loop for (lang docstring) on documentation by #'cddr
                        collect `(setf (multilang-documentation:documentation ,@(rest docform) :lang ',lang)
                                       ,docstring))
                ,default))
            (T
             (warn "Don't know how to deal with ~s. Can't expand to multilang definition." docform)
             default))))

  (export 'multilang-formatter))

(define-docs
  :formatter docs:multilang-formatter
  (type multilang-formatter
    (:en "This formatter allows specifying docstrings for multiple languages at once.

The docstring should be either just a single string like
always, in which case it is used for the default language,
or it should be a plist of languages and docstrings.

See DOCUMENTATION-FORMATTER
See MULTILANG-DOCUMENTATION:*LANGUAGE*
See MULTILANG-DOCUMENTATION:DOCUMENTATION"
     :jp "このformatterは複数の語のdocstring許します。

DOCUMENTATION-FORMATTER を参照
MULTILANG-DOCUMENTATION:*LANGUAGE* を参照
MULTILANG-DOCUMENTATION:DOCUMENTATION を参照")))


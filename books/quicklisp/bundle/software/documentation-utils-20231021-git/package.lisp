(in-package #:cl-user)
(defpackage #:documentation-utils
  (:nicknames #:docs #:org.shirakumo.documentation-utils)
  (:use #:cl)
  (:export
   #:*documentation-tests*
   #:documentation-test
   #:remove-documentation-test
   #:define-documentation-test
   #:*documentation-translators*
   #:documentation-translator
   #:remove-documentation-translator
   #:define-documentation-translator
   #:define-documentation-alias
   #:check
   #:*default-formatter*
   #:documentation-formatter
   #:format-documentation
   #:basic-formatter
   #:define-docs))

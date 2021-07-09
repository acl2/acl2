; A tool to get info about a method
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "classes")
(include-book "class-tables")
(include-book "method-designator-strings")

;; TODO: Deprecate:
(defun acl2::get-method-info-fn (method-designator-string state)
  (declare (xargs :stobjs state :verify-guards nil))
  (let ((class (acl2::extract-method-class method-designator-string))
        (name (acl2::extract-method-name method-designator-string))
        (desc (acl2::extract-method-descriptor method-designator-string)))
    (acl2::lookup-equal (cons name desc) (class-decl-methods (acl2::lookup-equal class (acl2::global-class-alist state))))))

;; TODO: Deprecate:
;; Get the info for the given method from the global class table.
(defmacro acl2::get-method-info (method-designator-string)
  `(acl2::get-method-info-fn ,method-designator-string state))

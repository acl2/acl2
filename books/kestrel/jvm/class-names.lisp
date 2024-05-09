; Class-names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "kestrel/utilities/string-contains-charp" :dir :system)
(include-book "kestrel/utilities/string-utilities" :dir :system) ; for substring-before-last-occurrence

(defund class-namep (name) (declare (xargs :guard t)) (stringp name))

;TODO: use this more instead of stringp and also, in many cases, instead of class-namep:
(defund class-or-interface-namep (name) (declare (xargs :guard t)) (stringp name))

(defthm class-or-interface-namep-forward-to-stringp
  (implies (class-or-interface-namep name)
           (stringp name))
  :rule-classes :forward-chaining)

;; Returns a string or :unnamed-package
(defun extract-package-name-from-class-name (class-name)
  (declare (xargs :guard (class-namep class-name)))
  (if (acl2::string-contains-charp class-name #\.)
      (acl2::substring-before-last-occurrence class-name #\.)
    :unnamed-package))

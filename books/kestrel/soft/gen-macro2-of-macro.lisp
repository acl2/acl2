; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "defsoft")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ gen-macro2-of-macro (macro)
  (declare (xargs :guard (symbolp macro)))
  :parents (soft-implementation)
  :short "Generate a second-order counterpart of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "SOFT provides second-order counterparts of a number of event macros.
     For instance, it provides @(tsee defun2)
     as a second-order counterpart of @(tsee defun).
     These second-order macros are implemented as simply
     their first-order counterparts followed by @(tsee defsoft).
     Since their implementation has such a simple and regular structure,
     we capture it in this ``meta'' macro,
     which you use to generate the second-order macros."))
  (b* ((macro2 (str::cat (symbol-name macro) "2"))
       (softmacro2 (intern$ macro2 "SOFT"))
       (acl2macro2 (intern$ macro2 "ACL2"))
       (macro2-string (str::downcase-string (symbol-name softmacro2)))
       (acl2macro2-string (str::cat "acl2::" macro2-string)))
    `(defsection ,(intern$ (str::cat macro2 "-IMPLEMENTATION") "SOFT")
       :parents (soft-implementation ,softmacro2)
       :short ,(str::cat "Implementation of @(tsee " macro2-string ").")
       :long ,(str::cat "@(def " macro2-string ") @(def " acl2macro2-string ")")
       (defmacro ,softmacro2 (sofun &rest rest)
         (list 'progn
               (list* ',macro sofun rest)
               (list 'defsoft sofun)))
       (defmacro ,acl2macro2 (&rest args)
         (list* ',softmacro2 args)))))

; Event Forms
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-forms
  :parents (kestrel-utilities system-utilities)
  :short "Utilities for event forms.")

(define pseudo-event-formp (x)
  :returns (yes/no booleanp)
  :parents (event-forms)
  :short "Recognize the basic structure of an event form."
  :long
  "<p>
   Check whether @('x') is a non-empty true list that starts with a symbol
   (like a function or macro call).
   </p>
   <p>
   This is a shallow check.
   Its satisfaction does not guarantee that @('x') is a valid event form.
   </p>"
  (and x
       (true-listp x)
       (symbolp (car x)))

  ///

  (defrule pseudo-event-formp-of-cons
    (equal (pseudo-event-formp (cons a b))
           (and (symbolp a)
                (true-listp b)))))

(std::deflist pseudo-event-form-listp (x)
  (pseudo-event-formp x)
  :parents (event-forms)
  :short "Recognize true lists whose elements all have the
          <see topic='@(url pseudo-event-formp)'>basic structure
          of an event form</see>."
  :true-listp t
  :elementp-of-nil nil)

(define function-intro-macro
  ((enable booleanp "Enable function or not.")
   (non-executable booleanp "Make function non-executable or not."))
  :returns (macro (member-eq macro '(defun defund defun-nx defund-nx)))
  :parents (event-forms)
  :short "Macro (name) for introducing a function
          with given enablement and non-executability."
  (if enable
      (if non-executable
          'defun-nx
        'defun)
    (if non-executable
        'defund-nx
      'defund)))

(define theorem-intro-macro ((enable booleanp "Enable theorem or not."))
  :returns (macro (member-eq macro '(defthm defthmd)))
  :parents (event-forms)
  :short "Macro (name) for introducing a theorem with a given enablement."
  (if enable
      'defthm
    'defthmd))

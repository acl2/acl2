; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-eval-to")
(include-book "must-eval-to-t")
(include-book "must-succeed")
(include-book "must-succeed-star")
(include-book "must-fail")
(include-book "must-fail-local")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Event-Level Evaluation

; Here we define macros that employ make-event to check evaluations of forms.
; See community book make-event/eval-tests.lisp (and many other .lisp files in
; that directory) for how these macros may be employed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-error
  :parents (std/testing errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that an error occurs."

  :long "<p>Evaluation of @('(must-fail-with-error <form>)') returns without
 error exactly when evaluation of @('<form>') causes an error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-error)

 <p>Also see @(see must-fail-with-soft-error) and
 @(see must-fail-with-hard-error).</p>"

  (defmacro must-fail-with-error (form &rest args)
    (list* 'must-fail form :expected :any args)))

;; deprecated:

(defsection ensure-error
  :parents (must-fail-with-error)
  :short "Deprecated synonym of @(tsee must-fail-with-error)"
  (defmacro ensure-error (&rest args)
    `(must-fail-with-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-soft-error
  :parents (std/testing errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that
          a soft error occurs."

  :long "<p>Evaluation of @('(must-fail-with-soft-error <form>)') returns
 without error exactly when evaluation of @('<form>') causes a soft error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-soft-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-soft-error)

 <p>Also see @(see must-fail-with-error) and
 @(see must-fail-with-hard-error).</p>"

  (defmacro must-fail-with-soft-error (form &rest args)
    (list* 'must-fail form :expected :soft args)))

;; deprecated:

(defsection ensure-soft-error
  :parents (must-fail-with-soft-error)
  :short "Deprecated synonym of @(tsee must-fail-with-soft-error)"
  (defmacro ensure-soft-error (&rest args)
    `(must-fail-with-soft-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-hard-error
  :parents (std/testing errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that
          a hard error occurs."

  :long "<p>Evaluation of @('(must-fail-with-hard-error <form>)') returns
 without error exactly when evaluation of @('<form>') causes a hard error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-hard-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-hard-error)

 <p>Also see @(see must-fail-with-error) and
 @(see must-fail-with-soft-error).</p>"

  (defmacro must-fail-with-hard-error (form &rest args)
    (list* 'must-fail form :expected :hard args)))

;; deprecated:

(defsection ensure-hard-error
  :parents (must-fail-with-hard-error)
  :short "Deprecated synonym of @(tsee must-fail-with-hard-error)"
  (defmacro ensure-hard-error (&rest args)
    `(must-fail-with-hard-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-prove
  :parents (std/testing errors)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula gets proved."
  :long
  "<p>
   This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-succeed).
   </p>
   @(def must-prove)"

  (defmacro must-prove (&rest args)
    `(must-succeed (thm ,@args))))

;; deprecated:

(defsection thm?
  :parents (must-prove)
  :short "Deprecated synonym of @(tsee must-prove)."
  (defmacro thm? (&rest args)
    `(must-prove ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-not-prove
  :parents (std/testing errors)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula does not get proved."
  :long
  "<p>
   This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-fail).
   </p>
   @(def must-not-prove)"

  (defmacro must-not-prove (&rest args)
    `(must-fail (thm ,@args))))

;; deprecated:

(defsection not-thm?
  :parents (must-not-prove)
  :short "Deprecated synonym of @(tsee must-not-prove)."
  (defmacro not-thm? (&rest args)
    `(must-not-prove ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-be-redundant
  :parents (std/testing errors)
  :short "A top-level @(tsee assert$)-like command
          to ensure that given forms are redundant."
  :long
  "<p>
   The forms are put into an @(tsee encapsulate),
   along with a @(tsee set-enforce-redundancy) command that precedes them.
   </p>
   @(def must-be-redundant)"
  (defmacro must-be-redundant (&rest forms)
    `(encapsulate
       ()
       (set-enforce-redundancy t)
       ,@forms)))

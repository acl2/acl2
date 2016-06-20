; Testing Facilities
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains macros for building tests,
; related to MUST-SUCCEED and MUST-FAIL.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-event/eval-check" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-succeed*

  :parents (kestrel-general-utilities errors)

  :short
  "A variant of @(tsee must-succeed)
  that takes multiple forms
  and uses default options."

  :long
  "<p>
  The forms must be
  <see topic='@(url embedded-event-form)'>embedded event forms</see>,
  because they are put into a @(tsee progn)
  so that earlier forms are evaluated
  before considering later forms in the sequence.
  This is a difference with @(tsee must-succeed),
  whose form is required to return
  an <see topic='@(url error-triple)'>error triple</see>
  without necessarily being an embedded event form;
  since @(tsee must-succeed) takes only one form,
  there is no issue of earlier forms being evaluated
  before considering later forms
  as in @(tsee must-succeed*).
  </p>
  @(def must-succeed*)"

  (defmacro must-succeed* (&rest forms)
    `(must-succeed (progn ,@forms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-succeed**

  :parents (kestrel-general-utilities errors)

  :short
  "A variant of @(tsee must-succeed)
  that takes multiple forms
  and explicit options."

  :long
  "<p>
  The first two arguments are
  the @(':with-output-off') and @(':check-expansion') options
  of @(tsee must-succeed).
  The remaining arguments are the forms.
  </p>
  <p>
  As in @(tsee must-succeed*), the forms must be
  <see topic='@(url embedded-event-form)'>embedded event forms</see>.
  See the discussion for @(tsee must-succeed*) in this regard.
  </p>
  @(def must-succeed**)"

  (defmacro must-succeed** (with-output-off check-expansion &rest forms)
    `(must-succeed (progn ,@forms)
                   :with-output-off ,with-output-off
                   :check-expansion ,check-expansion)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-be-redundant

  :parents (kestrel-general-utilities errors)

  :short
  "A top-level @(tsee assert$)-like command
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-local

  :parents (kestrel-general-utilities errors)

  :short "A @(see local) variant of @(tsee must-fail)."

  :long
  "<p>
  This is useful to overcome the problem discussed in the caveat
  in the documentation of @(tsee must-fail).
  </p>
  @(def must-fail-local)"

  (defmacro must-fail-local (&rest args)
    `(local (must-fail ,@args))))

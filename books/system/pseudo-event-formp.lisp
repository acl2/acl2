; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defsection pseudo-event-formp
  :parents (system-utilities-non-built-in)
  :short "Recognize well-formed event forms."
  :long
  "<p>Here we formalize some constraints on untranslated event forms.
      Because of macros it is almost impossible
      to put constraints on event forms.
      For example, with an appropriate @(tsee defmacro) of @('barf'),
      this could be a form @('(barf (1 . 2))').
      But even macros have to be symbols and take a true list of args.
      So we know that much at the top but all bets are off after that.</p>
   <p>The most rigorous test would translate the alleged form,
      but that would require state
      and the specification of translate's many options
      like whether stobjs are treated specially.
      Until we need it,
      we are not going to try to formalize the stronger test.</p>"

  (defun pseudo-event-formp (x)
    (declare (xargs :guard t))
    (and (consp x)
         (true-listp x)
         (symbolp (car x))))) ; This symbolp could be a macro or a function.

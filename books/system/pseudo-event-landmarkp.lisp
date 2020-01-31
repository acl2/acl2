; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributions by Alessandro Coglio

(in-package "ACL2")

(include-book "pseudo-event-formp")
(include-book "std/typed-lists/string-or-symbol-listp" :dir :system)

(defsection pseudo-event-landmarkp
  :parents (system-utilities-non-built-in)
  :short "Recognize event landmarks in the ACL2 @(see world)."
  :long
  "<p>Discussions of event landmarks may be found
      in the comment in @('make-event-tuple') in the ACL2 sources
      and in the comment, labeled `Event Tuples',
      above @('make-event-tuple').</p>"

  (defun pseudo-event-landmarkp (val)
    (declare (xargs :guard t))
    (or (equal val '(-1 ((NIL) 0)))   ; bogus tuple by primordial-world-globals
        (and (consp val)
             (or (natp (car val))       ; n = (car val), d = 0
                 (and (consp (car val))
                      (natp (car (car val)))  ; = n
                      (natp (cdr (car val))))) ; = d
             (consp (cdr val))
             (if (symbolp (cadr val))    ; ev-type is recoverable from form
                 (pseudo-event-formp (cdr val))  ; (cdr val) here is the event form
               (and (consp (cadr val))
                    (consp (car (cadr val))) ; (ev-type . skipped-proofs-p)
                    (symbolp (car (car (cadr val)))) ; ev-type
                    (booleanp (cdr (car (cadr val)))) ; skipped-proofs-p
                    (consp (cdr (cadr val)))
                    (or (symbolp (cadr (cadr val))) ; name introduced
                        (stringp (cadr (cadr val))) ; name introduced
                        (equal 0 (cadr (cadr val))) ; no names introduced
                        (string-or-symbol-listp (cadr (cadr val)))) ; list of names introduced
                    (member-eq (cddr (cadr val)) ; symbol-class
                               '(nil :program :ideal :common-lisp-compliant))
                    (pseudo-event-formp (cddr val)))))))) ; (cddr val) here is the event form

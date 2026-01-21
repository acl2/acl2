; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc eval-events-from-file
  :parents (macro-libraries io)
  :short "Create an event that evaluates events from a file"
  :long "<p>The form @('(eval-events-from-file filename)') reads the forms from
 the file named by the string, @('filename'), which should all be embedded
 @(see event) forms.  It then generates and evaluates those events.  Note that
 the package used for reading those forms is the current package at the time
 @('eval-events-from-file' is invoked; the file given by @('filename') should
 <b>not</b> start with an @(tsee in-package) form.</p>

 <p>Implementation details that can be ignored: The implementation reads the
 events and wraps them in a call of @(tsee progn), and passes that call to
 @(tsee make-event).</p>")


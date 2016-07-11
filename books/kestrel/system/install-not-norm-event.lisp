; Non-Normalized Definition Installation Event
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides a utility to create an event
; that installs a non-normalized definition of a function.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/system/event-forms" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define install-not-norm-event
  ((f symbolp "Function to install the non-normalized definition of.")
   (local booleanp "Make the event form local or not."))
  :returns (mv (f$not-normalized symbolp)
               (event-form pseudo-event-formp))
  :parents (kestrel-system-utilities system-utilities install-not-normalized)
  :short
  "Generate event form for
  <see topic='@(url install-not-normalized)'
  >installing a non-normalized definition</see>
  of @('f')."
  :long
  "<p>
  Besides the event form,
  also return the name @('f$not-normalized')
  of the theorem that installs the non-normalized definition.
  </p>"
  (b* ((f$not-normalized (intern-in-package-of-symbol
                          (symbol-name (packn (list f '$not-normalized)))
                          f))
       (event-form (if local
                       `(local (install-not-normalized ,f))
                     `(install-not-normalized ,f))))
    (mv f$not-normalized event-form)))

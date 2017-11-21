; Non-Normalized Definition Installation Event
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "misc/install-not-normalized" :dir :system)
(include-book "event-forms")
(include-book "fresh-names")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define install-not-norm-event
  ((fn symbolp "Function to install the non-normalized definition of.")
   (local booleanp "Make the event form local or not.")
   (names-to-avoid symbol-listp "Avoid these as theorem name.")
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp): the name of the theorem."))
  :mode :program
  :parents (kestrel-utilities system-utilities install-not-normalized)
  :short "Create an event form to
          <see topic='@(url install-not-normalized)'>install
          the non-normalized definition</see>
          of a function,
          ensuring that the name of the theorem will not cause a conflict."
  :long
  "<p>
   Ensure that the name of the theorem is not already in use
   and is not among a list of names to avoid.
   Start with the default name
   (i.e. the concatenation of
   the name of @('fn') with @('$not-normalized'))
   and ensure its uniqueness via @(tsee fresh-name-in-world-with-$s).
   </p>"
  (b* ((name (install-not-normalized-name fn))
       (name (fresh-name-in-world-with-$s name names-to-avoid wrld))
       (event (if local
                  `(local (install-not-normalized ,fn :defthm-name ',name))
                `(install-not-normalized ,fn :defthm-name ',name))))
    (mv event name)))

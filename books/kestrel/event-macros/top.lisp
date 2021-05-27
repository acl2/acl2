; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "applicability-conditions")
(include-book "cw-event")
(include-book "definedness")
(include-book "event-generation")
(include-book "event-generation-soft")
(include-book "input-processing")
(include-book "intro-macros")
(include-book "make-event-terse")
(include-book "proof-preparation")
(include-book "restore-output")
(include-book "results")
(include-book "screen-printing")
(include-book "template-generators")
(include-book "try-event")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macros
  :parents (macro-libraries kestrel-books)
  :short "A library of concepts and utilities for event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Event macros are macros at the event level.
     ACL2 provides several such macros
     (e.g. @(tsee defun), @(tsee defthm), @(tsee defun-sk)),
     and many more such macros are provided by the community books
     (e.g. @(tsee std::deflist), @(tsee fty::defprod), @(tsee apt::tailrec)).
     Event macros often generate events (via other event macros),
     and sometimes generate files (e.g. @(tsee java::atj), @(tsee c::atc)).")
   (xdoc::p
    "Amid the wide variety of these event macros,
     there are certain commonalities.
     The code and documentation in this directory
     provide utilities and concepts useful to
     develop and document event macros more quickly and consistently,
     based on those commonalities.")))

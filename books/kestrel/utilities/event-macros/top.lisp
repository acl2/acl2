; Event Macros
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc-constructors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macros
  :parents (macro-libraries system-utilities)
  :short "Concepts and utilities for event macros."
  :long
  (xdoc::topapp
   (xdoc::p
    "Event macros are macros at the event level.
     ACL2 provides several such macros
     (e.g. @(tsee defun), @(tsee defthm), @(tsee defun-sk)),
     and many more such macros are provided by the community books
     (e.g. @(tsee std::deflist), @(tsee fty::defprod), @(tsee apt::tailrec)).")
   (xdoc::p
    "Amid the wide variety of these event macros,
     there are certain commonalities.
     The code and documentation in this directory
     provide utilities and concepts useful to
     develop and document event macros more quickly and consistently,
     based on those commonalities.")))

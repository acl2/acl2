; System Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-vars-theorems")
(include-book "arglistp-theorems")
(include-book "defchoose-queries")
(include-book "defun-sk-queries")
(include-book "event-forms")
(include-book "fresh-names")
(include-book "install-not-norm-event")
(include-book "named-formulas")
(include-book "numbered-names")
(include-book "paired-names")
(include-book "terms")
(include-book "world-queries")
(include-book "world-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc system-utilities-non-built-in
  :parents (kestrel-utilities system-utilities)
  :short "System utilities related to the ACL2 system."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are useful for system programming,
     e.g. to build tools that generate new events
     based on existing events.")
   (xdoc::p
    "These (non-built-in) utilities complement the
     <see topic='@(url system-utilities)'>built-in system utilities</see>.")))

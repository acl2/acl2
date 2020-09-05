; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "defunvar")
(include-book "defsoft")
(include-book "defun-inst")
(include-book "defthm-inst")

(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/std/system/fundef-enabledp" :dir :system)
(include-book "kestrel/std/system/guard-verified-p" :dir :system)
(include-book "kestrel/std/system/irecursivep" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-implementation
  :parents (soft)
  :short "Implementation of SOFT."
  :order-subtopics t
  :default-parent t)

(gen-macro2-of-macro defun)

(gen-macro2-of-macro defund)

(gen-macro2-of-macro defchoose)

(gen-macro2-of-macro defun-sk)

(gen-macro2-of-macro define)

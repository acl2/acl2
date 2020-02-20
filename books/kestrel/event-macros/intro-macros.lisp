; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-intro-macros
  :parents (event-macros)
  :short "Utilities to determine the (names of) macros
          to use to introduce certain events."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define function-intro-macro
  ((enable booleanp "Enable function or not.")
   (non-executable booleanp "Make function non-executable or not."))
  :returns (macro (member-eq macro '(defun defund defun-nx defund-nx)))
  :short "Macro (name) for introducing a function
          with given enablement and non-executability."
  (if enable
      (if non-executable
          'defun-nx
        'defun)
    (if non-executable
        'defund-nx
      'defund)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define theorem-intro-macro ((enable booleanp "Enable theorem or not."))
  :returns (macro (member-eq macro '(defthm defthmd)))
  :short "Macro (name) for introducing a theorem with a given enablement."
  (if enable
      'defthm
    'defthmd))

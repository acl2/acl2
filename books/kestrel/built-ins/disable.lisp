; Built-Ins Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "collect")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We provide event macros to easily disable built-in functions and rules.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Macro to disable all the built-in logic-mode functions.
; It turns out that not all of them actually correspond to rules,
; and attempting to disable them causes an error.
; The error tells us which functions cannot be disabled,
; so we remove them from the list,
; defining a named constant for the functions that can be disabled,
; and we use the latter in the macro.

(defconst *builtin-logic-defun-names-that-can-be-disabled*
  (set-difference-eq *builtin-logic-defun-names*
                     '(ancestors-check
                       oncep-tp
                       too-many-ifs-pre-rewrite
                       too-many-ifs-post-rewrite
                       initialize-event-user
                       finalize-event-user
                       print-clause-id-okp
                       canonical-pathname
                       acl2x-expansion-alist
                       magic-ev-fncall
                       set-ld-history-entry-user-data
                       mfc-ap-fn
                       mfc-relieve-hyp-fn
                       mfc-relieve-hyp-ttree
                       mfc-rw+-fn
                       mfc-rw+-ttree
                       mfc-rw-fn
                       mfc-rw-ttree
                       mfc-ts-fn
                       mfc-ts-ttree)))

(defmacro disable-builtin-logic-defuns ()
  `(in-theory (disable ,@*builtin-logic-defun-names-that-can-be-disabled*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We could provide additional disabling macros in the future.

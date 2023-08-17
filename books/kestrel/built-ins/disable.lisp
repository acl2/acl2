; Built-Ins Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
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

; List of all the built-in logic-mode functions that can be disabled.
; It turns out that not all of the built-in logic-mode functions
; can be disabled; attempting to disable them causes an error.
; The error tells us which functions cannot be disabled,
; so we remove them from the list,
; defining a named constant for the functions that can be disabled.

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
                       mfc-ts-ttree
                       brkpt1-brr-data-entry
                       brkpt2-brr-data-entry
                       update-brr-data-1
                       update-brr-data-2
                       brr-near-missp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Macro to disable all the built-in logic-mode functions that can be disabled.

(defmacro disable-all-builtin-logic-defuns ()
  `(in-theory (disable ,@*builtin-logic-defun-names-that-can-be-disabled*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some built-in logic-mode functions are logical synonyms of others,
; motivated by execution efficiency.
; Those should be normally enabled,
; so they are replaced by the ones that they are synonyms of.
; Thus we define a macro to disable all the built-in logic-mode functions
; except some that are synonyms in the sense above.
; We use a whitelist approach to letting these functions enabled:
; that is, we have an explicit list of such functions
; that we remove from the constant defined above,
; which lists all the built-in logic-mode functions that can be disabled.

; We start with the following whitelisted functions:
; - The specialized equality functions, synonyms of EQUAL;
;   we also include /=, even though technically it is not a synonym,
;   but an abbreviation of (NOT (EQUAL ...)),
;   which we normally want to expose as such.
;  We may add more in the future.

(defmacro disable-most-builtin-logic-defuns ()
  `(in-theory (disable ,@(set-difference-eq
                          *builtin-logic-defun-names-that-can-be-disabled*
                          '(=
                            /=
                            eq
                            eql)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List of all the built-in rewrite rules that rewrite
; generic calls of certain built-in functions
; (i.e. calls on distinct variables)
; to something simpler according to how those function treat
; values outside the intended domain,
; provided suitable hypotheses are satisfied
; that say that the arguments are outside the domain.

(defconst *builtin-rewrite-rules-for-defaults*
  '(default-car
    default-cdr
    default-numerator
    default-denominator
    default-realpart
    default-imagpart
    default-code-char
    default-char-code
    default-coerce-1
    default-coerce-2
    default-coerce-3
    default-complex-1
    default-complex-2
    default-unary-minus
    default-unary-/
    default-+-1
    default-+-2
    default-*-1
    default-*-2
    default-<-1
    default-<-2
    default-intern-in-package-of-symbol
    default-pkg-imports))

(assert-event (subsetp-eq *builtin-rewrite-rules-for-defaults*
                          *builtin-rewrite-defaxiom/defthm-names*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro disable-builtin-rewrite-rules-for-defaults ()
  `(in-theory (disable ,@*builtin-rewrite-rules-for-defaults*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We could provide additional disabling macros in the future.

; System Utilities -- Term Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/all-lambdas" :dir :system)
(include-book "kestrel/std/system/all-non-gv-exec-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/all-non-gv-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/all-pkg-names" :dir :system)
(include-book "kestrel/std/system/all-program-ffn-symbs" :dir :system)
(include-book "kestrel/std/system/apply-term" :dir :system)
(include-book "kestrel/std/system/apply-terms-same-args" :dir :system)
(include-book "kestrel/std/system/apply-unary-to-terms" :dir :system)
(include-book "kestrel/std/system/check-user-lambda" :dir :system)
(include-book "kestrel/std/system/check-user-term" :dir :system)
(include-book "kestrel/std/system/fapply-term" :dir :system)
(include-book "kestrel/std/system/fapply-terms-same-args" :dir :system)
(include-book "kestrel/std/system/fapply-unary-to-terms" :dir :system)
(include-book "kestrel/std/system/fsublis-fn" :dir :system)
(include-book "kestrel/std/system/fsublis-var" :dir :system)
(include-book "kestrel/std/system/guard-verified-exec-fnsp" :dir :system)
(include-book "kestrel/std/system/guard-verified-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-closedp" :dir :system)
(include-book "kestrel/std/system/lambda-guard-verified-exec-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-guard-verified-fnsp" :dir :system)
(include-book "kestrel/std/system/lambda-logic-fnsp" :dir :system)
(include-book "kestrel/std/system/term-function-recognizers" :dir :system)
(include-book "kestrel/std/system/term-guard-obligation" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "world-queries")

(local (include-book "all-vars-theorems"))
(local (include-book "world-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc term-utilities
  :parents (system-utilities-non-built-in)
  :short "Utilities for @(see term)s.")

(define all-vars-in-untranslated-term (x (wrld plist-worldp))
  :returns (term "A @(tsee pseudo-termp).")
  :mode :program
  :parents (term-utilities)
  :short "The variables free in the given untranslated term."
  :long
  "<p>
   This function returns the variables of the given untranslated term.  They
   are returned in reverse order of print occurrence, for consistency with the
   function, @(tsee all-vars).
   </p>
   <p>
   The input is translated for reasoning, so restrictions for executability are
   not enforced.  There is also no restriction on the input being in
   @(':')@(tsee logic) mode.
   </p>"
  (let ((ctx 'all-vars-in-untranslated-term))
    (mv-let (erp term)
      (translate-cmp x
                     t ; stobjs-out
                     nil ; logic-modep (not required)
                     nil ; known-stobjs
                     ctx
                     wrld
                     (default-state-vars nil))
      (cond (erp (er hard erp "~@0" term))
            (t (all-vars term))))))

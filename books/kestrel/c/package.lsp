; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "C" (append
             (set-difference-eq *std-pkg-symbols*
                                '(assign
                                  boolean
                                  byte
                                  error
                                  pi
                                  pprint-indent
                                  schar
                                  type
                                  typep
                                  value))
             '(alist-to-doublets
               any
               bool
               check-if-call
               check-lambda-call
               check-list-call
               check-mbt-call
               check-mbt$-call
               check-mv-let-call
               conjoin
               ctxp
               cw-event
               define-sk
               defmacro+
               defopener
               defopeners
               defopeners-names
               deftutorial
               defxdoc+
               doublet-listp
               e/d*
               enable*
               er-soft+
               evmac-appcond-listp
               evmac-appcond-theorem-list
               evmac-generate-defthm
               evmac-generate-defun
               evmac-input-print->=
               evmac-input-print-p
               evmac-prepare-proofs
               evmac-process-input-print
               fargn
               fargs
               fcons-term
               ffn-symb
               flambda-applicationp
               flatten-ands-in-lit
               formals+
               fquotep
               fresh-logical-name-with-$s-suffix
               fsubcor-var
               fsublis-var-lst
               genvar
               get-ruleset
               implode
               impossible
               irecursivep+
               keyword-listp
               keyword-symbol-alistp
               lnfix
               make-event-terse
               make-evmac-appcond
               maybe-pseudo-event-formp
               mbt$
               measure+
               msg-listp
               mv-nth-of-cons
               nat
               nvariablep
               packn-pos
               pos-listp
               pseudo-event-form-listp
               pseudo-event-formp
               remove-equal-formals-actuals
               restore-output?
               run-when
               str-fix
               symbol-fix
               symbol-symbol-alistp
               tuple
               ubody+
               uguard
               uguard+
               untranslate-lst
               variablep
               std::defret-mutual)))

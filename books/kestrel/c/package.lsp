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
                                '(byte
                                  error
                                  pi
                                  pprint-indent
                                  schar
                                  type
                                  typep
                                  value))
             '(any
               bool
               bool-resultp
               cw-event
               define-sk
               defmacro+
               defopener
               defopeners
               defopeners-names
               deftutorial
               defxdoc+
               e/d*
               enable*
               er-soft+
               evmac-generate-defthm
               evmac-input-print->=
               evmac-input-print-p
               evmac-prepare-proofs
               evmac-process-input-print
               flatten-ands-in-lit
               get-ruleset
               implode
               impossible
               int
               lnfix
               make-event-terse
               maybe-pseudo-event-formp
               mbt$
               msg-listp
               nat
               patbind-bool-result-err ; workaround for an XDOC bug
               patbind-bool-result-ok ; workaround for an XDOC bug
               patbind-int-result-err ; workaround for an XDOC bug
               patbind-int-result-ok ; workaround for an XDOC bug
               pos-listp
               pseudo-event-form-listp
               pseudo-event-formp
               run-when
               symbol-symbol-alistp
               tuple
               std::defret-mutual)))

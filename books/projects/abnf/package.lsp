; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "kestrel/java/portcullis" :dir :system)
(include-book "kestrel/yul/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ABNF" (set-difference-eq
                (append *std-pkg-symbols*
                        '(add-const-to-untranslate-preprocess
                          alpha/digit/dash-charlist-p
                          bool
                          char-fix
                          chars=>nats
                          constant-namep
                          constant-value
                          cw-event
                          defmacro+
                          defxdoc+
                          ensure-symbol-is-fresh-event-name$
                          ensure-value-is-boolean$
                          ensure-value-is-constant-name$
                          ensure-value-is-string$
                          ensure-value-is-symbol$
                          er-soft+
                          erp
                          evmac-input-print-p
                          evmac-input-print-<
                          evmac-input-print-<=
                          evmac-input-print->
                          evmac-input-print->=
                          explode
                          fun
                          implode
                          integers-from-to
                          keyword-listp
                          known-packages+
                          legal-constantp
                          lnfix
                          make-event-terse
                          maybe-msgp
                          maybe-natp
                          msgp
                          nat
                          nati
                          nati-case
                          nati-finite
                          nati-finite->get
                          nati-infinity
                          natip
                          nat-list
                          nat-list-fix
                          nat-resultp
                          nat-list-resultp
                          nats=>chars
                          nats=>string
                          packn-pos
                          patbind-fun
                          pos-list
                          pos-listp
                          pseudo-event-formp
                          pseudo-event-form-listp
                          read-file-characters
                          restore-output?
                          reterr
                          retok
                          return-raw
                          seq
                          seq-backtrack
                          string=>nats
                          string-symbol-alistp
                          string-symbollist-alistp
                          symbol-pseudoeventform-alist
                          symbol-pseudoeventform-alistp
                          table-alist+
                          unsigned-byte-listp
                          fty::okf
                          fty::reserrf
                          fty::reserrf-push
                          fty::reserrp
                          set::list-in
                          set::nat-setp
                          std::define-sk
                          str::downcase-char
                          str::downcase-charlist
                          str::str-fix
                          str::upcase-char))
                '(closure
                  rule
                  symbol
                  symbolp
                  string
                  stringp)))

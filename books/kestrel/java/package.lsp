; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "JAVA" (append *std-pkg-symbols*
                       '(*pkg-witness-name*
                         *primitive-formals-and-guards*
                         access-event-tuple-namex
                         access-event-tuple-type
                         all-ffn-symbs
                         all-pkgs-in-world
                         alpha/digit-chars
                         alpha/digit/dash-charlist-p
                         alpha/digit/uscore/dollar-charlist-p
                         alpha/uscore/dollar-char-p
                         bad-atom<=
                         body
                         bool
                         char-downcase
                         char-upcase
                         chars=>nats
                         defxdoc+
                         doublets-to-alist
                         ensure-boolean$
                         ensure-doublet-list$
                         ensure-function-name$
                         ensure-function-name-list$
                         ensure-list-functions$
                         ensure-list-no-duplicates$
                         ensure-member-of-list$
                         ensure-string$
                         ensure-string-or-nil$
                         ensure-term$
                         ensure-term-ground$
                         er-soft+
                         explode
                         fargn
                         fargs
                         fcons-term
                         ffn-symb
                         flambda-applicationp
                         fmt-hard-right-margin
                         fmt-soft-right-margin
                         formals
                         fquotep
                         implode
                         impossible
                         known-packages
                         lambda-body
                         lambda-formals
                         logic-fns-with-raw-code
                         lower-case-p
                         make-lambda
                         maybe-stringp
                         msg-listp
                         no-stobjs-p
                         partition-rest-and-keyword-args
                         patbind-run-when
                         primitivep
                         printable-charlist-p
                         program-fns-with-raw-code
                         pseudo-termfnp
                         quote-listp
                         sbyte16
                         sbyte32
                         sbyte64
                         sbyte8
                         sort-symbol-listp
                         string-downcase
                         string-upcase
                         string=>nats
                         symbol-package-name-lst
                         trans-eval
                         tuplep
                         typed-tuplep
                         ubyte16
                         ubyte8=>hexchars
                         ubyte8s=>hexstring
                         unnormalized-body
                         upper-case-p
                         variablep
                         str::chars-in-charset-p
                         str::natchars16
                         str::natstr
                         str::strtok)))

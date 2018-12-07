; Java Library -- Package
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
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
                         alpha/digit/uscore/dollar-char-listp
                         alpha/uscore/dollar-char-p
                         body
                         bool
                         char-downcase
                         char-upcase
                         chars=>nats
                         defxdoc+
                         ensure-boolean$
                         ensure-function-name$
                         ensure-function-name-list$
                         ensure-list-functions$
                         ensure-list-no-duplicates$
                         ensure-string$
                         ensure-string-or-nil$
                         er-soft+
                         explode
                         fargn
                         fargs
                         fcons-term
                         ffn-symb
                         flambda-applicationp
                         formals
                         fquotep
                         implode
                         known-packages
                         lambda-body
                         lambda-formals
                         lower-case-p
                         make-lambda
                         maybe-stringp
                         msg-listp
                         no-stobjs-p
                         partition-rest-and-keyword-args
                         patbind-run-when
                         primitivep
                         printable-char-listp
                         pseudo-termfnp
                         sbyte8
                         sbyte16
                         sbyte32
                         sbyte64
                         sort-symbol-listp
                         string-downcase
                         string-upcase
                         string=>nats
                         tuplep
                         typed-tuplep
                         ubyte8s=>hexstring
                         ubyte16
                         upper-case-p
                         variablep
                         str::natchars16
                         str::natstr
                         str::strtok)))

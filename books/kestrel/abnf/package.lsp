; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ABNF" (set-difference-eq
                (append *std-pkg-symbols*
                        '(add-const-to-untranslate-preprocess
                          alpha/digit/dash-charlist-p
                          bool
                          char-fix
                          chars=>nats
                          defmacro+
                          defxdoc+
                          explode
                          implode
                          integers-from-to
                          legal-constantp
                          lnfix
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
                          patbind-fun
                          pos-list
                          pos-listp
                          pseudo-event-formp
                          pseudo-event-form-listp
                          read-file-characters
                          return-raw
                          seq
                          seq-backtrack
                          string=>nats
                          unsigned-byte-listp
                          fty::err
                          fty::err-push
                          fty::resulterrp
                          set::list-in
                          set::nat-setp
                          std::define-sk
                          str::downcase-char
                          str::downcase-charlist
                          str::upcase-char))
                '(closure
                  rule
                  symbol
                  symbolp
                  string
                  stringp)))

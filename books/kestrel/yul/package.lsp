; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "YUL" (append (set-difference-eq
                       *std-pkg-symbols*
                       '(block
                         error
                         funcall
                         value
                         values))
                      '(any
                        bebytes=>nat
                        bool
                        boolean-resultp
                        bytep
                        byte-listp
                        defund-sk
                        defxdoc+
                        impossible
                        integers-from-to
                        nat
                        nat-listp
                        nat-list-fix
                        nat-resultp
                        nats=>chars
                        nats=>string
                        ubyte8p
                        ubyte8-listp
                        ubyte16p
                        ubyte16-fix
                        ubyte256
                        ubyte256p
                        unsigned-byte-listp
                        values
                        fty::info
                        fty::okf
                        fty::reserr
                        fty::reserrf
                        fty::reserrp
                        fty::reserr-optionp
                        fty::stack
                        std::define-sk
                        str::hex-digit-char)))

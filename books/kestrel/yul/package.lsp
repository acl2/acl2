; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/utilities/omaps/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "YUL" (append (set-difference-eq
                       *std-pkg-symbols*
                       '(block
                         error
                         funcall
                         value
                         values))
                      '(any
                        bool
                        boolean-resultp
                        defund-sk
                        defxdoc+
                        nat
                        nat-resultp
                        fty::err
                        fty::info
                        fty::ok
                        fty::resulterr
                        fty::resulterrp
                        fty::resulterr-optionp
                        fty::stack
                        std::define-sk
                        str::hex-digit-char
                        ubyte256
                        values)))

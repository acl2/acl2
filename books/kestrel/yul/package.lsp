; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
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
                         value))
                      '(any
                        bool
                        boolean-resultp
                        defund-sk
                        defxdoc+
                        nat
                        nat-resultp
                        patbind-nat-result-err
                        patbind-nat-result-ok
                        fty::err
                        fty::info
                        fty::ok
                        fty::resulterr
                        fty::resulterrp
                        fty::resulterr-optionp
                        fty::stack
                        str::hex-digit-char
                        ubyte256
                        values)))

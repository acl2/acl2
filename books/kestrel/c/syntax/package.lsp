; C Library
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
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "C$" (append
              (set-difference-eq *std-pkg-symbols*
                                 '(position
                                   read-char
                                   schar
                                   unread-char))
              '(any
                bool
                bytep
                byte-list
                byte-listp
                defirrelevant
                defmacro+
                defxdoc+
                erp
                impossible
                nat
                nat-list
                nat-optionp
                nats=>string
                pos
                reterr
                retok
                unsigned-byte-listp
                std::defret-mutual
                str::dec-digit-char
                str::dec-digit-char-p
                str::dec-digit-char-list
                str::dec-digit-char-listp
                str::hex-digit-char
                str::hex-digit-char-p
                str::hex-digit-char-list
                str::hex-digit-char-listp
                str::oct-digit-char
                str::oct-digit-char-p)))

; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "C$" (append
              (set-difference-eq *std-pkg-symbols*
                                 '(position
                                   read-char
                                   read-files
                                   schar
                                   standardp
                                   type
                                   typep
                                   unread-char))
              '(any
                assert!-stobj
                bool
                bool-fix
                bytep
                byte-list
                byte-listp
                byte-list-fix
                defirrelevant
                defmacro+
                defxdoc+
                enable*
                er-soft+
                erp
                impossible
                keyword-listp
                keyword-value-list-to-alist
                lnfix
                make-event-terse
                nat
                nat-list
                nat-list-fix
                nat-optionp
                nats=>string
                packn-pos
                pos
                pseudo-event-formp
                pseudo-event-form-listp
                reterr
                retok
                string-optionp
                table-alist+
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
                str::oct-digit-char-p
                str::oct-digit-char-list
                str::oct-digit-char-listp
                c::*keywords*)))

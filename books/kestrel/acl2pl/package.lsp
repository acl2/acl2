; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ACL2PL" (append (set-difference-eq *std-pkg-symbols*
                                            '(function
                                              functionp
                                              make-package
                                              package
                                              packagep
                                              program
                                              step
                                              symbol-value
                                              value
                                              values))
                         '(acl2-number
                           define-sk
                           defxdoc+
                           explode
                           fargs
                           ffn-symb
                           formals+
                           fquotep
                           good-pseudo-termp
                           good-pseudo-term-listp
                           good-valuep
                           impossible
                           known-packages+
                           lambda-body
                           lambda-formals
                           lower-case-p
                           str-fix
                           ubody+
                           variablep)))

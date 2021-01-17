; Isar (Intelligible Semi-Automated Reasoning) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ISAR" (append (set-difference-eq *std-pkg-symbols*
                                          '())
                       '(cw-event
                         defxdoc+
                         er-soft+
                         keyword-listp
                         make-event-terse
                         packn-pos
                         pseudo-event-formp
                         pseudo-event-form-listp
                         restore-output
                         run-unless
                         tuple
                         tuplep)))

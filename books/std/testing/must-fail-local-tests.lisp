; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-fail-local")

(include-book "must-succeed-star")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail-local (defthm th (natp (1+ x))))

(must-fail-local (defthm th (natp (1+ x)))
                 :with-output-off nil)

(must-fail-local (defthm th (natp (1+ x)))
                 :with-output-off (summary)
                 :check-expansion t)

(must-fail-local (defthm th (natp (1+ x))))

(must-fail-local (defthm th (natp (1+ x))))

(must-fail-local (defthm th (natp (1+ x))))

; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "solve")
(include-book "solve-templates")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 1.

(must-succeed*
 (gen-inputs-1-sat-eqterm)
 (apt::solve old
             :method :manual
             :solution-body (term x)
             :solution-hints (("Goal" :in-theory (enable sat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 2.

(must-succeed*
 (gen-inputs-2-sat-eqterm)
 (apt::solve old
             :method :manual
             :solution-body (term x1 x2)
             :solution-hints (("Goal" :in-theory (enable sat)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 3.

(must-succeed*
 (gen-inputs-3-sat-eqterm)
 (apt::solve old
             :method :manual
             :solution-body (term x1 x2 x3)
             :solution-hints (("Goal" :in-theory (enable sat)))))

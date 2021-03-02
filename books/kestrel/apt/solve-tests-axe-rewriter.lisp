; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/apt/solve" :dir :system)
(include-book "solve-method-axe-rewriter")

(include-book "kestrel/apt/solve-templates" :dir :system)

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 1.

(must-succeed*
 (gen-inputs-1-rw-eqterm)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

(must-succeed*
 (gen-inputs-1-rw-t)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 2.

(must-succeed*
 (gen-inputs-2-rw-eqterm)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

(must-succeed*
 (gen-inputs-2-rw-t)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 3.

(must-succeed*
 (gen-inputs-3-rw-eqterm)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

(must-succeed*
 (gen-inputs-3-rw-t)
 (apt::solve old
             :method :axe-rewriter
             :method-rules (rwrule)))

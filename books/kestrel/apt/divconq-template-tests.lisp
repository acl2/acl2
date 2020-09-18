; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "divconq")
(include-book "divconq-templates")

(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = m = 0.

(must-succeed*
 (gen-inputs 0 0 0 0)
 (apt::divconq old :schema :list-fold)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = m = 1.

(must-succeed*
 (gen-inputs 1 0 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 2 and m = 1.

(must-succeed*
 (gen-inputs 2 0 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 1 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 1 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 1 and m = 2.

(must-succeed*
 (gen-inputs 1 0 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 0 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 1 1 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = m = 2.

(must-succeed*
 (gen-inputs 2 0 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 0)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 1)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 0 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 1 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

(must-succeed*
 (gen-inputs 2 2 2 2)
 (apt::divconq old :schema :list-fold :list-input x)
 :with-output-off nil)

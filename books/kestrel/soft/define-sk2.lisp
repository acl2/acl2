; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "implementation")

(include-book "kestrel/utilities/define-sk" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is in a separate file from implementation.lisp
; because it includes the non-built-in DEFINE-SK.
; Thus, one can include this file only if needed.
; Note that we do not create a file define2.lisp analogous to this one
; because SOFT already includes DEFINE for its own implementation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(gen-macro2-of-macro std::define-sk)

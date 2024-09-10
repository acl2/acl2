; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See gen-as-foundation.lisp for an explanation.

(in-package "ACL2")

; Provide a non-error implementation for export misc of to-be-defined
; attachable stobj st.
(include-book "impl")

; Define attachable stobj st, and also define abstract stobj st-top that has st
; as its foundation.
(include-book "gen-as-foundation")

; An error at the end of gen-as-foundation.lisp is avoided here by use of the
; attached version of export misc of st when executing export misc-top of
; st-top.
(value-triple (f1-top st-top))

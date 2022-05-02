; Verifying termination and guards of functions related to defstobj
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(verify-termination doublet-listp) ; and guards, also done elsewhere

(verify-termination defstobj-fnname) ; and guards

(verify-termination defstobj-fnname-key2) ; and guards

; (verify-termination fix-stobj-array-type) ; problem due to raw Lisp code

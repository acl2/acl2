; Unquote Object If Quoted
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2017 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-unquote (x)
  :parents (kestrel-utilities unquote)
  :short "Unquote an object, if quoted; otherwise, leave unchanged."
  (case-match x
    (('quote y) y)
    (& x)))

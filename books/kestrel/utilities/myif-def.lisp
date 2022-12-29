; MYIF, an alias for IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; MYIF is just an alias for IF, but MYIF can be disabled to prevent
;; case-splitting.  (Before ACL2 allowed the left-hand-side of a
;; rewrite rule to be an IF, MYIF was also used to state rewrite rules.)

;; See theorems in myif.lisp.

;; See also the built-in function if*.

;; TODO: Consider giving this a better name.

(defund myif (test thenpart elsepart)
  (declare (xargs :guard t))
  (if test thenpart elsepart))

; MYIF, an alias for IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; MYIF is just an alias for IF, but MYIF can be disabled to prevent
;; case-splitting.

(defund myif (test thenpart elsepart)
  (declare (xargs :guard t))
  (if test thenpart elsepart))

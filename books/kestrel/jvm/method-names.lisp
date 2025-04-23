; Method names
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; The name of a method is just a string (at least for now)
(defun method-namep (obj) (declare (xargs :guard t)) (stringp obj))

;; Disabled by default
;; Needed if we call string functions on method-names
(defthmd stringp-when-method-namep
  (implies (stringp name)
           (method-namep name)))

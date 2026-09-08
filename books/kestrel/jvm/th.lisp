; A designator for an arbitrary thread
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ;todo: use jvm package?

;fixme where should this go?
;FIXME use a defstub?  Is it important to be able to execute this?
(defund th () (declare (xargs :guard t)) 0)
(in-theory (disable (:type-prescription th)))
(in-theory (disable (:executable-counterpart th)))

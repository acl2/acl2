; Support for concrete and symbolic execution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ;todo: use jvm package?

(include-book "jvm")

;fixme where should this go?
;FIXME use a defstub?  Is it important to be able to execute this?
(defund th () (declare (xargs :guard t)) 0)
(in-theory (disable (:type-prescription th)))
(in-theory (disable (:executable-counterpart th)))

;; The height of the call stack of thread (TH) in state S.
(defund stack-height (s)
  (jvm::call-stack-size (jvm::call-stack (th) s)))

; Alist Utilities -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some tests for the alist utilities in alists.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alists")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (symbol-symbol-alistp nil))

(assert-event (symbol-symbol-alistp '((a . b))))

(assert-event (symbol-symbol-alistp '((t . nil) (:logic . :program))))

(assert-event (not (symbol-symbol-alistp 3)))

(assert-event (not (symbol-symbol-alistp '(3))))

(assert-event (not (symbol-symbol-alistp '((x . y) (2/3 . nil)))))

(assert-event (not (symbol-symbol-alistp '((xx . yy) (t . "nil")))))

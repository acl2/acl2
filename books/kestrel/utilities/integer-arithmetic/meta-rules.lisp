; Integer Arithmetic -- Meta Rules
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "operations")

(include-book "meta-iplus-equal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we put together our meta rules for integer arithmetic.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm cancel_iplus-equal-correct ; proved in meta-iplus-equal.lisp
  (equal (ev-iplus-equal x a)
         (ev-iplus-equal (cancel_iplus-equal x) a))
  :rule-classes ((:meta :trigger-fns (equal))))

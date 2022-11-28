; The definition of symbol-symbol-alistp
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See theorems in symbol-symbol-alistp.lisp.

;; From including std/typed-alists/symbol-symbol-alistp.lisp
(defund symbol-symbol-alistp (x)
  (declare (xargs :guard t
                  :normalize nil))
  (if (consp x)
      (and (consp (car x))
           (symbolp (caar x))
           (symbolp (cdar x))
           (symbol-symbol-alistp (cdr x)))
    (null x)))

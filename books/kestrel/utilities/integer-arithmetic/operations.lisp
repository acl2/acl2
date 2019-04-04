; Integer Arithmetic -- Operations
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define integer counterparts binary-i+, binary-i*, and unary-i-
; of the primitive functions binary-+, binary-*, and unary--.
; These integer counterparts fix their inputs to integers.
; We also define macros i+, i*, and i- analogously to the built-in +, *, and -;
; however, we do not evaluate unary-i- when its argument is a number, unlike -.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-i+ (x y)
  (declare (xargs :guard (and (integerp x) (integerp y))))
  (binary-+ (ifix x) (ifix y)))

(defmacro i+ (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst)) (list 'binary-i+ 0 (car rst)))
        (t (xxxjoin 'binary-i+ rst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-i* (x y)
  (declare (xargs :guard (and (integerp x) (integerp y))))
  (binary-* (ifix x) (ifix y)))

(defmacro i* (&rest rst)
  (cond ((null rst) 1)
        ((null (cdr rst)) (list 'binary-i* 1 (car rst)))
        (t (xxxjoin 'binary-i* rst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund unary-i- (x)
  (declare (xargs :guard (integerp x)))
  (unary-- (ifix x)))

(defmacro i- (x &optional (y 'nil binary-casep))
  (if binary-casep
      `(binary-i+ ,x (unary-i- ,y))
    `(unary-i- ,x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-macro-fn i+ binary-i+)
(add-macro-fn i* binary-i*)
(add-macro-fn i- unary-i-)

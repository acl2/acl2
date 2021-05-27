; Taking the xnor of two bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(include-book "getbit")
(include-book "bitnot")

;x and y should be single bits
;guards?
;; ACL2 derives the bit type (0 or 1) for this.
(defun bitxnor (x y)
  (declare (type integer x y))
  (if (= (getbit 0 x) (getbit 0 y))
      1
    0))

;bozo gen
(defthm unsigned-byte-p-of-bitxnor
  (equal (unsigned-byte-p 1 (bitxnor x y))
         t))

(defthm bitxnor-of-0-arg1
  (equal (bitxnor 0 x)
         (bitnot x))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable bitxnor bitnot))))

(defthm bitxnor-of-0-arg2
  (equal (bitxnor x 0)
         (bitnot x))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable bitxnor bitnot))))

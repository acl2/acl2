; Taking the xnor of two bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(include-book "getbit")
(include-book "bitnot")

;; Computes the XNOR (complement of XOR) of the bits X and Y.
;x and y should be single bits
;; ACL2 derives the bit type (0 or 1) for this.
(defund bitxnor (x y)
  (declare (type integer x y))
  (if (= (getbit 0 x) (getbit 0 y))
      1
    0))

(defthm bitp-of-bitxnor
  (bitp (bitxnor x y)))

(defthm unsigned-byte-p-of-bitxnor
  (implies (posp size)
           (unsigned-byte-p size (bitxnor x y)))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-0-arg1
  (equal (bitxnor 0 y)
         (bitnot y))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-0-arg2
  (equal (bitxnor x 0)
         (bitnot x))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-getbit-0-arg1
  (equal (bitxnor (getbit 0 x) y)
         (bitxnor x y))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-getbit-0-arg2
  (equal (bitxnor x (getbit 0 y))
         (bitxnor x y))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-1-arg1
  (equal (bitxnor 1 y)
         (getbit 0 y))
  :hints (("Goal" :in-theory (enable bitxnor))))

(defthm bitxnor-of-1-arg2
  (equal (bitxnor x 1)
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable bitxnor))))

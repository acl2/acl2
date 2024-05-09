(in-package 3bz)

(deftype ub8 () '(unsigned-byte 8))
(deftype ub16 () '(unsigned-byte 16))
(deftype ub32 () '(unsigned-byte 32))
(deftype ub64 () '(unsigned-byte 64))

(deftype ht-bit-count-type ()'(unsigned-byte 4))
(deftype ht-offset-type ()'(unsigned-byte 11))
(deftype ht-node-type ()'(unsigned-byte 16))
(deftype ht-node-array-type () `(simple-array ht-node-type (,+max-tree-size+)))

(deftype code-table-type () '(simple-array (unsigned-byte 4) 1))

;; mezzano likes (integer 0 m-p-f) better than (and fixnum unsigned-byte)
(deftype non-negative-fixnum () `(integer 0 ,most-positive-fixnum))

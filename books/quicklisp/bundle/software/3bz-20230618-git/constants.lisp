(in-package 3bz)

;; libz says these are enough entries for zlib as specified
(defconstant +max-tree-entries/len+ 852)
(defconstant +max-tree-entries/dist+ 592)
(defconstant +max-tree-size+ (+ +max-tree-entries/len+
                                +max-tree-entries/dist+))

;; max # of bits for an encoded huffman tree entry + and optional extra bits
;; (= 15 bits + 13 extra bits)
(defconstant +ht-max-bits+ 28)

;; low-bit tags for nodes in tree
(defconstant +ht-literal+ #b00)
(defconstant +ht-link/end+ #b01)
(defconstant +ht-len/dist+ #b10)
(defconstant +ht-invalid+ #b11)

;; 'end' code in lit/len alphabet
(defconstant +end-code+ 256)
;; first length code in lit/len alphabet
(defconstant +lengths-start+ 257)
;; last valid length (there are some extra unused values to fill tree)
(defconstant +lengths-end+ 285)
;; offset of length codes in extra-bits tables
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +lengths-extra-bits-offset+ 32))

(defconstant +adler32-prime+ 65521)



;; extra-bits and len/dist-bases store
(declaim (type (simple-array (unsigned-byte 4)
                             (#. (+ 29 +lengths-extra-bits-offset+)))
               +extra-bits+)
         (type (simple-array (unsigned-byte 16)
                             (#. (+ 29 +lengths-extra-bits-offset+)))
               +len/dist-bases+))

(alexandria:define-constant +extra-bits+
    (concatenate
     '(simple-array (unsigned-byte 4) (61))
     (replace (make-array +lengths-extra-bits-offset+ :initial-element 0)
              #(0 0 0 0 1 1 2 2 3 3 4 4 5 5 6 6 7 7 8 8 9 9 10 10 11 11 12 12 13 13))
     #(0 0 0 0 0 0 0 0 1 1 1 1 2 2 2 2 3 3 3 3 4 4 4 4 5 5 5 5 0))
  :test 'equalp)


;; base length value for each length/distance code, add to extra bits
;; to get length
(alexandria:define-constant +len/dist-bases+
    (concatenate '(simple-array (unsigned-byte 16) (61))
                 (replace (make-array +lengths-extra-bits-offset+ :initial-element 0)
                          #(1 2 3 4 5 7 9 13 17 25 33 49 65 97
                            129 193 257 385 513 769
                            1025 1537 2049 3073 4097 6145 8193
                            12289 16385 24577))
                 #(3 4 5 6 7 8 9 10 11 13 15 17 19 23 27 31 35 43 51 59 67 83 99
                   115 131 163 195 227 258))
  :test 'equalp)

(declaim (type (simple-array (unsigned-byte 8) (19)) +len-code-order+))

(alexandria:define-constant +len-code-order+
    (coerce #(16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15)
            '(simple-array (unsigned-byte 8) (19)))
  :test 'equalp)
(declaim (type (simple-array (unsigned-byte 4) (19)) +len-code-extra+))
(alexandria:define-constant +len-code-extra+
    (coerce #(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 3 7)
            '(simple-array (unsigned-byte 4) (19)))
  :test 'equalp)

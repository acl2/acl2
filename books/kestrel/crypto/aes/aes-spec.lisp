; Formal specification of the AES block cipher
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AES")

;Formal specification of AES encryption, decryption, and key expansion
;Supports all 3 key sizes: 128-bits, 192-bits, and 256-bits.
;(Note that the block size [size of the plaintext and ciphertext] for AES is always 128 bits.)
;Written from the spec, FIPS 197 (http://csrc.nist.gov/publications/fips/fips197/fips-197.pdf)

;; TODO: Perhaps modernize the coding style used (e.g., add stricter types).
;; TODO: Perhaps improve the proofs in this file.

(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/arrays-2d/bv-arrays-2d" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice2" :dir :system))
(local (include-book "kestrel/arrays-2d/bv-arrays-2d" :dir :system)) ; for BV-ARRAYP-of-GET-COLUMN
(local (include-book "kestrel/bv/rules" :dir :system)) ; for unsigned-byte-p-when-top-bit-0
(local (in-theory (disable true-listp)))

(local (in-theory (enable acl2::integerp-of-nth-when-bv-arrayp
                          acl2::<=-of-0-and-nth-when-bv-arrayp)))

(local
 (defthm nonneg-of-nth-when-all-unsigned-byte-p
   (implies (and (acl2::all-unsigned-byte-p size list)
                 (natp n)
                 (< n (len list)))
            (<= 0 (nth n list)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm <-of-256-when-all-unsigned-byte-p
   (implies (and (acl2::all-unsigned-byte-p 8 list)
                 (natp n)
                 (< n (len list)))
            (< (nth n list) 256))
   :hints (("Goal" :in-theory (enable nth acl2::all-unsigned-byte-p)))))

(local
 (defthm unsigned-byte-p-of-nth-when-all-unsigned-byte-p
  (implies (and (acl2::all-unsigned-byte-p size list)
                (natp n)
                (< n (len list)))
           (unsigned-byte-p size (nth n list)))
  :hints (("Goal" :in-theory (enable nth)))))

(defthm 2d-bv-arrayp-of-reverse-list
  (implies (acl2::2d-bv-arrayp width numrows numcols array)
           (acl2::2d-bv-arrayp width numrows numcols (acl2::reverse-list array)))
  :hints (("Goal" :in-theory (enable acl2::2d-bv-arrayp))))

(defthm 2d-array-width-of-cons
  (equal (acl2::2d-array-width (cons row rows))
         (len row))
  :hints (("Goal" :in-theory (enable acl2::2d-array-width))))

(defthm 2d-bv-arrayp-of-update-nth
  (implies (and (acl2::bv-arrayp bytesize numcols val)
                (natp index)
                (< index numrows)
                (acl2::2d-bv-arrayp bytesize numrows numcols items))
           (acl2::2d-bv-arrayp bytesize numrows numcols (update-nth index val items)))
  :hints (("Goal" :in-theory (enable acl2::2d-bv-arrayp acl2::len-update-nth))))

(defthm 2d-bv-arrayp-of-take
  (implies (and (acl2::2d-bv-arrayp bytesize (len items) numcols items)
                (natp n)
                (<= n (len items)))
           (acl2::2d-bv-arrayp bytesize n numcols (acl2::take n items)))
  :hints (("Goal" :in-theory (enable acl2::2d-bv-arrayp))))

;;;
;;; end of library material
;;;

;number of columns (32-bit words) in the State.  For AES this is always 4 (see FIPS 197, section 2.2).
(defconst *nb* 4)

;number of rounds.  Will be 10, 12, or 14.  (See Figure 4 in FIPS 197.)
;nk is the number of 32-bit words in the cipher key.  Must be 4, 6, or 8. (see FIPS 197, section 2.2).
(defun nr (nk)
  (declare (xargs :guard (natp nk)))
  (+ 6 nk))

;the "bytes" mentioned by the standard are 8-bit unsigned-byte-p's
(defmacro bytep (item)
  `(unsigned-byte-p 8 ,item))

(defmacro byte-arrayp (length array)
  `(acl2::bv-arrayp 8 ,length ,array))

;A word is an array of 4 bytes (could instead use 32-bit bit vectors)
(defmacro wordp (item)
  `(byte-arrayp 4 ,item))

(defmacro word-listp (lst)
  (declare (xargs :guard t))
  `(acl2::bv-arrayp-list 8 4 ,lst))

(defun wordbyte0 (word)
  (declare (xargs :guard (wordp word)))
  (nth 0 word))

(defun wordbyte1 (word)
  (declare (xargs :guard (wordp word)))
  (nth 1 word))

(defun wordbyte2 (word)
  (declare (xargs :guard (wordp word)))
  (nth 2 word))

(defun wordbyte3 (word)
  (declare (xargs :guard (wordp word)))
  (nth 3 word))

(defun make-word (byte0 byte1 byte2 byte3)
  (declare (xargs :guard (and (bytep byte0)
                              (bytep byte1)
                              (bytep byte2)
                              (bytep byte3))))
  (list byte0 byte1 byte2 byte3))

;the state is a 4x4 array of bytes.
(defmacro statep (item)
  (declare (xargs :guard t))
  `(acl2::2d-bv-arrayp 8 4 4 ,item))

(defun inp (array)
  (declare (xargs :guard t))
  (acl2::bv-arrayp 8 (* 4 *nb*) array))

(defun keyp (key nk)
  (declare (xargs :guard (or (equal nk 4) (equal nk 6) (equal nk 8))))
  (acl2::bv-arrayp 8 (* 4 nk) key))

(defund expanded-keyp (item nk)
  (declare (xargs :guard (acl2::member nk '(4 6 8))))
  (acl2::2d-bv-arrayp 8
                      (* *nb* (+ (nr nk) 1))
                      4
                      item))

(defthm expanded-keyp-of-update-nth
  (implies (and (expanded-keyp w nk)
                (acl2::bv-arrayp  8 4 val)
                (natp i)
                (< i (* *nb* (+ (nr nk) 1))))
           (expanded-keyp (update-nth i val w) nk))
  :hints (("Goal" :in-theory (enable expanded-keyp))))

(defthm bv-arrayp-of-nth-when-expanded-keyp
  (implies (and (expanded-keyp w nk)
                (natp i)
                (< i (* *nb* (+ (nr nk) 1))))
           (acl2::bv-arrayp 8 4 (nth i w)))
  :hints (("Goal" :in-theory (enable expanded-keyp))))

;we make this a function instead of a constant so we can disable it during proofs
(defund sbox () (declare (xargs :guard t))
  '(#x63 #x7c #x77 #x7b #xf2 #x6b #x6f #xc5 #x30 #x01 #x67 #x2b #xfe #xd7 #xab #x76
    #xca #x82 #xc9 #x7d #xfa #x59 #x47 #xf0 #xad #xd4 #xa2 #xaf #x9c #xa4 #x72 #xc0
    #xb7 #xfd #x93 #x26 #x36 #x3f #xf7 #xcc #x34 #xa5 #xe5 #xf1 #x71 #xd8 #x31 #x15
    #x04 #xc7 #x23 #xc3 #x18 #x96 #x05 #x9a #x07 #x12 #x80 #xe2 #xeb #x27 #xb2 #x75
    #x09 #x83 #x2c #x1a #x1b #x6e #x5a #xa0 #x52 #x3b #xd6 #xb3 #x29 #xe3 #x2f #x84
    #x53 #xd1 #x00 #xed #x20 #xfc #xb1 #x5b #x6a #xcb #xbe #x39 #x4a #x4c #x58 #xcf
    #xd0 #xef #xaa #xfb #x43 #x4d #x33 #x85 #x45 #xf9 #x02 #x7f #x50 #x3c #x9f #xa8
    #x51 #xa3 #x40 #x8f #x92 #x9d #x38 #xf5 #xbc #xb6 #xda #x21 #x10 #xff #xf3 #xd2
    #xcd #x0c #x13 #xec #x5f #x97 #x44 #x17 #xc4 #xa7 #x7e #x3d #x64 #x5d #x19 #x73
    #x60 #x81 #x4f #xdc #x22 #x2a #x90 #x88 #x46 #xee #xb8 #x14 #xde #x5e #x0b #xdb
    #xe0 #x32 #x3a #x0a #x49 #x06 #x24 #x5c #xc2 #xd3 #xac #x62 #x91 #x95 #xe4 #x79
    #xe7 #xc8 #x37 #x6d #x8d #xd5 #x4e #xa9 #x6c #x56 #xf4 #xea #x65 #x7a #xae #x08
    #xba #x78 #x25 #x2e #x1c #xa6 #xb4 #xc6 #xe8 #xdd #x74 #x1f #x4b #xbd #x8b #x8a
    #x70 #x3e #xb5 #x66 #x48 #x03 #xf6 #x0e #x61 #x35 #x57 #xb9 #x86 #xc1 #x1d #x9e
    #xe1 #xf8 #x98 #x11 #x69 #xd9 #x8e #x94 #x9b #x1e #x87 #xe9 #xce #x55 #x28 #xdf
    #x8c #xa1 #x89 #x0d #xbf #xe6 #x42 #x68 #x41 #x99 #x2d #x0f #xb0 #x54 #xbb #x16))

(in-theory (disable (:e sbox)))

(defthm len-of-sbox
  (equal (len (sbox))
         256)
  :hints (("Goal" :in-theory (enable (sbox)))))

(defthm all-unsigned-byte-p-of-sbox
  (acl2::all-unsigned-byte-p 8 (sbox))
  :hints (("Goal" :in-theory (enable (sbox)))))

(defthm unsigned-byte-p-of-nth-of-sbox-gen
  (implies (and (bytep n)
                (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (nth n (sbox)))))

;we make this a function instead of a constant so we can disable it during proofs
(defund invsbox () (declare (xargs :guard t))
  '(#x52 #x09 #x6a #xd5 #x30 #x36 #xa5 #x38 #xbf #x40 #xa3 #x9e #x81 #xf3 #xd7 #xfb
    #x7c #xe3 #x39 #x82 #x9b #x2f #xff #x87 #x34 #x8e #x43 #x44 #xc4 #xde #xe9 #xcb
    #x54 #x7b #x94 #x32 #xa6 #xc2 #x23 #x3d #xee #x4c #x95 #x0b #x42 #xfa #xc3 #x4e
    #x08 #x2e #xa1 #x66 #x28 #xd9 #x24 #xb2 #x76 #x5b #xa2 #x49 #x6d #x8b #xd1 #x25
    #x72 #xf8 #xf6 #x64 #x86 #x68 #x98 #x16 #xd4 #xa4 #x5c #xcc #x5d #x65 #xb6 #x92
    #x6c #x70 #x48 #x50 #xfd #xed #xb9 #xda #x5e #x15 #x46 #x57 #xa7 #x8d #x9d #x84
    #x90 #xd8 #xab #x00 #x8c #xbc #xd3 #x0a #xf7 #xe4 #x58 #x05 #xb8 #xb3 #x45 #x06
    #xd0 #x2c #x1e #x8f #xca #x3f #x0f #x02 #xc1 #xaf #xbd #x03 #x01 #x13 #x8a #x6b
    #x3a #x91 #x11 #x41 #x4f #x67 #xdc #xea #x97 #xf2 #xcf #xce #xf0 #xb4 #xe6 #x73
    #x96 #xac #x74 #x22 #xe7 #xad #x35 #x85 #xe2 #xf9 #x37 #xe8 #x1c #x75 #xdf #x6e
    #x47 #xf1 #x1a #x71 #x1d #x29 #xc5 #x89 #x6f #xb7 #x62 #x0e #xaa #x18 #xbe #x1b
    #xfc #x56 #x3e #x4b #xc6 #xd2 #x79 #x20 #x9a #xdb #xc0 #xfe #x78 #xcd #x5a #xf4
    #x1f #xdd #xa8 #x33 #x88 #x07 #xc7 #x31 #xb1 #x12 #x10 #x59 #x27 #x80 #xec #x5f
    #x60 #x51 #x7f #xa9 #x19 #xb5 #x4a #x0d #x2d #xe5 #x7a #x9f #x93 #xc9 #x9c #xef
    #xa0 #xe0 #x3b #x4d #xae #x2a #xf5 #xb0 #xc8 #xeb #xbb #x3c #x83 #x53 #x99 #x61
    #x17 #x2b #x04 #x7e #xba #x77 #xd6 #x26 #xe1 #x69 #x14 #x63 #x55 #x21 #x0c #x7d))

(in-theory (disable (:e invsbox)))

(defthm len-of-invsbox
  (equal (len (invsbox))
         256)
  :hints (("Goal" :in-theory (enable (invsbox)))))

(defthm all-unsigned-byte-p-of-inv-sbox
  (acl2::all-unsigned-byte-p 8 (invsbox))
  :hints (("Goal" :in-theory (enable (invsbox)))))

(defthm unsigned-byte-p-of-nth-of-invsbox-gen
  (implies (and (bytep n)
                (<= 8 size)
                (integerp size))
           (unsigned-byte-p size (nth n (invsbox)))))

;move
(defthm all-true-listp-when-2d-bv-arrayp
  (implies (acl2::2d-bv-arrayp bytesize numrows numcols state) ;free vars
           (acl2::all-true-listp state))
  :hints (("Goal" :in-theory (enable acl2::all-true-listp
                                     acl2::2d-bv-arrayp))))

(defund subbytes (state)
  (declare (xargs :guard (statep state)))
  (list (list (nth (array-elem-2d 0 0 state) (sbox))
              (nth (array-elem-2d 0 1 state) (sbox))
              (nth (array-elem-2d 0 2 state) (sbox))
              (nth (array-elem-2d 0 3 state) (sbox)))
        (list (nth (array-elem-2d 1 0 state) (sbox))
              (nth (array-elem-2d 1 1 state) (sbox))
              (nth (array-elem-2d 1 2 state) (sbox))
              (nth (array-elem-2d 1 3 state) (sbox)))
        (list (nth (array-elem-2d 2 0 state) (sbox))
              (nth (array-elem-2d 2 1 state) (sbox))
              (nth (array-elem-2d 2 2 state) (sbox))
              (nth (array-elem-2d 2 3 state) (sbox)))
        (list (nth (array-elem-2d 3 0 state) (sbox))
              (nth (array-elem-2d 3 1 state) (sbox))
              (nth (array-elem-2d 3 2 state) (sbox))
              (nth (array-elem-2d 3 3 state) (sbox)))))

(defthm statep-of-subbytes
  (implies (statep state)
           (statep (subbytes state)))
  :hints (("Goal" :in-theory (enable subbytes))))

(defund invsubbytes (state)
  (declare (xargs :guard (statep state)))
  (list (list (nth (array-elem-2d 0 0 state) (invsbox))
              (nth (array-elem-2d 0 1 state) (invsbox))
              (nth (array-elem-2d 0 2 state) (invsbox))
              (nth (array-elem-2d 0 3 state) (invsbox)))
        (list (nth (array-elem-2d 1 0 state) (invsbox))
              (nth (array-elem-2d 1 1 state) (invsbox))
              (nth (array-elem-2d 1 2 state) (invsbox))
              (nth (array-elem-2d 1 3 state) (invsbox)))
        (list (nth (array-elem-2d 2 0 state) (invsbox))
              (nth (array-elem-2d 2 1 state) (invsbox))
              (nth (array-elem-2d 2 2 state) (invsbox))
              (nth (array-elem-2d 2 3 state) (invsbox)))
        (list (nth (array-elem-2d 3 0 state) (invsbox))
              (nth (array-elem-2d 3 1 state) (invsbox))
              (nth (array-elem-2d 3 2 state) (invsbox))
              (nth (array-elem-2d 3 3 state) (invsbox)))))

(defthm statep-of-invsubbytes
  (implies (statep state)
           (statep (invsubbytes state)))
  :hints (("Goal" :in-theory (enable invsubbytes))))

(defund shiftrows (state)
  (declare (xargs :guard (statep state)))
  (list (list (array-elem-2d 0 0 state)
              (array-elem-2d 0 1 state)
              (array-elem-2d 0 2 state)
              (array-elem-2d 0 3 state))
        (list (array-elem-2d 1 1 state)
              (array-elem-2d 1 2 state)
              (array-elem-2d 1 3 state)
              (array-elem-2d 1 0 state))
        (list (array-elem-2d 2 2 state)
              (array-elem-2d 2 3 state)
              (array-elem-2d 2 0 state)
              (array-elem-2d 2 1 state))
        (list (array-elem-2d 3 3 state)
              (array-elem-2d 3 0 state)
              (array-elem-2d 3 1 state)
              (array-elem-2d 3 2 state))))

(defthm statep-of-shiftrows
  (implies (statep state)
           (statep (shiftrows state)))
  :hints (("Goal" :in-theory (enable shiftrows))))

(defund invshiftrows (state)
  (declare (xargs :guard (statep state)))
  (list (list (array-elem-2d 0 0 state)
              (array-elem-2d 0 1 state)
              (array-elem-2d 0 2 state)
              (array-elem-2d 0 3 state))
        (list (array-elem-2d 1 3 state)
              (array-elem-2d 1 0 state)
              (array-elem-2d 1 1 state)
              (array-elem-2d 1 2 state))
        (list (array-elem-2d 2 2 state)
              (array-elem-2d 2 3 state)
              (array-elem-2d 2 0 state)
              (array-elem-2d 2 1 state))
        (list (array-elem-2d 3 1 state)
              (array-elem-2d 3 2 state)
              (array-elem-2d 3 3 state)
              (array-elem-2d 3 0 state))))

(defthm statep-of-invshiftrows
  (implies (statep state)
           (statep (invshiftrows state)))
  :hints (("Goal" :in-theory (enable invshiftrows))))

(defun binary-gf256add (x y)
  (declare (xargs :guard (and (bytep x)
                              (bytep y))))
  (acl2::bvxor 8 x y))

;adapted from the macro for "+".
(defmacro gf256add (&rest rst)
  (if rst
      (if (cdr rst)
          (xxxjoin 'binary-gf256add rst)
        (cons 'binary-gf256add
              (cons 0 (cons (car rst) nil))))
    0))

;The bit-vector representation of the special polynomial m(x) = x^8+x^4+x^3+x+1.
(defconst *m* #b100011011)

(in-theory (disable integer-length))

; Multiply the polynomial b by the polynomial x, modulo m.  There is of course a
;more efficient way to do this while remaining in the 8 bit (not 9 bit) world.
(defund xtime (b)
  (declare (xargs :guard (bytep b)))
  (let* ((b (acl2::bvshl 9 b 1)) ;shift left one bit, giving a 9-bit result
         (b (if (equal 1 (getbit 8 b)) ;check the top bit
                (bvxor 9 b *m*) ; subtract m (using XOR) if needed to reduce the polynomial
              b)))
    b))

(defthm bytep-of-xtime
  (implies (bytep b)
           (bytep (xtime b)))
  :hints (("Goal" :in-theory (enable acl2::bvshl xtime))))

;We traverse the bits of d from 0 to 7.  For each bit n, if d[n] is 1, we add
;c*x^n to the accumulator, where x is the polynomial 'x'.  We maintain
;c-times-x-to-the-n to be equal to c*x^n by repeatedly calling xtime.
;TODO: Can we obtain this from finite-differencing applied to something without
;the c-times-x-to-the-n parameter?
(defund gf256mult-aux (d n c-times-x-to-the-n acc)
  (declare (xargs :measure (nfix (- 8 n))
                  :guard (and (bytep d)
                              (natp n)
                              (bytep c-times-x-to-the-n)
                              (bytep acc))
                  ))
  (if (or (not (mbt (natp n)))
          (>= n 8))
      acc
    (let* ((bit (getbit n d))
           (acc (if (acl2::eql 1 bit) (gf256add acc c-times-x-to-the-n) acc))
           (c-times-x-to-the-n (xtime c-times-x-to-the-n)))
      (gf256mult-aux d (+ 1 n) c-times-x-to-the-n acc))))

(defund gf256mult (c d)
  (declare (xargs :guard (and (bytep c)
                              (bytep d))))
  (gf256mult-aux d
                 0     ;start at bit 0
                 c     ;c*x^0 = c*1 = c
                 0     ;initial accumulator
                 ))

(defthm bytep-of-GF256MULT-AUX
  (IMPLIES (AND ;(bytep d)
                ;(bytep c-times-x-to-the-n)
                (bytep acc))
           (bytep (GF256MULT-AUX D n c-times-x-to-the-n acc)))
  :hints (("Goal" :in-theory (enable GF256MULT-AUX))))

(defthm bytep-of-GF256MULT
  (bytep (gf256mult c d))
  :hints (("Goal" :in-theory (enable gf256mult))))

;COL is a list of four bytes
(defund mixcolumn (col)
  (declare (xargs :guard (wordp col)))
  (list (gf256add (gf256mult #x02 (nth 0 col))
                  (gf256mult #x03 (nth 1 col))
                  (nth 2 col)
                  (nth 3 col))
        (gf256add (nth 0 col)
                  (gf256mult #x02 (nth 1 col))
                  (gf256mult #x03 (nth 2 col))
                  (nth 3 col))
        (gf256add (nth 0 col)
                  (nth 1 col)
                  (gf256mult #x02 (nth 2 col))
                  (gf256mult #x03 (nth 3 col)))
        (gf256add (gf256mult #x03 (nth 0 col))
                  (nth 1 col)
                  (nth 2 col)
                  (gf256mult #x02 (nth 3 col)))))

(defthm bv-arrayp-of-mixcolumn
  (acl2::bv-arrayp 8 4 (mixcolumn col))
  :hints (("Goal" :in-theory (enable mixcolumn))))

(defthm len-of-mixcolumn
  (equal (len (mixcolumn col))
         4)
  :hints (("Goal" :in-theory (enable mixcolumn))))

(defund mixcolumns (state)
  (declare (xargs :guard (statep state)))
  (acl2::transpose-2d-array (list (mixcolumn (acl2::get-column 0 state))
                                  (mixcolumn (acl2::get-column 1 state))
                                  (mixcolumn (acl2::get-column 2 state))
                                  (mixcolumn (acl2::get-column 3 state)))))

(defthm statep-of-mixcolumns
  (statep (mixcolumns state))
  :otf-flg t
  :hints (("Goal" :in-theory (enable mixcolumns))))

;col is an array of 4 bytes
(defund invmixcolumn (col)
  (declare (xargs :guard (wordp col)))
  (list (gf256add (gf256mult #x0e (nth 0 col))
                  (gf256mult #x0b (nth 1 col))
                  (gf256mult #x0d (nth 2 col))
                  (gf256mult #x09 (nth 3 col)))
        (gf256add (gf256mult #x09 (nth 0 col))
                  (gf256mult #x0e (nth 1 col))
                  (gf256mult #x0b (nth 2 col))
                  (gf256mult #x0d (nth 3 col)))
        (gf256add (gf256mult #x0d (nth 0 col))
                  (gf256mult #x09 (nth 1 col))
                  (gf256mult #x0e (nth 2 col))
                  (gf256mult #x0b (nth 3 col)))
        (gf256add (gf256mult #x0b (nth 0 col))
                  (gf256mult #x0d (nth 1 col))
                  (gf256mult #x09 (nth 2 col))
                  (gf256mult #x0e (nth 3 col)))))

(defthm len-of-invmixcolumn
  (equal (len (invmixcolumn col))
         4)
  :hints (("Goal" :in-theory (enable invmixcolumn))))

(defthm bv-arrayp-of-invmixcolumn
  (acl2::bv-arrayp 8 4 (invmixcolumn col))
  :hints (("Goal" :in-theory (enable invmixcolumn))))

(defund invmixcolumns (state)
  (declare (xargs :guard (statep state)))
  (acl2::transpose-2d-array (list (invmixcolumn (acl2::get-column 0 state))
                                  (invmixcolumn (acl2::get-column 1 state))
                                  (invmixcolumn (acl2::get-column 2 state))
                                  (invmixcolumn (acl2::get-column 3 state)))))

(defthm statep-of-invmixcolumns
  (statep (invmixcolumns state))
  :hints (("Goal" :in-theory (enable invmixcolumns))))

(defund addroundkey-elem (r c state roundkey)
  (declare (xargs :guard (and (natp r)
                              (< r 4)
                              (natp c)
                              (< c 4)
                              (statep state)
                              (statep roundkey))))
  (gf256add (array-elem-2d r c state)
            (nth r (nth c roundkey))))

(defund addroundkey (state roundkey)
  (declare (xargs :guard (and (statep state)
                              (statep roundkey))))
  (list (list (addroundkey-elem 0 0 state roundkey)
              (addroundkey-elem 0 1 state roundkey)
              (addroundkey-elem 0 2 state roundkey)
              (addroundkey-elem 0 3 state roundkey))
        (list (addroundkey-elem 1 0 state roundkey)
              (addroundkey-elem 1 1 state roundkey)
              (addroundkey-elem 1 2 state roundkey)
              (addroundkey-elem 1 3 state roundkey))
        (list (addroundkey-elem 2 0 state roundkey)
              (addroundkey-elem 2 1 state roundkey)
              (addroundkey-elem 2 2 state roundkey)
              (addroundkey-elem 2 3 state roundkey))
        (list (addroundkey-elem 3 0 state roundkey)
              (addroundkey-elem 3 1 state roundkey)
              (addroundkey-elem 3 2 state roundkey)
              (addroundkey-elem 3 3 state roundkey))))

(defthm statep-of-addroundkey
  (statep (addroundkey state roundkey))
  :hints (("Goal" :in-theory (enable addroundkey ADDROUNDKEY-ELEM))))

(defund apply-round (round state nk w)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8))
                              (integerp round)
                              (<= 1 round)
                              (<= round (+ -1 (nr nk)))
                              (statep state)
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (enable expanded-keyp))))
           (acl2::ignore nk) ; only used in the guard
           )
  (let* ((state (subbytes state))
         (state (shiftrows state))
         (state (mixcolumns state))
         (state (addroundkey state (subrange (* round *nb*) (+ (* (+ 1 round) *nb*) -1) w))))
    state))

;BOZO change things to remove the hyps on this?
(defthm statep-of-apply-round
  (implies (and; (expanded-keyp w)
                (statep state)
                (natp round)
                ;(< round 11)
                )
           (statep (apply-round round state nk w)))
  :hints (("Goal" :in-theory (e/d (apply-round) ()))))

(defund apply-rounds (round max state nk w)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8))
                              (equal max (+ -1 (nr nk)))
                              (integerp round)
                              (<= 1 round)
                              (<= round (+ 1 max))
                              (statep state)
                              (expanded-keyp w nk))
                  :measure (nfix (+ 1 max (- round)))))
  (if (or (< max round)
          (not (integerp max))
          (not (integerp round)))
      state
    (apply-rounds (+ 1 round) max (apply-round round state nk w) nk w)))

(defthm statep-of-apply-rounds
  (implies (and; (expanded-keyp w)
                (statep state)
                (natp round)
                ;(< round 11)
                )
           (statep (apply-rounds round max state nk w)))
  :hints (("Goal" :in-theory (e/d (apply-rounds) ()))))

(defund copyarraytostate (in)
  (declare (xargs :guard (byte-arrayp (* 4 *nb*) in)))
  (list (list (nth 0 in) (nth 4 in) (nth  8 in) (nth 12 in))
        (list (nth 1 in) (nth 5 in) (nth  9 in) (nth 13 in))
        (list (nth 2 in) (nth 6 in) (nth 10 in) (nth 14 in))
        (list (nth 3 in) (nth 7 in) (nth 11 in) (nth 15 in))))

(defthm statep-of-copyarraytostate
  (implies (inp input)
           (statep (copyarraytostate input)))
  :hints (("Goal" :in-theory (enable copyarraytostate))))

(defund copy-state-to-array (state)
  (declare (xargs :guard (statep state)))
  (list (array-elem-2d 0 0 state)
        (array-elem-2d 1 0 state)
        (array-elem-2d 2 0 state)
        (array-elem-2d 3 0 state)
        (array-elem-2d 0 1 state)
        (array-elem-2d 1 1 state)
        (array-elem-2d 2 1 state)
        (array-elem-2d 3 1 state)
        (array-elem-2d 0 2 state)
        (array-elem-2d 1 2 state)
        (array-elem-2d 2 2 state)
        (array-elem-2d 3 2 state)
        (array-elem-2d 0 3 state)
        (array-elem-2d 1 3 state)
        (array-elem-2d 2 3 state)
        (array-elem-2d 3 3 state)))

;this wasn't separate before, but it's better to keep things separate (in one
;implementation, the copy in and copy out are done in separate routines from
;the core encryption)
;w is the expanded key
(defund cipher-core (state w nk)
  (declare (xargs :guard (and (statep state)
                              (acl2::member nk '(4 6 8))
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (enable expanded-keyp)))))
  (let* ((state (addroundkey state (subrange 0 (+ -1 *nb*) w)))
         (state (apply-rounds 1 (+ -1 (nr nk)) state nk w)) ;most of the work is here
         (state (subbytes state))
         (state (shiftrows state))
         (state (addroundkey state (subrange (* (nr nk) *nb*) (+ -1 (* (+ 1 (nr nk)) *nb*)) w))))
    state))

(defthm statep-of-ciphercore
  (implies (aes::statep state)
           (aes::statep (aes::cipher-core state w nk)))
  :hints (("Goal" :in-theory (enable AES::CIPHER-CORE))))

;W is the expanded key
;IN is a list of 16 bytes
(defun cipher (in w nk)
  (declare (xargs :guard (and (inp in)
                              (acl2::member nk '(4 6 8))
                              (expanded-keyp w nk))))
 (let* ((state (copyarraytostate in))
         (state (cipher-core state w nk)))
    (copy-state-to-array state)))

(defund wordxor (x y)
  (declare (xargs :guard (and (wordp x)
                              (wordp y))))
  (make-word (bvxor 8 (wordbyte0 x) (wordbyte0 y))
             (bvxor 8 (wordbyte1 x) (wordbyte1 y))
             (bvxor 8 (wordbyte2 x) (wordbyte2 y))
             (bvxor 8 (wordbyte3 x) (wordbyte3 y))))

(defthm wordp-of-wordxor
  (implies (and (wordp x)
                (wordp y))
           (wordp (wordxor x y)))
  :hints (("Goal" :in-theory (enable ;wordp
                                     wordxor))))

(defund subword (word)
  (declare (xargs :guard (wordp word)))
  (make-word (nth (wordbyte0 word) (sbox))
             (nth (wordbyte1 word) (sbox))
             (nth (wordbyte2 word) (sbox))
             (nth (wordbyte3 word) (sbox))))

(defthm wordp-of-subword
  (implies (wordp word)
           (wordp (subword word)))
  :hints (("Goal" :in-theory (enable subword))))

(defund rotword (word)
  (declare (xargs :guard (wordp word)))
  (make-word (wordbyte1 word)
             (wordbyte2 word)
             (wordbyte3 word)
             (wordbyte0 word)))

(defthm wordp-of-rotword
  (implies (wordp word)
           (wordp (rotword word)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (rotword) ( ;ACL2::CONS-NTH-ONTO-SUBRANGE-ALT
;ACL2::CONS-OF-NTH-AND-NTH-PLUS-1
                                      ;;ACL2::SUBRANGE-TO-END-BECOMES-NTHCDR
                                      )))))

(defun xpow (n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil ;done below
                  ))
  (if (zp n)
      1
    (xtime (xpow (+ -1 n)))))

(defthm bytep-of-xpow
  (bytep (xpow n))
  :hints (("Goal" :in-theory (enable xpow))))

(acl2::verify-guards xpow)

(defun dummy () (declare (xargs :guard t)) '(0 0 0 0))

(defconst *rcon*
  (list (dummy) ;index 0 isn't used
        (make-word (xpow 0) 0 0 0)
        (make-word (xpow 1) 0 0 0)
        (make-word (xpow 2) 0 0 0)
        (make-word (xpow 3) 0 0 0)
        (make-word (xpow 4) 0 0 0)
        (make-word (xpow 5) 0 0 0)
        (make-word (xpow 6) 0 0 0)
        (make-word (xpow 7) 0 0 0)
        (make-word (xpow 8) 0 0 0)
        (make-word (xpow 9) 0 0 0)))

(defund keyexpansionloop1 (i nk key w)
  (declare (xargs :measure (nfix (+ 1 nk (- i)))
                  :guard (and (acl2::member nk '(4 6 8))
                              (natp i)
                              (keyp key nk)
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (enable expanded-keyp)))))
  (if (and (< i nk)
           (integerp i)
           (integerp nk))
      (let* ((w (update-nth i
                            (make-word (nth (* 4 i) key)
                                       (nth (+ (* 4 i) 1) key)
                                       (nth (+ (* 4 i) 2) key)
                                       (nth (+ (* 4 i) 3) key))
                            w))
             (i (+ 1 i)))
        (keyexpansionloop1 i nk key w))
    w))

(defthm expanded-keyp-of-KEYEXPANSIONLOOP1
  (implies (and (natp i)
                (natp nk)
                ;(<= i nk)
                ;(< nk (* *nb* (+ 1 (nr nk))))
                (keyp key nk)
                ;(<= (* 4 nk) (len key)) ;okay?
                ;(acl2::bv-arrayp 8 (len key) key)
                (expanded-keyp w nk)
                (equal len (* *nb* (+ 1 (nr nk))))
                )
           (expanded-keyp (keyexpansionloop1 i nk key w) nk))
  :hints (("Goal" :in-theory (e/d (KEYEXPANSIONLOOP1
                                   expanded-keyp
                            acl2::bv-arrayp) ( ;ACL2::NTH-TIMES
                                                          ;make-word
                                                          ))
           :do-not '(generalize eliminate-destructors))))

(defund keyexpansionloop2 (i bound nk w)
  (declare (xargs :measure (nfix (+ (- bound i) 1))
                  :guard (and (acl2::member nk '(4 6 8))
                              (integerp i)
                              (<= nk i)
                              (equal bound (* *nb* (+ 1 (nr nk))))
                              (<= i (+ 1 bound))
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (e/d (expanded-keyp)
                                                        (ACL2::BV-ARRAYP
                                                         acl2::mod-by-4-becomes-bvchop ;todo
                                                         ))))))
  (if (and (< i bound)
           (integerp i)
           (integerp bound))
      (let* ((temp (nth (+ -1 i) w))
             (temp (if (equal (mod i nk) 0)
                       (wordxor (subword (rotword temp)) (nth (/ i nk) *rcon*))
                     (if (and (> nk 6) (equal (mod i nk) 4))
                         (subword temp)
                       temp)))
             (w (update-nth i (wordxor (nth (- i nk) w) temp) w))
             (i (+ 1 i)))
        (keyexpansionloop2 i bound nk w))
    w))

(defthm expanded-keyp-of-keyexpansionloop2
  (implies (and (acl2::member nk '(4 6 8))
                (integerp i)
                (<= nk i)
                (equal bound (* *nb* (+ 1 (nr nk))))
                (<= i (+ 1 bound))
                (expanded-keyp w nk))
           (expanded-keyp (keyexpansionloop2 i bound nk w) nk))
  :hints (("Goal" :in-theory (e/d (keyexpansionloop2
                                   ;EXPANDED-KEYP
                                   )
                                  (acl2::bv-arrayp
                                   acl2::mod-by-4-becomes-bvchop ;todo
                                   acl2::update-nth))
           :do-not '(generalize eliminate-destructors)
           )))

;key is a list of (* 4 nk) usb8's
(defund keyexpansion (key nk)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8))
                              (keyp key nk))))
  (let* ((w (acl2::repeat (* *nb* (+ 1 (nr nk))) '(0 0 0 0))) ;the 0's get completely overwritten...
         (w (keyexpansionloop1 0 nk key w))
         (w (keyexpansionloop2 nk (* *nb* (+ 1 (nr nk))) nk w)))
    w))

(defthm expanded-keyp-of-keyexpansion
  (implies (and (keyp key nk)
                (acl2::member nk '(4 6 8)))
                     ;(expanded-keyp (keyexpansion key nk) nk)
           (expanded-keyp (KEYEXPANSION KEY NK) nk))
  :hints (("Goal"    ;:expand (:free (x y) (KEYEXPANSIONLOOP2 x y))
           :in-theory (e/d (keyexpansion (acl2::repeat)) ()))))

;prove that it returns the right type

;; in[16]: 128 bit plaintext, xxx bit key
;; out: 128 bit cipher text
;; copy plaintext into state
;; encrypt state
;; copy state to output

(defund invapply-round (round state nk w)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8))
                              (integerp round)
                              (<= 1 round)
                              (<= round (+ -1 (nr nk)))
                              (statep state)
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (enable expanded-keyp))))
           (acl2::ignore nk))
  (let* ((state (invshiftrows state))
         (state (invsubbytes state))
         (state (addroundkey state (subrange (* round *nb*) (+ -1 (* (+ 1 round) *nb*)) w)))
         (state (invmixcolumns state))
         )
    state))

(defthm statep-of-invapply-round
  (implies (and; (expanded-keyp w)
                (statep state)
                ;(natp round)
                ;(< round 11)
                )
           (statep (invapply-round round state nk w)))
  :hints (("Goal" :in-theory (e/d (invapply-round) ()))))

;;todo: make tailrecursive?
(defund invapply-rounds (currentround state w nk)
  (declare (xargs :guard (and (acl2::member nk '(4 6 8))
                              (natp currentround)
                              (<= currentround (+ -1 (nr nk)))
                              (statep state)
                              (expanded-keyp w nk))
                  :verify-guards nil ; done below
                  ))
  (if (zp currentround)
      state
    (invapply-round (- (nr nk) currentround)
                    (invapply-rounds (+ -1 currentround) state w nk)
                    nk
                    w)))

(defthm statep-of-invapply-rounds
  (implies (and; (expanded-keyp w)
                (statep state)
                (natp round)
                ;;(< round 11)
                (acl2::member nk '(4 6 8))
                )
           (statep (invapply-rounds round state w nk)))
  :hints (("Goal" :in-theory (e/d (invapply-rounds) ()))))

(acl2::verify-guards invapply-rounds)

(defund invcipher-core (state w nk)
  (declare (xargs :guard (and (statep state)
                              (acl2::member nk '(4 6 8))
                              (expanded-keyp w nk))
                  :guard-hints (("Goal" :in-theory (enable expanded-keyp)))))
  (let* ((state (addroundkey state (subrange (* (nr nk) *nb*) (+ -1 (* (+ 1 (nr nk)) *nb*)) w)))
         (state (invapply-rounds (+ -1 (nr nk)) state w nk)) ;most of the work is here
         (state (invshiftrows state))
         (state (invsubbytes state))
         (state (addroundkey state (subrange 0 (+ -1 *nb*) w))))
    state))

(defthm statep-of-invciphercore
  (implies (aes::statep state)
           (aes::statep (aes::invcipher-core state w nk)))
  :hints (("Goal" :in-theory (enable aes::invcipher-core))))

(defun invcipher (in w nk)
  (declare (xargs :guard (and (inp in)
                              (acl2::member nk '(4 6 8))
                              (expanded-keyp w nk))))
  (let* ((state (copyarraytostate in))
         (state (invcipher-core state w nk)))
    (copy-state-to-array state)))

;plaintext is a list of 16 bytes
;key is a list of 16 bytes
;returns a list of 16 bytes
(defun aes-128-encrypt (plaintext key)
  (declare (xargs :guard (and (inp plaintext)
                              (keyp key 4))))
  (let ((nk 4)) ;nk=4 means 128-bit AES (four 32-bit words)
    (cipher plaintext (keyexpansion key nk) nk)))

;ciphertext is a list of 16 bytes
;key is a list of 16 bytes
(defun aes-128-decrypt (ciphertext key)
  (declare (xargs :guard (and (inp ciphertext)
                              (keyp key 4))))
  (let ((nk 4)) ;nk=4 means 128-bit AES (four 32-bit words)
    (invcipher ciphertext (keyexpansion key nk) nk)))

;plaintext is a list of 16 bytes
;key is a list of 24 bytes
(defun aes-192-encrypt (plaintext key)
  (declare (xargs :guard (and (inp plaintext)
                              (keyp key 6))))
  (let ((nk 6)) ;nk=6 means 192-bit AES (six 32-bit words)
    (cipher plaintext (keyexpansion key nk) nk)))

;ciphertext is a list of 16 bytes
;key is a list of 24 bytes
(defun aes-192-decrypt (ciphertext key)
  (declare (xargs :guard (and (inp ciphertext)
                              (keyp key 6))))
  (let ((nk 6))      ;nk=6 means 192-bit AES (six 32-bit words)
    (invcipher ciphertext (keyexpansion key nk) nk)))

;plaintext is a list of 16 bytes
;key is a list of 32 bytes
(defun aes-256-encrypt (plaintext key)
  (declare (xargs :guard (and (inp plaintext)
                              (keyp key 8))))
  (let ((nk 8)) ;nk=8 means 256-bit AES (eight 32-bit words)
    (cipher plaintext (keyexpansion key nk) nk)))

;ciphertext is a list of 16 bytes
;key is a list of 32 bytes
(defun aes-256-decrypt (ciphertext key)
  (declare (xargs :guard (and (inp ciphertext)
                              (keyp key 8))))
  (let ((nk 8))      ;nk=8 means 256-bit AES (eight 32-bit words)
    (invcipher ciphertext (keyexpansion key nk) nk)))

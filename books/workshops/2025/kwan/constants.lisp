;; Book containing constants related to various machine models,
;; Modified from Y86 and CHERI-Y86 ACL2 books.
(in-package "ACL2")

(defconst *b-size*   8)  ; Byte
(defconst *w-size*  16)  ; Word
(defconst *d-size*  32)  ; Double
(defconst *q-size*  64)  ; Quad
(defconst *a-size*  64)  ; Physical address size
(defconst *m-size*  64)  ; Machine size

;  Memory size
(defconst *mem-size-in-bytes*  (expt 2 32))
(defconst *mem-size-in-words*  (floor *mem-size-in-bytes* 2))
(defconst *mem-size-in-dwords* (floor *mem-size-in-bytes* 4))
(defconst *mem-size-in-qwords* (floor *mem-size-in-bytes* 8))

; Some "useful" constants.  We define these because the ACL2
; definition mechanism does not evaluate and "fold" constants.
(defconst *2^0*       (expt 2  0))
(defconst *2^1*       (expt 2  1))
(defconst *2^2*       (expt 2  2))
(defconst *2^3*       (expt 2  3))
(defconst *2^4*       (expt 2  4))
(defconst *2^5*       (expt 2  5))
(defconst *2^6*       (expt 2  6))
(defconst *2^7*       (expt 2  7))
(defconst *2^8*       (expt 2  8))
(defconst *2^16*      (expt 2 16))
(defconst *2^24*      (expt 2 24))
(defconst *2^30*      (expt 2 30))
(defconst *2^32*      (expt 2 32))
(defconst *2^64*      (expt 2 64))

(defconst *2^16-1*    (- *2^16* 1))

(defconst *2^24-1*    (- *2^24*  1))
(defconst *2^24-2*    (- *2^24*  2))
(defconst *2^24-3*    (- *2^24*  3))
(defconst *2^24-4*    (- *2^24*  4))
(defconst *2^24-5*    (- *2^24*  5))
(defconst *2^24-6*    (- *2^24*  6))
(defconst *2^24-7*    (- *2^24*  7))
(defconst *2^24-8*    (- *2^24*  8))
(defconst *2^24-9*    (- *2^24*  9))
(defconst *2^24-10*   (- *2^24* 10))
(defconst *2^24-11*   (- *2^24* 11))
(defconst *2^24-12*   (- *2^24* 12))
(defconst *2^24-13*   (- *2^24* 13))
(defconst *2^24-14*   (- *2^24* 14))
(defconst *2^24-15*   (- *2^24* 15))
(defconst *2^24-16*   (- *2^24* 16))

(defconst *2^32-1*    (- *2^32*  1))
(defconst *2^32-2*    (- *2^32*  2))
(defconst *2^32-3*    (- *2^32*  3))
(defconst *2^32-4*    (- *2^32*  4))
(defconst *2^32-5*    (- *2^32*  5))
(defconst *2^32-6*    (- *2^32*  6))
(defconst *2^32-7*    (- *2^32*  7))
(defconst *2^32-8*    (- *2^32*  8))
(defconst *2^32-9*    (- *2^32*  9))
(defconst *2^32-10*   (- *2^32* 10))
(defconst *2^32-11*   (- *2^32* 11))
(defconst *2^32-12*   (- *2^32* 12))
(defconst *2^32-13*   (- *2^32* 13))
(defconst *2^32-14*   (- *2^32* 14))
(defconst *2^32-15*   (- *2^32* 15))
(defconst *2^32-16*   (- *2^32* 16))

(defconst *2^64-1*    (- *2^64*  1))
(defconst *2^64-2*    (- *2^64*  2))
(defconst *2^64-3*    (- *2^64*  3))
(defconst *2^64-4*    (- *2^64*  4))
(defconst *2^64-5*    (- *2^64*  5))
(defconst *2^64-6*    (- *2^64*  6))
(defconst *2^64-7*    (- *2^64*  7))
(defconst *2^64-8*    (- *2^64*  8))
(defconst *2^64-9*    (- *2^64*  9))
(defconst *2^64-10*   (- *2^64* 10))
(defconst *2^64-11*   (- *2^64* 11))
(defconst *2^64-12*   (- *2^64* 12))
(defconst *2^64-13*   (- *2^64* 13))
(defconst *2^64-14*   (- *2^64* 14))
(defconst *2^64-15*   (- *2^64* 15))
(defconst *2^64-16*   (- *2^64* 16))

(defun reg-nump (n)
  ;; n is a legal register number
  (and (natp n)
       (< n 32)))

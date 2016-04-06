;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of bit-vectors as lists
; Definitions of bit-vectors operations
;------------------------------------------


(in-package "ACL2")


(include-book "misc")

; Added by Matt K. in v2-9 to eliminate stack overflows in GCL in, at least,
; the proofs of last64-padding-1-256=length and last128-padding-512=length.
(set-verify-guards-eagerness 2)

;----def bit

; The definition of bitp here was deleted April 2016 by Matt K. now that
; bitp is defined in ACL2.


;--- bit operations

; or
(defun b-or (x y)
   (if (and (bitp x) (bitp y))
       (if (or (equal x 1) (equal y 1))
            1
            0)
       nil))

; and
(defun b-and (x y)
   (if (and (bitp x) (bitp y))
       (if (and (equal x 1) (equal y 1))
            1
            0)
       nil))

;not
(defun b-not (x)
   (if (bitp x)
       (if (equal x 0)
           1
           0)
       nil))

;xor
(defun  b-xor (x y)
   (if (and (bitp x) (bitp y))
       (if (or (and (equal x 1) (equal y 1))
               (and (equal x 0) (equal y 0)))
            0
            1)
       nil))

;----- def of a bit-vector

(defun bvp (m)
  (if (true-listp m)
      (if (endp m)
          t
          (and (bitp (car m))
               (bvp (cdr m))))
       nil))

;------ word of len i

(defun wordp (w i)
  (and (bvp w) (integerp i) (<= 0 i)
       (equal (len w) i)))


;------ vector of words each one with len i

(defun wvp (m i)
   (if  (and (true-listp m) (integerp i) (<= 0 i))
       (if (endp m)
            t
           (and (wordp (car m) i) (wvp (cdr m) i)))
       nil))





; transforms a bit-vector into the positive integer corresponding at the little-endian interpretation
; we treat only the unsigned case

(defun bv-int-little-endian (v)
   (if   (bvp v)
       (if (endp v)
           0
           (+  (car v) (* 2 ( bv-int-little-endian (cdr v)))))
      nil))

; Added by Matt K. to balance the earlier call of set-verify-guards-eagerness,
; since guard verification fails for the function bv-int-big-endian just
; below.
(set-verify-guards-eagerness 1)

; transforms v into the positive integer corresponding at the big-endian interpretation

(defun bv-int-big-endian (v)
   (bv-int-little-endian ( reverse v)))

; transforms a positive integer into the bit-vector corresponding to the little-endian interpretation
; we treat only the unsigned case

(defun int-bv-little-endian(i)
  (if (and (integerp i)
            (<= 0 i))
       (if  (equal (floor i 2) 0)
            (list (mod i 2))
            (cons (mod i 2) (int-bv-little-endian (floor i 2))))
    nil))


;  transforms i into the bit-vector corresponding at the big-endian interpretation of i

(defun int-bv-big-endian (i)
  (reverse (int-bv-little-endian i)))

; transforms a bit-vector v into a bit-vector of len n, if n is bigger then v's length. if not, returns the last n bits of v (v is considered in big-endian representation)

(defun bv-to-n (v n)
  (if (and (bvp v)
           (integerp n)
           (<= 0 n))
      (if  (>= n (len v))
           (append (make-list  (- n (len v)) :initial-element 0) v)
           (nthcdr (- (len v) n) v))
       nil))


;and between two bit-vectors with the same length

(defun bv-a (x y)
   (if (and (bvp x) (bvp y)
            (equal (len x) (len y)))
       (if (endp x) nil
           (cons (b-and (car x) (car y))
                 (bv-a (cdr x) (cdr y))))
       nil))



;and between two bit-vectors with arbitrary length

(defun binary-bv-and (x y)
  (if (and (bvp x) (bvp y))
      (if (<= (len x) (len y))
          (bv-a (bv-to-n x (len y)) y)
          (bv-a x (bv-to-n y (len x))))
      nil))


(defun bv-and-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'binary-bv-and (car lst)
                (bv-and-macro (cdr lst)))
          (car lst))
      nil))

(defmacro bv-and (&rest args)
   (bv-and-macro args))



;or between two bit-vectors with the same length

(defun bv-o (x y)
   (if (and (bvp x) (bvp y)
            (equal (len x) (len y)))
       (if (endp x) nil
           (cons (b-or (car x) (car y))
                 (bv-o (cdr x) (cdr y))))
       nil))

;or between two bit-vectors with arbitrary length

(defun binary-bv-or (x y)
  (if (and (bvp x) (bvp y))
      (if (<= (len x) (len y))
          (bv-o (bv-to-n x (len y)) y)
          (bv-o x (bv-to-n y (len x))))
      nil))

(defun bv-or-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'binary-bv-or (car lst)
                (bv-or-macro (cdr lst)))
          (car lst))
      nil))

(defmacro bv-or (&rest args)
   (bv-or-macro args))



;xor between two bit-vectors with the same length

(defun bv-xo (x y)
   (if (and (bvp x) (bvp y)
            (equal (len x) (len y)))
       (if (endp x) nil
           (cons (b-xor (car x) (car y))
                 (bv-xo (cdr x) (cdr y))))
       nil))



;xor between two bit-vectors with arbitrary length

(defun binary-bv-xor (x y)
  (if (and (bvp x) (bvp y))
      (if (<= (len x) (len y))
          (bv-xo (bv-to-n x (len y)) y)
          (bv-xo x (bv-to-n y (len x))))
      nil))

(defun bv-xor-macro (lst)
  (if (consp lst)
      (if (consp (cdr lst))
          (list 'binary-bv-xor (car lst)
                (bv-xor-macro (cdr lst)))
          (car lst))
      nil))

(defmacro bv-xor (&rest args)
   (bv-xor-macro args))


; not of a bit-vector x

(defun bv-not (x)
  (if (bvp x)
      (if (endp x)
           nil
          (cons (b-not (car x)) (bv-not (cdr x))))
      nil))



; addition modulo  (2 pow i) of two bit-vectors x and y

(defun binary-plus (i x y )
  (if (and (bvp x) (<= 0 (bv-int-big-endian x))
           (<=  (bv-int-big-endian x) (expt 2 i))
           (bvp y) (<= 0 (bv-int-big-endian y))
           (<=  (bv-int-big-endian y) (expt 2 i))
           (integerp i) (<= 0 i))
      (bv-to-n (int-bv-big-endian (mod (+  (bv-int-big-endian x)
                      (bv-int-big-endian y))  (expt 2 i))) i)
      nil))


(defun plus-macro (i lst )
  (if (and (consp lst) (integerp i) (<= 0 i))
      (if (consp (cdr lst))
          (list 'binary-plus i (car lst)
                (plus-macro i (cdr lst) ))
          (car lst))
      nil))

(defmacro plus (i &rest args )
   (plus-macro  i args ))

;auxiliary shift operations

(defun << (x n w)
   (if (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w))
       (cond ((zp n) x)
               ((endp x ) nil)
               (t  (append  (nthcdr n x) (make-list  n :initial-element 0) )))
       nil))

;ACL2 !>(<< '(1 1 1 1) 2 4)
;(1 1 0 0)


(defun >> (  x n w)
     (if (and (wordp x w)
           (integerp n)
           (<= 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
         (cond ((zp n) x)
               ((endp x ) nil)
               (t  (append (make-list  n :initial-element 0) (firstn (- (len x) n)  x) ) ))
          nil))

;ACL2 !>(>> '(1 1 1 1) 2 4)
;(0 0 1 1)

;right shift of x with n elements on w bits

(defun shr (n x w)
     (if (and (wordp x w)
           (integerp n)
           (<= 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
        (>>  x n w) nil))


;rotate right (circular right shift) of x with n elements on w bits

(defun rotr (n x w)
     (if (and (wordp x w)
           (integerp n)
           (<= 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
        (bv-or (>>  x n w) (<< x (- w n) w)) nil))

;rotate left (circular left shift) of x with n elements on w bits

(defun rotl (n x w)
     (if (and (wordp x w)
           (integerp n)
           (<= 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
        (bv-or (<<  x n w) (>> x (- w n) w)) nil))

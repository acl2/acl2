;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHAs
; Padding function for SHA-384 and SHA-512
;------------------------------------------

;I strongly recommend after charging the book to do :comp t in order to accelerate the computation

(IN-PACKAGE "ACL2")

(include-book "bv-op-defthms")

;---padding
;for sha-512 and sha-384
;Let M be a message of length len bits. The purpose of padding is to extend M to  a multiple of 1024 bits. To obtain the padded message, append the bit 1 to the end of message M, followed by k zero bits, where k is the smallest, non-negative solution to the equation (len+1+k) mod 1024 = 896. Then append the 128-bit binary representation of number len.

;For example, the (8-bit ASCII) message ``abc'' has the length 8*3=24, so the message is padded with one bit, then 896-(24+1)=871 zero bits, and then the message length, to become the 1024-bit padded message:

;ACL2 !>(padding-512 ' (0 1 1 0 0 0 0 1  0 1 1 0 0 0 1 0  0 1 1 0 0 0 1 1 ))
;(0 1 1 0
;   0 0 0 1 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1
;   1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
;   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0)

(local
(defthm 2n<i
  (implies (and (integerp n) (< 0 n) (integerp i)
                (<  n i) (integerp (* i (/ n))) )
           (<= 2 (* i (/ n) )))))

(local
(defthm n<=i
  (implies (and (integerp n) (< 0 n) (integerp i)
                (equal (mod  i n) 0) (< 0 i) )
           (<= n i) )))



(defun padding-512 (m)
 (if (and (bvp m)
          (< (len m) (expt 2 128)))
     (if (<= (mod (1+ (len m)) 1024) 896)
         (append  m (list 1)
                 (make-list (- 896 (mod (1+ (len m)) 1024))
                           :initial-element 0)
                 (bv-to-n (int-bv-big-endian (len m)) 128))
         (append   m (list 1)
                 (make-list (- 1920 (mod (1+ (len m)) 1024))
                    :initial-element 0 )
                 (bv-to-n (int-bv-big-endian (len m)) 128)))
      nil))


(defthm bvp-padding-512
  (bvp (padding-512 m)))


(defthm len-padding-512
 (implies (and (bvp m)
         (< (len m) (expt 2 128)))
  (<= 1024 (len (padding-512 m))))
:hints
(("Goal"
  :in-theory (disable mod  MOD-ZERO  ASSOCIATIVITY-OF-+  ))
("subgoal 2"
  :use (:instance simplify-mod-+-mod1 (w (+ 1921 (len m)))
                    (x (+ 1 (len m))) (y 1024) (z 1024) ))
("subgoal 1"
  :use (:instance simplify-mod-+-mod1 (w (+ 897 (len m)))
                 (x (+ 1 (len m))) (y 1024) (z 1024) ))))



(defthm len-padding-512-mod-1024=0
  (implies (bvp m)
           (equal (mod (len (padding-512 m)) 1024) 0))
:hints
(("Goal"
  :in-theory (disable  MOD-ZERO int-bv-big-endian ))
("subgoal 2"
  :use (:instance simplify-mod-+-mod1 (w (+ 2049 (len m)))
                    (x (+ 1 (len m))) (y 1024) (z 1024) ))
("subgoal 1"
  :use (:instance simplify-mod-+-mod1 (w (+ 1025 (len m)))
                  (x (+ 1 (len m))) (y 1024) (z 1024) ))))


(local
(defthm last-512-aux
 (implies   (and (BVP M)
          (< (LEN M) 340282366920938463463374607431768211456)
          (< 896 (MOD (+ 1 (LEN M)) 1024))
          (<= (NFIX (+ 1 (LEN M)
                   1920 (- (MOD (+ 1 (LEN M)) 1024))))
          (LEN M)))
         (<= 1921 (MOD (+ 1 (LEN M)) 1024) ))))



(defthm last128-padding-512=length
   (implies (and (bvp m) (< (len m) (expt 2 128)))
            (equal (bv-int-big-endian
                        (nthcdr (- (len (padding-512 m)) 128)
                                  (padding-512 m)))
                  (len m)))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian ))
("subgoal 2.2" :use  last-512-aux)))



(defthm end-message-padding-512
   (implies (and (bvp m) (< (len m) (expt 2 128)))
            (equal (nth (len m) (padding-512 m)) 1))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian ))))



(defthm first-padding-512=message
   (implies (and (bvp m) (< (len m) (expt 2 128)))
            (equal (firstn ( len m) (padding-512 m)) m))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian nthcdr   ))))



(defthm 0-fill-padding-512
   (implies (and (bvp m) (< (len m) (expt 2 128)))
            (equal (segment (1+ (len m))
                            (- (len (padding-512 m)) 128)
                            (padding-512 m))
                  (make-list (- (len (padding-512 m)) (+ 129 (len m)))
                      :initial-element 0))))


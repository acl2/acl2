;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHAs
; Padding function for SHA-1 and SHA-256
;------------------------------------------

;I strongly recommend after charging the book to do :comp t in order to accelerate the computation

(IN-PACKAGE "ACL2")

(include-book "bv-op-defthms")

;---padding
;for sha-1 and sha-256

;Let M be a message of length len bits. The purpose of padding is to extend M to  a multiple of 512 bits. To obtain the padded message, append the bit 1 to the end of message M, followed by k zero bits, where k is the smallest, non-negative solution to the equation (len+1+k) mod 512 = 448. Then append the 64-bit binary representation of number len.

;For example, the (8-bit ASCII) message ``abc'' has the length 8*3=24, so the message is padded with one bit, then 448-(24+1)=423 zero bits, and then the message length, to become the 512-bit padded message:

;ACL2 !>(padding-1-256 ' (0 1 1 0 0 0 0 1  0 1 1 0 0 0 1 0  0 1 1 0 0 0 1 1 ))
;(0 1 1 0 0 0 0 1 0 1 1 0
;   0 0 1 0 0 1 1 0 0 0 1 1 1 0 0 0 0 0 0 0
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

(defun padding-1-256 (m)
 (if (and (bvp m)
          (< (len m) (expt 2 64)))
     (if (<= (mod (1+ (len m)) 512) 448)
         (append  m (list 1)
                 (make-list (- 448 (mod (1+ (len m)) 512)):initial-element 0 )
                 (bv-to-n (int-bv-big-endian (len m)) 64))
         (append   m (list 1)
                 (make-list (- 960 (mod (1+ (len m)) 512)):initial-element 0 )
                 (bv-to-n (int-bv-big-endian (len m)) 64)))
      nil))


(defthm bvp-padding-1-256
  (bvp (padding-1-256 m)))


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


(defthm len-padding-1-256
 (implies (and (bvp m)
          (< (len m) (expt 2 64)))
  (<= 512 (len (padding-1-256 m))))
:hints
(("Goal"
  :in-theory (disable mod  MOD-ZERO  ASSOCIATIVITY-OF-+  ))
("subgoal 2"
  :use (:instance simplify-mod-+-mod1 (w (+ 1025 (len m)))
                      (x (+ 1 (len m))) (y 512) (z 512) ))
("subgoal 1"
  :use (:instance simplify-mod-+-mod1 (w (+ 513 (len m)))
                   (x (+ 1 (len m))) (y 512) (z 512) ))))



(defthm len-padding-1-256-mod-512=0
  (implies (bvp m)
           (equal (mod (len (padding-1-256 m)) 512) 0))
:hints
(("Goal"
  :in-theory (disable  MOD-ZERO int-bv-big-endian  ))
("subgoal 2"
  :use (:instance simplify-mod-+-mod1 (w (+ 1025 (len m)))
                      (x (+ 1 (len m))) (y 512) (z 512) ))
("subgoal 1"
  :use (:instance simplify-mod-+-mod1 (w (+ 513 (len m)))
                   (x (+ 1 (len m))) (y 512) (z 512) ))))



(local
(defthm last-256-aux
 (implies (and (BVP M)
            (< (LEN M) 18446744073709551616)
            (< 448 (MOD (+ 1 (LEN M)) 512))
            (<= (nfix (+ 1 (LEN M) 960 (- (MOD (+ 1 (LEN M)) 512)))) (LEN M)))
          (<= 961 (MOD (+ 1 (LEN M)) 512)))))



(defthm last64-padding-1-256=length
   (implies (and (bvp m) (< (len m) (expt 2 64)))
            (equal (bv-int-big-endian
                        (nthcdr (- (len (padding-1-256 m)) 64)
                                  (padding-1-256 m)))
                  (len m)))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian  ))
("subgoal 2.2" :use last-256-aux)))



(defthm end-message-padding-1-256
   (implies (and (bvp m) (< (len m) (expt 2 64)))
            (equal (nth (len m) (padding-1-256 m)) 1))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian ))))



(defthm first-padding-1-256=message
   (implies (and (bvp m) (< (len m) (expt 2 64)))
            (equal (firstn ( len m) (padding-1-256 m))  m))
:hints
(("Goal"
  :in-theory (disable bv-int-big-endian int-bv-big-endian nthcdr ))))



(defthm 0-fill-padding-1-256
   (implies (and (bvp m) (< (len m) (expt 2 64)))
            (equal (segment (1+ (len m))
                            (- (len (padding-1-256 m)) 64)
                            (padding-1-256 m))
                  (make-list (- (len (padding-1-256 m)) (+ 65 (len m)))
                           :initial-element 0))))


; For message "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", with length 448

;ACL2 !>(padding-1-256 '(0 1 1 0 0 0 0 1
;   0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1 0 1 1 0
;   0 1 0 0 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1
;   0 1 1 0 0 1 0 0 0 1 1 0 0 1 0 1 0 1 1 0
;   0 0 1 1 0 1 1 0 0 1 0 0 0 1 1 0 0 1 0 1
;   0 1 1 0 0 1 1 0 0 1 1 0 0 1 0 0 0 1 1 0
;   0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 0 0 1 1 1
;   0 1 1 0 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 0
;   0 1 1 1 0 1 1 0 1 0 0 0 0 1 1 0 0 1 1 0
;   0 1 1 0 0 1 1 1 0 1 1 0 1 0 0 0 0 1 1 0
;   1 0 0 1 0 1 1 0 0 1 1 1 0 1 1 0 1 0 0 0
;   0 1 1 0 1 0 0 1 0 1 1 0 1 0 1 0 0 1 1 0
;   1 0 0 0 0 1 1 0 1 0 0 1 0 1 1 0 1 0 1 0
;   0 1 1 0 1 0 1 1 0 1 1 0 1 0 0 1 0 1 1 0
;   1 0 1 0 0 1 1 0 1 0 1 1 0 1 1 0 1 1 0 0
;   0 1 1 0 1 0 1 0 0 1 1 0 1 0 1 1 0 1 1 0
;   1 1 0 0 0 1 1 0 1 1 0 1 0 1 1 0 1 0 1 1
;   0 1 1 0 1 1 0 0 0 1 1 0 1 1 0 1 0 1 1 0
;   1 1 1 0 0 1 1 0 1 1 0 0 0 1 1 0 1 1 0 1
;   0 1 1 0 1 1 1 0 0 1 1 0 1 1 1 1 0 1 1 0
;   1 1 0 1 0 1 1 0 1 1 1 0 0 1 1 0 1 1 1 1
;   0 1 1 1 0 0 0 0 0 1 1 0 1 1 1 0 0 1 1 0
;   1 1 1 1 0 1 1 1 0 0 0 0 0 1 1 1 0 0 0 1))
;Padding has 1024 bits
; (0 1 1 0
;   0 0 0 1 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1
;   0 1 1 0 0 1 0 0 0 1 1 0 0 0 1 0 0 1 1 0
;   0 0 1 1 0 1 1 0 0 1 0 0 0 1 1 0 0 1 0 1
;   0 1 1 0 0 0 1 1 0 1 1 0 0 1 0 0 0 1 1 0
;   0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 0 0 1 0 0
;   0 1 1 0 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 0
;   0 1 1 1 0 1 1 0 0 1 0 1 0 1 1 0 0 1 1 0
;   0 1 1 0 0 1 1 1 0 1 1 0 1 0 0 0 0 1 1 0
;   0 1 1 0 0 1 1 0 0 1 1 1 0 1 1 0 1 0 0 0
;   0 1 1 0 1 0 0 1 0 1 1 0 0 1 1 1 0 1 1 0
;   1 0 0 0 0 1 1 0 1 0 0 1 0 1 1 0 1 0 1 0
;   0 1 1 0 1 0 0 0 0 1 1 0 1 0 0 1 0 1 1 0
;   1 0 1 0 0 1 1 0 1 0 1 1 0 1 1 0 1 0 0 1
;   0 1 1 0 1 0 1 0 0 1 1 0 1 0 1 1 0 1 1 0
;   1 1 0 0 0 1 1 0 1 0 1 0 0 1 1 0 1 0 1 1
;   0 1 1 0 1 1 0 0 0 1 1 0 1 1 0 1 0 1 1 0
;   1 0 1 1 0 1 1 0 1 1 0 0 0 1 1 0 1 1 0 1
;   0 1 1 0 1 1 1 0 0 1 1 0 1 1 0 0 0 1 1 0
;   1 1 0 1 0 1 1 0 1 1 1 0 0 1 1 0 1 1 1 1
;   0 1 1 0 1 1 0 1 0 1 1 0 1 1 1 0 0 1 1 0
;   1 1 1 1 0 1 1 1 0 0 0 0 0 1 1 0 1 1 1 0
;   0 1 1 0 1 1 1 1 0 1 1 1 0 0 0 0 0 1 1 1
;   0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
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
;   0 0 0 0 0 0 0 0 0 0 0 1 1 1 0 0 0 0 0 0)
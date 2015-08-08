;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHA-256
; Message digest functions and theorems
;------------------------------------------

(IN-PACKAGE "ACL2")

(include-book "parsing")
(include-book "sha-functions")

;I strongly recommend after charging the book to do :comp t in order to accelerate the computation

; For a message M with length less than (expt 2 64) sha-1 returns a message digest of 256 bits (eight words each of 32 bits).

;For message "abc"
;ACL2 !>(sha-256 '(0 1 1 0 0 0 0 1 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1 ))
;((1 0 1 1 1 0 1 0 0 1 1 1
;    1 0 0 0 0 0 0 1 0 1 1 0 1 0 1 1 1 1 1 1)
; (1 0 0 0 1 1 1 1 0 0 0 0
;    0 0 0 1 1 1 0 0 1 1 1 1 1 1 1 0 1 0 1 0)
; (0 1 0 0 0 0 0 1 0 1 0 0
;    0 0 0 1 0 1 0 0 0 0 0 0 1 1 0 1 1 1 1 0)
; (0 1 0 1 1 1 0 1 1 0 1 0
;    1 1 1 0 0 0 1 0 0 0 1 0 0 0 1 0 0 0 1 1)
; (1 0 1 1 0 0 0 0 0 0 0 0
;    0 0 1 1 0 1 1 0 0 0 0 1 1 0 1 0 0 0 1 1)
; (1 0 0 1 0 1 1 0 0 0 0 1
;    0 1 1 1 0 1 1 1 1 0 1 0 1 0 0 1 1 1 0 0)
; (1 0 1 1 0 1 0 0 0 0 0 1
;    0 0 0 0 1 1 1 1 1 1 1 1 0 1 1 0 0 0 0 1)
; (1 1 1 1 0 0 1 0 0 0 0 0 0
;   0 0 0 0 0 0 1 0 1 0 1 1 0 1 0 1 1 0 1))

;For the message "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (448 bits)
;ACL2 !>(sha-256 '(0 1 1 0 0 0 0 1
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

; The result:

;((0 0 1 0 0 1 0 0 1 0 0 0
;    1 1 0 1 0 1 1 0 1 0 1 0 0 1 1 0 0 0 0 1)
; (1 1 0 1 0 0 1 0 0 0 0 0
;    0 1 1 0 0 0 1 1 1 0 0 0 1 0 1 1 1 0 0 0)
; (1 1 1 0 0 1 0 1 1 1 0 0
;    0 0 0 0 0 0 1 0 0 1 1 0 1 0 0 1 0 0 1 1)
; (0 0 0 0 1 1 0 0 0 0 1 1
;    1 1 1 0 0 1 1 0 0 0 0 0 0 0 1 1 1 0 0 1)
; (1 0 1 0 0 0 1 1 0 0 1 1
;    1 1 0 0 1 1 1 0 0 1 0 0 0 1 0 1 1 0 0 1)
; (0 1 1 0 0 1 0 0 1 1 1 1
;    1 1 1 1 0 0 1 0 0 0 0 1 0 1 1 0 0 1 1 1)
; (1 1 1 1 0 1 1 0 1 1 1 0
;    1 1 0 0 1 1 1 0 1 1 0 1 1 1 0 1 0 1 0 0)
; (0 0 0 1 1 0 0 1 1 1 0 1 1
;    0 1 1 0 0 0 0 0 1 1 0 1 1 0 0 0 0 0 1))

; constants of sha-256
(defun K-256 (i)
   (cond ((equal i 0)
        '(0 1 0 0 0 0 1 0 1 0 0 0
   1 0 1 0 0 0 1 0 1 1 1 1 1 0 0 1 1 0 0 0))
         ((equal i 1)
        '(0 1 1 1 0 0 0 1 0 0 1 1
   0 1 1 1 0 1 0 0 0 1 0 0 1 0 0 1 0 0 0 1))
         ((equal i 2) '(1 0 1 1 0 1 0 1 1 1 0 0
   0 0 0 0 1 1 1 1 1 0 1 1 1 1 0 0 1 1 1 1))
         ((equal i 3) '(1 1 1 0 1 0 0 1 1 0 1 1
   0 1 0 1 1 1 0 1 1 0 1 1 1 0 1 0 0 1 0 1))
         ((equal i 4) '(0 0 1 1 1 0 0 1 0 1 0 1
   0 1 1 0 1 1 0 0 0 0 1 0 0 1 0 1 1 0 1 1))
         ((equal i 5) '(0 1 0 1 1 0 0 1 1 1 1 1
   0 0 0 1 0 0 0 1 0 0 0 1 1 1 1 1 0 0 0 1))
         ((equal i 6) '(1 0 0 1 0 0 1 0 0 0 1 1
   1 1 1 1 1 0 0 0 0 0 1 0 1 0 1 0 0 1 0 0))
         ((equal i 7) '(1 0 1 0 1 0 1 1 0 0 0 1
   1 1 0 0 0 1 0 1 1 1 1 0 1 1 0 1 0 1 0 1))
         ((equal i 8) '(1 1 0 1
   1 0 0 0 0 0 0 0 0 1 1 1 1 0 1 0 1 0 1 0
   1 0 0 1 1 0 0 0))
         ((equal i 9) '(0 0 0 1
   0 0 1 0 1 0 0 0 0 0 1 1 0 1 0 1 1 0 1 1
   0 0 0 0 0 0 0 1))
         ((equal i 10) '(0 0 1 0
   0 1 0 0 0 0 1 1 0 0 0 1 1 0 0 0 0 1 0 1
   1 0 1 1 1 1 1 0))
         ((equal i 11) '(0 1 0 1
   0 1 0 1 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 1
   1 1 0 0 0 0 1 1))
         ((equal i 12) '(0 1 1 1
   0 0 1 0 1 0 1 1 1 1 1 0 0 1 0 1 1 1 0 1
   0 1 1 1 0 1 0 0))
         ((equal i 13) '(1 0 0 0
   0 0 0 0 1 1 0 1 1 1 1 0 1 0 1 1 0 0 0 1
   1 1 1 1 1 1 1 0))
         ((equal i 14) '(1 0 0 1
   1 0 1 1 1 1 0 1 1 1 0 0 0 0 0 0 0 1 1 0
   1 0 1 0 0 1 1 1))
         ((equal i 15) '(1 1 0 0
   0 0 0 1 1 0 0 1 1 0 1 1 1 1 1 1 0 0 0 1
   0 1 1 1 0 1 0 0))
         ((equal i 16) '(1 1 1 0
   0 1 0 0 1 0 0 1 1 0 1 1 0 1 1 0 1 0 0 1
   1 1 0 0 0 0 0 1))
         ((equal i 17) '(1 1 1 0
   1 1 1 1 1 0 1 1 1 1 1 0 0 1 0 0 0 1 1 1
   1 0 0 0 0 1 1 0))
         ((equal i 18) '(0 0 0 0
   1 1 1 1 1 1 0 0 0 0 0 1 1 0 0 1 1 1 0 1
   1 1 0 0 0 1 1 0))
         ((equal i 19) '(0 0 1 0
   0 1 0 0 0 0 0 0 1 1 0 0 1 0 1 0 0 0 0 1
   1 1 0 0 1 1 0 0))
         ((equal i 20) '(0 0 1 0
   1 1 0 1 1 1 1 0 1 0 0 1 0 0 1 0 1 1 0 0
   0 1 1 0 1 1 1 1))
         ((equal i 21) '(0 1 0 0
   1 0 1 0 0 1 1 1 0 1 0 0 1 0 0 0 0 1 0 0
   1 0 1 0 1 0 1 0))
         ((equal i 22) '(0 1 0 1
   1 1 0 0 1 0 1 1 0 0 0 0 1 0 1 0 1 0 0 1
   1 1 0 1 1 1 0 0))
         ((equal i 23) '(0 1 1 1
   0 1 1 0 1 1 1 1 1 0 0 1 1 0 0 0 1 0 0 0
   1 1 0 1 1 0 1 0))
         ((equal i 24) '(1 0 0 1
   1 0 0 0 0 0 1 1 1 1 1 0 0 1 0 1 0 0 0 1
   0 1 0 1 0 0 1 0))
         ((equal i 25) '(1 0 1 0
   1 0 0 0 0 0 1 1 0 0 0 1 1 1 0 0 0 1 1 0
   0 1 1 0 1 1 0 1))
         ((equal i 26) '(1 0 1 1
   0 0 0 0 0 0 0 0 0 0 1 1 0 0 1 0 0 1 1 1
   1 1 0 0 1 0 0 0))
         ((equal i 27) '(1 0 1 1
   1 1 1 1 0 1 0 1 1 0 0 1 0 1 1 1 1 1 1 1
   1 1 0 0 0 1 1 1))
         ((equal i 28) '(1 1 0 0
   0 1 1 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 1 1
   1 1 1 1 0 0 1 1 ))
         ((equal i 29) '(1 1 0 1
   0 1 0 1 1 0 1 0 0 1 1 1 1 0 0 1 0 0 0 1
   0 1 0 0 0 1 1 1 ))
         ((equal i 30) '(0 0 0 0
   0 1 1 0 1 1 0 0 1 0 1 0 0 1 1 0 0 0 1 1
   0 1 0 1 0 0 0 1 ))
         ((equal i 31) '(0 0 0 1
   0 1 0 0 0 0 1 0 1 0 0 1 0 0 1 0 1 0 0 1
   0 1 1 0 0 1 1 1))
         ((equal i 32) '(0 0 1 0
   0 1 1 1 1 0 1 1 0 1 1 1 0 0 0 0 1 0 1 0
   1 0 0 0 0 1 0 1))
         ((equal i 33) '(0 0 1 0
   1 1 1 0 0 0 0 1 1 0 1 1 0 0 1 0 0 0 0 1
   0 0 1 1 1 0 0 0 ))
         ((equal i 34) '(0 1 0 0
   1 1 0 1 0 0 1 0 1 1 0 0 0 1 1 0 1 1 0 1
   1 1 1 1 1 1 0 0))
         ((equal i 35) '(0 1 0 1
   0 0 1 1 0 0 1 1 1 0 0 0 0 0 0 0 1 1 0 1
   0 0 0 1 0 0 1 1 ))
         ((equal i 36) '(0 1 1 0 0 1 0 1 0 0 0 0
   1 0 1 0 0 1 1 1 0 0 1 1 0 1 0 1 0 1 0 0))
         ((equal i 37) '(0 1 1 1
   0 1 1 0 0 1 1 0 1 0 1 0 0 0 0 0 1 0 1 0
   1 0 1 1 1 0 1 1))
         ((equal i 38) '(1 0 0 0
   0 0 0 1 1 1 0 0 0 0 1 0 1 1 0 0 1 0 0 1
   0 0 1 0 1 1 1 0))
         ((equal i 39) '(1 0 0 1
   0 0 1 0 0 1 1 1 0 0 1 0 0 0 1 0 1 1 0 0
   1 0 0 0 0 1 0 1))
         ((equal i 40) '(1 0 1 0
   0 0 1 0 1 0 1 1 1 1 1 1 1 1 1 0 1 0 0 0
   1 0 1 0 0 0 0 1 ))
         ((equal i 41) '(1 0 1 0
   1 0 0 0 0 0 0 1 1 0 1 0 0 1 1 0 0 1 1 0
   0 1 0 0 1 0 1 1))
         ((equal i 42) '(1 1 0 0
   0 0 1 0 0 1 0 0 1 0 1 1 1 0 0 0 1 0 1 1
   0 1 1 1 0 0 0 0 ))
         ((equal i 43) '(1 1 0 0
   0 1 1 1 0 1 1 0 1 1 0 0 0 1 0 1 0 0 0 1
   1 0 1 0 0 0 1 1))
         ((equal i 44) '(1 1 0 1
   0 0 0 1 1 0 0 1 0 0 1 0 1 1 1 0 1 0 0 0
   0 0 0 1 1 0 0 1 ))
         ((equal i 45) '(1 1 0 1
   0 1 1 0 1 0 0 1 1 0 0 1 0 0 0 0 0 1 1 0
   0 0 1 0 0 1 0 0 ))
         ((equal i 46) '(1 1 1 1
   0 1 0 0 0 0 0 0 1 1 1 0 0 0 1 1 0 1 0 1
   1 0 0 0 0 1 0 1 ))
         ((equal i 47) '(0 0 0 1
   0 0 0 0 0 1 1 0 1 0 1 0 1 0 1 0 0 0 0 0
   0 1 1 1 0 0 0 0))
         ((equal i 48) '(0 0 0 1
   1 0 0 1 1 0 1 0 0 1 0 0 1 1 0 0 0 0 0 1
   0 0 0 1 0 1 1 0 ))
         ((equal i 49) '(0 0 0 1
   1 1 1 0 0 0 1 1 0 1 1 1 0 1 1 0 1 1 0 0
   0 0 0 0 1 0 0 0))
         ((equal i 50) '(0 0 1 0
   0 1 1 1 0 1 0 0 1 0 0 0 0 1 1 1 0 1 1 1
   0 1 0 0 1 1 0 0 ))
         ((equal i 51) '(0 0 1 1
   0 1 0 0 1 0 1 1 0 0 0 0 1 0 1 1 1 1 0 0
   1 0 1 1 0 1 0 1 ))
         ((equal i 52) '(0 0 1 1
   1 0 0 1 0 0 0 1 1 1 0 0 0 0 0 0 1 1 0 0
   1 0 1 1 0 0 1 1 ))
         ((equal i 53) '(0 1 0 0
   1 1 1 0 1 1 0 1 1 0 0 0 1 0 1 0 1 0 1 0
   0 1 0 0 1 0 1 0 ))
         ((equal i 54) '(0 1 0 1
   1 0 1 1 1 0 0 1 1 1 0 0 1 1 0 0 1 0 1 0
   0 1 0 0 1 1 1 1 ))
         ((equal i 55) '(0 1 1 0
   1 0 0 0 0 0 1 0 1 1 1 0 0 1 1 0 1 1 1 1
   1 1 1 1 0 0 1 1 ))
         ((equal i 56) '(0 1 1 1
   0 1 0 0 1 0 0 0 1 1 1 1 1 0 0 0 0 0 1 0
   1 1 1 0 1 1 1 0))
         ((equal i 57) '(0 1 1 1
   1 0 0 0 1 0 1 0 0 1 0 1 0 1 1 0 0 0 1 1
   0 1 1 0 1 1 1 1 ))
         ((equal i 58) '(1 0 0 0
   0 1 0 0 1 1 0 0 1 0 0 0 0 1 1 1 1 0 0 0
   0 0 0 1 0 1 0 0 ))
         ((equal i 59) '(1 0 0 0
   1 1 0 0 1 1 0 0 0 1 1 1 0 0 0 0 0 0 1 0
   0 0 0 0 1 0 0 0 ))
         ((equal i 60) '(1 0 0 1
   0 0 0 0 1 0 1 1 1 1 1 0 1 1 1 1 1 1 1 1
   1 1 1 1 1 0 1 0 ))
         ((equal i 61) '(1 0 1 0
   0 1 0 0 0 1 0 1 0 0 0 0 0 1 1 0 1 1 0 0
   1 1 1 0 1 0 1 1 ))
         ((equal i 62) '(1 0 1 1
   1 1 1 0 1 1 1 1 1 0 0 1 1 0 1 0 0 0 1 1
   1 1 1 1 0 1 1 1 ))
         ((equal i 63) '(1 1 0 0
   0 1 1 0 0 1 1 1 0 0 0 1 0 1 1 1 1 0 0 0
   1 1 1 1 0 0 1 0))
         (t   nil)))

(defthm wordp-K-256
(implies (and (integerp i) (<= 0 i) (<= i 63))
  (wordp (k-256 i) 32)))


; initial hash values for sha-256
(defun h-256 ()
'((0 1 1 0 1 0 1 0 0 0 0 0
   1 0 0 1 1 1 1 0 0 1 1 0 0 1 1 0 0 1 1 1)
(1 0 1 1 1 0 1 1 0 1 1 0
   0 1 1 1 1 0 1 0 1 1 1 0 1 0 0 0 0 1 0 1)
(0 0 1 1 1 1 0 0 0 1 1 0
   1 1 1 0 1 1 1 1 0 0 1 1 0 1 1 1 0 0 1 0)
(1 0 1 0 0 1 0 1 0 1 0 0
   1 1 1 1 1 1 1 1 0 1 0 1 0 0 1 1 1 0 1 0)
(0 1 0 1 0 0 0 1 0 0 0 0
   1 1 1 0 0 1 0 1 0 0 1 0 0 1 1 1 1 1 1 1)
(1 0 0 1 1 0 1 1 0 0 0 0
   0 1 0 1 0 1 1 0 1 0 0 0 1 0 0 0 1 1 0 0)
(0 0 0 1 1 1 1 1 1 0 0 0
   0 0 1 1 1 1 0 1 1 0 0 1 1 0 1 0 1 0 1 1)
(0 1 0 1 1 0 1 1 1 1 1 0
   0 0 0 0 1 1 0 0 1 1 0 1 0 0 0 1 1 0 0 1))
)

(defthm wordp-h-256
 (and  (wvp (h-256) 32) (equal (len (h-256)) 8 )))


;-----sha-256

(defun prepare-256-ac ( j m-i)
(declare (xargs :measure (acl2-count (- 64 j))))
  (if (and (wvp m-i 32) (integerp j) (<= 16 j))
      (cond ((<= 64 j) m-i)
            ((<= j 63)
             (prepare-256-ac (1+ j)  (append m-i
                  (list (plus 32 (s-1-256 (nth (- j 2) m-i))
                        (nth (- j 7) m-i)
                        (s-0-256 (nth (- j 15) m-i))
                        (nth (- j 16) m-i) ))))))
      nil))


(defun prepare-256 (m-i)
  (if (wordp m-i 512)
      (prepare-256-ac 16 (parsing m-i 32))
      nil))


(defthm wvp-prepare-256-ac
  (implies (and  (integerp j) (<= 16 j) (wvp  m 32))
           (wvp (prepare-256-ac j m) 32))
:hints
(("goal"
  :in-theory (disable s-1-256 s-0-256 nth binary-plus ))))


(defthm len-prepare-256-ac
  (implies (and  (wvp  m 32) (integerp j) (<= 16 j) (<= j (len m) ))
       (equal (len (prepare-256-ac  j m))
              (if  (<= j 64)
                   (+ (- 64 j) (len m))
                   (len m))))
:hints
(("goal"
  :in-theory (disable s-1-256 s-0-256 nth binary-plus ))))


(defthm wvp-prepare-256
  (implies (wordp  m 512)
           (wvp (prepare-256  m) 32))
:hints (("goal" :in-theory (disable prepare-256-ac ))))


(defthm len-prepare-256
  (implies (wordp m 512)
           (equal (len (prepare-256 m)) 64))
:hints (("goal" :in-theory (disable prepare-256-ac))))


(defun temp-1-256 (j  working-variables  m-i-ext)
 (if (and (wvp  working-variables 32) (equal (len  working-variables) 8)
          (integerp j) (<= 0 j)
          (wvp  m-i-ext 32) (equal (len m-i-ext) 64))
    (plus 32 (nth 7  working-variables)
             (sigma-1-256 (nth 4  working-variables))
             (Ch (nth 4  working-variables)
             (nth 5  working-variables)
             (nth 6 working-variables ))
             (k-256 j)
             (nth j m-i-ext) )
     nil))

(defthm wordp-temp-1-256
 (implies (and (wvp l 32) (equal (len l) 8)
               (integerp j) (<= 0 j) (< j 64)
               (wvp  m 32) (equal (len m) 64))
          (wordp (temp-1-256 j l m ) 32))
:hints (("goal" :in-theory (disable sigma-1-256 ch k-256 nth binary-plus ))
))

(defun temp-2-256 ( working-variables )
 (if (and (wvp working-variables  32) (equal (len working-variables) 8))
     (plus 32 (sigma-0-256 (nth 0 working-variables))
              (Maj (nth 0 working-variables )
              (nth 1 working-variables)
              (nth 2 working-variables)) )
      nil))


(defthm wordp-temp-2-256
 (implies (and  (wvp l 32) (equal (len l) 8))
          (wordp (temp-2-256  l ) 32))
:hints
(("goal"
  :in-theory (disable sigma-0-256 maj binary-plus  nth ))))


(defun digest-one-block-256-ac ( j working-variables m-i-ext)
(declare (xargs :measure (acl2-count (- 64 j))))
    (if (and (wvp working-variables 32) (equal (len working-variables) 8)
             (integerp j) (<= 0 j)
             (wvp  m-i-ext 32) (equal (len m-i-ext) 64))
        (if (<= 64 j)
            working-variables
            (digest-one-block-256-ac (+ 1 j)
                      (list (plus 32 (temp-1-256 j working-variables m-i-ext)
                                     (temp-2-256  working-variables ))
                            (nth 0 working-variables)
                            (nth 1 working-variables)
                            (nth 2 working-variables)
                            (plus 32 (nth 3 working-variables)
                                 (temp-1-256 j  working-variables m-i-ext))
                            (nth 4 working-variables)
                            (nth 5 working-variables)
                            (nth 6 working-variables))
                        m-i-ext) )
      nil))


(defun digest-one-block-256 (hash-values m-i-ext)
   (if (and  (wvp hash-values 32) (equal (len hash-values) 8)
             (wvp m-i-ext 32) (equal (len m-i-ext) 64))
       (digest-one-block-256-ac 0 hash-values  m-i-ext)
       nil))


(defthm wvp-digest-one-block-256-ac
 (implies (and  (wvp l 32) (equal (len l) 8)
                (integerp j) (<= 0 j)
                (wvp m 32) (equal (len m) 64))
          (wvp (digest-one-block-256-ac j l m ) 32))
:hints (("goal" :in-theory (disable  temp-1-256 temp-2-256 nth binary-plus))
))

(defthm len-digest-one-block-256-ac
 (implies (and  (wvp l 32) (equal (len l) 8)
                (integerp j) (<= 0 j)
                (wvp m 32) (equal (len m) 64))
          (equal (len (digest-one-block-256-ac j l m )) 8))
:hints (("goal" :in-theory (disable temp-1-256 temp-2-256 nth binary-plus ))))



(defthm wvp-digest-one-block-256
 (implies (and  (wvp l 32) (equal (len l) 8)
                (wvp m 32) (equal (len m) 64))
          (wvp (digest-one-block-256 l m ) 32))
:hints
(("goal"
  :in-theory (disable digest-one-block-256-ac))))


(defthm len-digest-one-block-256
 (implies (and (wvp l 32) (equal (len l) 8)
               (wvp m 32) (equal (len m) 64))
          (equal (len (digest-one-block-256  l m )) 8))
:hints
(("goal"
  :in-theory (disable digest-one-block-256-ac ))))


(defun intermediate-hash-256 ( l1 l2)
 (if (and  (wvp l1 32) (equal (len l1) 8)
           (wvp l2 32) (equal (len l2) 8) )
     (list (plus 32 (nth 0 l1) (nth 0 l2))
           (plus 32 (nth 1 l1) (nth 1 l2) )
           (plus 32 (nth 2 l1) (nth 2 l2) )
           (plus 32 (nth 3 l1) (nth 3 l2) )
           (plus 32 (nth 4 l1) (nth 4 l2) )
           (plus 32 (nth 5 l1) (nth 5 l2) )
           (plus 32 (nth 6 l1) (nth 6 l2) )
           (plus 32 (nth 7 l1) (nth 7 l2) ) )
     nil))


(defthm wvp-intermediate-hash-256
 (implies (and  (wvp l1 32) (equal (len l1) 8)
                (wvp l2 32) (equal (len l2) 8) )
          (wvp (intermediate-hash-256 l1 l2 ) 32))
:hints
(("goal"
  :in-theory (disable binary-plus wordp nth ))))


(defthm len-intermediate-hash-256
 (implies (and  (wvp l1 32) (equal (len l1) 8)
                (wvp l2 32) (equal (len l2) 8) )
          (equal (len (intermediate-hash-256 l1 l2 )) 8)))


(defun digest-256 ( m hash-values)
  (if (and (wvp m 512) (wvp  hash-values 32) (equal (len hash-values) 8))
      (if (endp m)   hash-values
          (digest-256 (cdr m)
              (intermediate-hash-256   hash-values
                    (digest-one-block-256 hash-values
                                (prepare-256  (car m) )))))
       nil) )


(defthm wvp-digest-256
 (implies (and (wvp m 512) (wvp hash-values 32)
               (equal (len hash-values) 8))
          (wvp (digest-256 m hash-values ) 32) )
:hints
(("goal"
  :in-theory (disable intermediate-hash-256
              digest-one-block-256 prepare-256 ))))


(defthm len-digest-256
 (implies (and (wvp m 512) (wvp hash-values 32) (not (endp m))
               (equal (len hash-values) 8))
          (equal (len (digest-256 m hash-values )) 8) )
:hints
(("goal"
  :in-theory (disable intermediate-hash-256
              digest-one-block-256 prepare-256 ))))

(defun sha-256 ( m)
  (if (and (bvp m) (< (len m) (expt 2 64)))
      (digest-256 (parsing (padding-1-256 m) 512) (h-256))
      nil))


(defthm wvp-sha-256
(implies (and (bvp m) (< (len m) (expt 2 64)))
         (wvp (sha-256 m) 32) )
:hints
(("goal"
  :in-theory (disable digest-256 parsing padding-1-256))))


(defthm len-sha-256
(implies (and (bvp m) (< (len m) (expt 2 64)))
         (equal (len (sha-256 m)) 8 ))
:hints
(("goal"
  :use (:instance len-digest-256 (m (parsing (padding-1-256 m) 512))
                          (hash-values (h-256)))
  :in-theory (disable digest-256 parsing padding-1-256))))
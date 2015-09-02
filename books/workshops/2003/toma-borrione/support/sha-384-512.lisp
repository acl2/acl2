;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHA-384 and SHA-512
; Message digest functions and theorems
;------------------------------------------

(IN-PACKAGE "ACL2")

(include-book "parsing")
(include-book "sha-functions")

;I strongly recommend after charging the book to do :comp t in order to accelerate the computation

; For a message M with length less than (expt 2 128) sha-512 returns a message digest of 512 bits (eight words each of 64 bits), and sha-384 returns 384 bits of message digest (six words each of 64 bits) .

;For message "abc"
;ACL2 !>(sha-512 '(0 1 1 0 0 0 0 1 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1 ))
;((1 1 0 1
;    1 1 0 1 1 0 1 0 1 1 1 1 0 0 1 1 0 1 0 1
;    1 0 1 0 0 0 0 1 1 0 0 1 0 0 1 1 0 1 1 0
;    0 0 0 1 0 1 1 1 1 0 1 0 1 0 1 1 1 0 1 0)
; (1 1 0 0
;    1 1 0 0 0 1 0 0 0 0 0 1 0 1 1 1 0 0 1 1
;    0 1 0 0 1 0 0 1 1 0 1 0 1 1 1 0 0 0 1 0
;    0 0 0 0 0 1 0 0 0 0 0 1 0 0 1 1 0 0 0 1)
; (0 0 0 1
;    0 0 1 0 1 1 1 0 0 1 1 0 1 1 1 1 1 0 1 0
;    0 1 0 0 1 1 1 0 1 0 0 0 1 0 0 1 1 0 1 0
;    1 0 0 1 0 1 1 1 1 1 1 0 1 0 1 0 0 0 1 0)
; (0 0 0 0
;    1 0 1 0 1 0 0 1 1 1 1 0 1 1 1 0 1 1 1 0
;    1 1 1 0 0 1 1 0 0 1 0 0 1 0 1 1 0 1 0 1
;    0 1 0 1 1 1 0 1 0 0 1 1 1 0 0 1 1 0 1 0)
; (0 0 1 0
;    0 0 0 1 1 0 0 1 0 0 1 0 1 0 0 1 1 0 0 1
;    0 0 1 0 1 0 1 0 0 0 1 0 0 1 1 1 0 1 0 0
;    1 1 1 1 1 1 0 0 0 0 0 1 1 0 1 0 1 0 0 0)
; (0 0 1 1
;    0 1 1 0 1 0 1 1 1 0 1 0 0 0 1 1 1 1 0 0
;    0 0 1 0 0 0 1 1 1 0 1 0 0 0 1 1 1 1 1 1
;    1 1 1 0 1 1 1 0 1 0 1 1 1 0 1 1 1 1 0 1)
; (0 1 0 0
;    0 1 0 1 0 1 0 0 1 1 0 1 0 1 0 0 0 1 0 0
;    0 0 1 0 0 0 1 1 0 1 1 0 0 1 0 0 0 0 1 1
;    1 1 0 0 1 1 1 0 1 0 0 0 0 0 0 0 1 1 1 0)
; (0 0 1 0 1
;    0 1 0 1 0 0 1 1 0 1 0 1 1 0 0 1 0 0 1 0
;    1 0 0 1 1 1 1 1 0 1 0 0 1 0 1 0 1 0 0 1
;    1 0 0 1 0 1 0 0 1 0 0 1 0 0 1 1 1 1 1))



; constants of sha-512
(defun K-512 (i)
   (cond ((equal i 0)
        '(0 1 0 0 0 0 1 0 1 0 0 0
   1 0 1 0 0 0 1 0 1 1 1 1 1 0 0 1 1 0 0 0 1 1 0 1 0 1 1 1 0 0 1 0
   1 0 0 0 1 0 1 0 1 1 1 0 0 0 1 0 0 0 1 0))
         ((equal i 1)
        '(0 1 1 1 0 0 0 1 0 0 1 1
   0 1 1 1 0 1 0 0 0 1 0 0 1 0 0 1 0 0 0 1 0 0 1 0 0 0 1 1 1 1 1 0
   1 1 1 1 0 1 1 0 0 1 0 1 1 1 0 0 1 1 0 1))
         ((equal i 2) '(1 0 1 1 0 1 0 1 1 1 0 0
   0 0 0 0 1 1 1 1 1 0 1 1 1 1 0 0 1 1 1 1 1 1 1 0 1 1 0 0 0 1 0 0
   1 1 0 1 0 0 1 1 1 0 1 1 0 0 1 0 1 1 1 1))
         ((equal i 3) '(1 1 1 0 1 0 0 1 1 0 1 1
   0 1 0 1 1 1 0 1 1 0 1 1 1 0 1 0 0 1 0 1 1 0 0 0 0 0 0 1 1 0 0 0
   1 0 0 1 1 1 0 1 1 0 1 1 1 0 1 1 1 1 0 0))
         ((equal i 4) '(0 0 1 1 1 0 0 1 0 1 0 1
   0 1 1 0 1 1 0 0 0 0 1 0 0 1 0 1 1 0 1 1 1 1 1 1 0 0 1 1 0 1 0 0
   1 0 0 0 1 0 1 1 0 1 0 1 0 0 1 1 1 0 0 0))
         ((equal i 5) '(0 1 0 1 1 0 0 1 1 1 1 1
   0 0 0 1 0 0 0 1 0 0 0 1 1 1 1 1 0 0 0 1 1 0 1 1 0 1 1 0 0 0 0 0
   0 1 0 1 1 1 0 1 0 0 0 0 0 0 0 1 1 0 0 1))
         ((equal i 6) '(1 0 0 1 0 0 1 0 0 0 1 1
   1 1 1 1 1 0 0 0 0 0 1 0 1 0 1 0 0 1 0 0 1 0 1 0 1 1 1 1 0 0 0 1
   1 0 0 1 0 1 0 0 1 1 1 1 1 0 0 1 1 0 1 1))
         ((equal i 7) '(1 0 1 0
   1 0 1 1 0 0 0 1 1 1 0 0 0 1 0 1 1 1 1 0
   1 1 0 1 0 1 0 1 1 1 0 1 1 0 1 0 0 1 1 0
   1 1 0 1 1 0 0 0 0 0 0 1 0 0 0 1 1 0 0 0))
         ((equal i 8) '(1 1 0 1
   1 0 0 0 0 0 0 0 0 1 1 1 1 0 1 0 1 0 1 0
   1 0 0 1 1 0 0 0 1 0 1 0 0 0 1 1 0 0 0 0
   0 0 1 1 0 0 0 0 0 0 1 0 0 1 0 0 0 0 1 0))
         ((equal i 9) '(0 0 0 1
   0 0 1 0 1 0 0 0 0 0 1 1 0 1 0 1 1 0 1 1
   0 0 0 0 0 0 0 1 0 1 0 0 0 1 0 1 0 1 1 1
   0 0 0 0 0 1 1 0 1 1 1 1 1 0 1 1 1 1 1 0))
         ((equal i 10) '(0 0 1 0
   0 1 0 0 0 0 1 1 0 0 0 1 1 0 0 0 0 1 0 1
   1 0 1 1 1 1 1 0 0 1 0 0 1 1 1 0 1 1 1 0
   0 1 0 0 1 0 1 1 0 0 1 0 1 0 0 0 1 1 0 0))
         ((equal i 11) '(0 1 0 1
   0 1 0 1 0 0 0 0 1 1 0 0 0 1 1 1 1 1 0 1
   1 1 0 0 0 0 1 1 1 1 0 1 0 1 0 1 1 1 1 1
   1 1 1 1 1 0 1 1 0 1 0 0 1 1 1 0 0 0 1 0))
         ((equal i 12) '(0 1 1 1
   0 0 1 0 1 0 1 1 1 1 1 0 0 1 0 1 1 1 0 1
   0 1 1 1 0 1 0 0 1 1 1 1 0 0 1 0 0 1 1 1
   1 0 1 1 1 0 0 0 1 0 0 1 0 1 1 0 1 1 1 1))
         ((equal i 13) '(1 0 0 0
   0 0 0 0 1 1 0 1 1 1 1 0 1 0 1 1 0 0 0 1
   1 1 1 1 1 1 1 0 0 0 1 1 1 0 1 1 0 0 0 1
   0 1 1 0 1 0 0 1 0 1 1 0 1 0 1 1 0 0 0 1))
         ((equal i 14) '(1 0 0 1
   1 0 1 1 1 1 0 1 1 1 0 0 0 0 0 0 0 1 1 0
   1 0 1 0 0 1 1 1 0 0 1 0 0 1 0 1 1 1 0 0
   0 1 1 1 0 0 0 1 0 0 1 0 0 0 1 1 0 1 0 1))
         ((equal i 15) '(1 1 0 0
   0 0 0 1 1 0 0 1 1 0 1 1 1 1 1 1 0 0 0 1
   0 1 1 1 0 1 0 0 1 1 0 0 1 1 1 1 0 1 1 0
   1 0 0 1 0 0 1 0 0 1 1 0 1 0 0 1 0 1 0 0))
         ((equal i 16) '(1 1 1 0
   0 1 0 0 1 0 0 1 1 0 1 1 0 1 1 0 1 0 0 1
   1 1 0 0 0 0 0 1 1 0 0 1 1 1 1 0 1 1 1 1
   0 0 0 1 0 1 0 0 1 0 1 0 1 1 0 1 0 0 1 0))
         ((equal i 17) '(1 1 1 0
   1 1 1 1 1 0 1 1 1 1 1 0 0 1 0 0 0 1 1 1
   1 0 0 0 0 1 1 0 0 0 1 1 1 0 0 0 0 1 0 0
   1 1 1 1 0 0 1 0 0 1 0 1 1 1 1 0 0 0 1 1))
         ((equal i 18) '(0 0 0 0
   1 1 1 1 1 1 0 0 0 0 0 1 1 0 0 1 1 1 0 1
   1 1 0 0 0 1 1 0 1 0 0 0 1 0 1 1 1 0 0 0
   1 1 0 0 1 1 0 1 0 1 0 1 1 0 1 1 0 1 0 1))
         ((equal i 19) '(0 0 1 0
   0 1 0 0 0 0 0 0 1 1 0 0 1 0 1 0 0 0 0 1
   1 1 0 0 1 1 0 0 0 1 1 1 0 1 1 1 1 0 1 0
   1 1 0 0 1 0 0 1 1 1 0 0 0 1 1 0 0 1 0 1))
         ((equal i 20) '(0 0 1 0
   1 1 0 1 1 1 1 0 1 0 0 1 0 0 1 0 1 1 0 0
   0 1 1 0 1 1 1 1 0 1 0 1 1 0 0 1 0 0 1 0
   1 0 1 1 0 0 0 0 0 0 1 0 0 1 1 1 0 1 0 1))
         ((equal i 21) '(0 1 0 0
   1 0 1 0 0 1 1 1 0 1 0 0 1 0 0 0 0 1 0 0
   1 0 1 0 1 0 1 0 0 1 1 0 1 1 1 0 1 0 1 0
   0 1 1 0 1 1 1 0 0 1 0 0 1 0 0 0 0 0 1 1))
         ((equal i 22) '(0 1 0 1
   1 1 0 0 1 0 1 1 0 0 0 0 1 0 1 0 1 0 0 1
   1 1 0 1 1 1 0 0 1 0 1 1 1 1 0 1 0 1 0 0
   0 0 0 1 1 1 1 1 1 0 1 1 1 1 0 1 0 1 0 0))
         ((equal i 23) '(0 1 1 1
   0 1 1 0 1 1 1 1 1 0 0 1 1 0 0 0 1 0 0 0
   1 1 0 1 1 0 1 0 1 0 0 0 0 0 1 1 0 0 0 1
   0 0 0 1 0 1 0 1 0 0 1 1 1 0 1 1 0 1 0 1))
         ((equal i 24) '(1 0 0 1
   1 0 0 0 0 0 1 1 1 1 1 0 0 1 0 1 0 0 0 1
   0 1 0 1 0 0 1 0 1 1 1 0 1 1 1 0 0 1 1 0
   0 1 1 0 1 1 0 1 1 1 1 1 1 0 1 0 1 0 1 1))
         ((equal i 25) '(1 0 1 0
   1 0 0 0 0 0 1 1 0 0 0 1 1 1 0 0 0 1 1 0
   0 1 1 0 1 1 0 1 0 0 1 0 1 1 0 1 1 0 1 1
   0 1 0 0 0 0 1 1 0 0 1 0 0 0 0 1 0 0 0 0))
         ((equal i 26) '(1 0 1 1
   0 0 0 0 0 0 0 0 0 0 1 1 0 0 1 0 0 1 1 1
   1 1 0 0 1 0 0 0 1 0 0 1 1 0 0 0 1 1 1 1
   1 0 1 1 0 0 1 0 0 0 0 1 0 0 1 1 1 1 1 1))
         ((equal i 27) '(1 0 1 1
   1 1 1 1 0 1 0 1 1 0 0 1 0 1 1 1 1 1 1 1
   1 1 0 0 0 1 1 1 1 0 1 1 1 1 1 0 1 1 1 0
   1 1 1 1 0 0 0 0 1 1 1 0 1 1 1 0 0 1 0 0))
         ((equal i 28) '(1 1 0 0
   0 1 1 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 1 1
   1 1 1 1 0 0 1 1 0 0 1 1 1 1 0 1 1 0 1 0
   1 0 0 0 1 0 0 0 1 1 1 1 1 1 0 0 0 0 1 0))
         ((equal i 29) '(1 1 0 1
   0 1 0 1 1 0 1 0 0 1 1 1 1 0 0 1 0 0 0 1
   0 1 0 0 0 1 1 1 1 0 0 1 0 0 1 1 0 0 0 0
   1 0 1 0 1 0 1 0 0 1 1 1 0 0 1 0 0 1 0 1))
         ((equal i 30) '(0 0 0 0
   0 1 1 0 1 1 0 0 1 0 1 0 0 1 1 0 0 0 1 1
   0 1 0 1 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0
   0 0 1 1 1 0 0 0 0 0 1 0 0 1 1 0 1 1 1 1))
         ((equal i 31) '(0 0 0 1
   0 1 0 0 0 0 1 0 1 0 0 1 0 0 1 0 1 0 0 1
   0 1 1 0 0 1 1 1 0 0 0 0 1 0 1 0 0 0 0 0
   1 1 1 0 0 1 1 0 1 1 1 0 0 1 1 1 0 0 0 0))
         ((equal i 32) '(0 0 1 0
   0 1 1 1 1 0 1 1 0 1 1 1 0 0 0 0 1 0 1 0
   1 0 0 0 0 1 0 1 0 1 0 0 0 1 1 0 1 1 0 1
   0 0 1 0 0 0 1 0 1 1 1 1 1 1 1 1 1 1 0 0))
         ((equal i 33) '(0 0 1 0
   1 1 1 0 0 0 0 1 1 0 1 1 0 0 1 0 0 0 0 1
   0 0 1 1 1 0 0 0 0 1 0 1 1 1 0 0 0 0 1 0
   0 1 1 0 1 1 0 0 1 0 0 1 0 0 1 0 0 1 1 0))
         ((equal i 34) '(0 1 0 0
   1 1 0 1 0 0 1 0 1 1 0 0 0 1 1 0 1 1 0 1
   1 1 1 1 1 1 0 0 0 1 0 1 1 0 1 0 1 1 0 0
   0 1 0 0 0 0 1 0 1 0 1 0 1 1 1 0 1 1 0 1))
         ((equal i 35) '(0 1 0 1
   0 0 1 1 0 0 1 1 1 0 0 0 0 0 0 0 1 1 0 1
   0 0 0 1 0 0 1 1 1 0 0 1 1 1 0 1 1 0 0 1
   0 1 0 1 1 0 1 1 0 0 1 1 1 1 0 1 1 1 1 1))
         ((equal i 36) '(0 1 1 0
   0 1 0 1 0 0 0 0 1 0 1 0 0 1 1 1 0 0 1 1
   0 1 0 1 0 1 0 0 1 0 0 0 1 0 1 1 1 0 1 0
   1 1 1 1 0 1 1 0 0 0 1 1 1 1 0 1 1 1 1 0))
         ((equal i 37) '(0 1 1 1
   0 1 1 0 0 1 1 0 1 0 1 0 0 0 0 0 1 0 1 0
   1 0 1 1 1 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1
   0 1 1 1 1 0 1 1 0 0 1 0 1 0 1 0 1 0 0 0))
         ((equal i 38) '(1 0 0 0
   0 0 0 1 1 1 0 0 0 0 1 0 1 1 0 0 1 0 0 1
   0 0 1 0 1 1 1 0 0 1 0 0 0 1 1 1 1 1 1 0
   1 1 0 1 1 0 1 0 1 1 1 0 1 1 1 0 0 1 1 0))
         ((equal i 39) '(1 0 0 1
   0 0 1 0 0 1 1 1 0 0 1 0 0 0 1 0 1 1 0 0
   1 0 0 0 0 1 0 1 0 0 0 1 0 1 0 0 1 0 0 0
   0 0 1 0 0 0 1 1 0 1 0 1 0 0 1 1 1 0 1 1))
         ((equal i 40) '(1 0 1 0
   0 0 1 0 1 0 1 1 1 1 1 1 1 1 1 0 1 0 0 0
   1 0 1 0 0 0 0 1 0 1 0 0 1 1 0 0 1 1 1 1
   0 0 0 1 0 0 0 0 0 0 1 1 0 1 1 0 0 1 0 0))
         ((equal i 41) '(1 0 1 0
   1 0 0 0 0 0 0 1 1 0 1 0 0 1 1 0 0 1 1 0
   0 1 0 0 1 0 1 1 1 0 1 1 1 1 0 0 0 1 0 0
   0 0 1 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 1))
         ((equal i 42) '(1 1 0 0
   0 0 1 0 0 1 0 0 1 0 1 1 1 0 0 0 1 0 1 1
   0 1 1 1 0 0 0 0 1 1 0 1 0 0 0 0 1 1 1 1
   1 0 0 0 1 0 0 1 0 1 1 1 1 0 0 1 0 0 0 1))
         ((equal i 43) '(1 1 0 0
   0 1 1 1 0 1 1 0 1 1 0 0 0 1 0 1 0 0 0 1
   1 0 1 0 0 0 1 1 0 0 0 0 0 1 1 0 0 1 0 1
   0 1 0 0 1 0 1 1 1 1 1 0 0 0 1 1 0 0 0 0))
         ((equal i 44) '(1 1 0 1
   0 0 0 1 1 0 0 1 0 0 1 0 1 1 1 0 1 0 0 0
   0 0 0 1 1 0 0 1 1 1 0 1 0 1 1 0 1 1 1 0
   1 1 1 1 0 1 0 1 0 0 1 0 0 0 0 1 1 0 0 0))
         ((equal i 45) '(1 1 0 1
   0 1 1 0 1 0 0 1 1 0 0 1 0 0 0 0 0 1 1 0
   0 0 1 0 0 1 0 0 0 1 0 1 0 1 0 1 0 1 1 0
   0 1 0 1 1 0 1 0 1 0 0 1 0 0 0 1 0 0 0 0))
         ((equal i 46) '(1 1 1 1
   0 1 0 0 0 0 0 0 1 1 1 0 0 0 1 1 0 1 0 1
   1 0 0 0 0 1 0 1 0 1 0 1 0 1 1 1 0 1 1 1
   0 0 0 1 0 0 1 0 0 0 0 0 0 0 1 0 1 0 1 0))
         ((equal i 47) '(0 0 0 1
   0 0 0 0 0 1 1 0 1 0 1 0 1 0 1 0 0 0 0 0
   0 1 1 1 0 0 0 0 0 0 1 1 0 0 1 0 1 0 1 1
   1 0 1 1 1 1 0 1 0 0 0 1 1 0 1 1 1 0 0 0))
         ((equal i 48) '(0 0 0 1
   1 0 0 1 1 0 1 0 0 1 0 0 1 1 0 0 0 0 0 1
   0 0 0 1 0 1 1 0 1 0 1 1 1 0 0 0 1 1 0 1
   0 0 1 0 1 1 0 1 0 0 0 0 1 1 0 0 1 0 0 0))
         ((equal i 49) '(0 0 0 1
   1 1 1 0 0 0 1 1 0 1 1 1 0 1 1 0 1 1 0 0
   0 0 0 0 1 0 0 0 0 1 0 1 0 0 0 1 0 1 0 0
   0 0 0 1 1 0 1 0 1 0 1 1 0 1 0 1 0 0 1 1))
         ((equal i 50) '(0 0 1 0
   0 1 1 1 0 1 0 0 1 0 0 0 0 1 1 1 0 1 1 1
   0 1 0 0 1 1 0 0 1 1 0 1 1 1 1 1 1 0 0 0
   1 1 1 0 1 1 1 0 1 0 1 1 1 0 0 1 1 0 0 1))
         ((equal i 51) '(0 0 1 1
   0 1 0 0 1 0 1 1 0 0 0 0 1 0 1 1 1 1 0 0
   1 0 1 1 0 1 0 1 1 1 1 0 0 0 0 1 1 0 0 1
   1 0 1 1 0 1 0 0 1 0 0 0 1 0 1 0 1 0 0 0))
         ((equal i 52) '(0 0 1 1
   1 0 0 1 0 0 0 1 1 1 0 0 0 0 0 0 1 1 0 0
   1 0 1 1 0 0 1 1 1 1 0 0 0 1 0 1 1 1 0 0
   1 0 0 1 0 1 0 1 1 0 1 0 0 1 1 0 0 0 1 1))
         ((equal i 53) '(0 1 0 0
   1 1 1 0 1 1 0 1 1 0 0 0 1 0 1 0 1 0 1 0
   0 1 0 0 1 0 1 0 1 1 1 0 0 0 1 1 0 1 0 0
   0 0 0 1 1 0 0 0 1 0 1 0 1 1 0 0 1 0 1 1))
         ((equal i 54) '(0 1 0 1
   1 0 1 1 1 0 0 1 1 1 0 0 1 1 0 0 1 0 1 0
   0 1 0 0 1 1 1 1 0 1 1 1 0 1 1 1 0 1 1 0
   0 0 1 1 1 1 1 0 0 0 1 1 0 1 1 1 0 0 1 1))
         ((equal i 55) '(0 1 1 0
   1 0 0 0 0 0 1 0 1 1 1 0 0 1 1 0 1 1 1 1
   1 1 1 1 0 0 1 1 1 1 0 1 0 1 1 0 1 0 1 1
   0 0 1 0 1 0 1 1 1 0 0 0 1 0 1 0 0 0 1 1))
         ((equal i 56) '(0 1 1 1
   0 1 0 0 1 0 0 0 1 1 1 1 1 0 0 0 0 0 1 0
   1 1 1 0 1 1 1 0 0 1 0 1 1 1 0 1 1 1 1 0
   1 1 1 1 1 0 1 1 0 0 1 0 1 1 1 1 1 1 0 0))
         ((equal i 57) '(0 1 1 1
   1 0 0 0 1 0 1 0 0 1 0 1 0 1 1 0 0 0 1 1
   0 1 1 0 1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 1
   0 1 1 1 0 0 1 0 1 1 1 1 0 1 1 0 0 0 0 0))
         ((equal i 58) '(1 0 0 0
   0 1 0 0 1 1 0 0 1 0 0 0 0 1 1 1 1 0 0 0
   0 0 0 1 0 1 0 0 1 0 1 0 0 0 0 1 1 1 1 1
   0 0 0 0 1 0 1 0 1 0 1 1 0 1 1 1 0 0 1 0))
         ((equal i 59) '(1 0 0 0
   1 1 0 0 1 1 0 0 0 1 1 1 0 0 0 0 0 0 1 0
   0 0 0 0 1 0 0 0 0 0 0 1 1 0 1 0 0 1 1 0
   0 1 0 0 0 0 1 1 1 0 0 1 1 1 1 0 1 1 0 0))
         ((equal i 60) '(1 0 0 1
   0 0 0 0 1 0 1 1 1 1 1 0 1 1 1 1 1 1 1 1
   1 1 1 1 1 0 1 0 0 0 1 0 0 0 1 1 0 1 1 0
   0 0 1 1 0 0 0 1 1 1 1 0 0 0 1 0 1 0 0 0))
         ((equal i 61) '(1 0 1 0
   0 1 0 0 0 1 0 1 0 0 0 0 0 1 1 0 1 1 0 0
   1 1 1 0 1 0 1 1 1 1 0 1 1 1 1 0 1 0 0 0
   0 0 1 0 1 0 1 1 1 1 0 1 1 1 1 0 1 0 0 1))
         ((equal i 62) '(1 0 1 1
   1 1 1 0 1 1 1 1 1 0 0 1 1 0 1 0 0 0 1 1
   1 1 1 1 0 1 1 1 1 0 1 1 0 0 1 0 1 1 0 0
   0 1 1 0 0 1 1 1 1 0 0 1 0 0 0 1 0 1 0 1))
         ((equal i 63) '(1 1 0 0
   0 1 1 0 0 1 1 1 0 0 0 1 0 1 1 1 1 0 0 0
   1 1 1 1 0 0 1 0 1 1 1 0 0 0 1 1 0 1 1 1
   0 0 1 0 0 1 0 1 0 0 1 1 0 0 1 0 1 0 1 1))
         ((equal i 64) '(1 1 0 0
   1 0 1 0 0 0 1 0 0 1 1 1 0 0 1 1 1 1 1 0
   1 1 0 0 1 1 1 0 1 1 1 0 1 0 1 0 0 0 1 0
   0 1 1 0 0 1 1 0 0 0 0 1 1 0 0 1 1 1 0 0))
         ((equal i 65) '(1 1 0 1
   0 0 0 1 1 0 0 0 0 1 1 0 1 0 1 1 1 0 0 0
   1 1 0 0 0 1 1 1 0 0 1 0 0 0 0 1 1 1 0 0
   0 0 0 0 1 1 0 0 0 0 1 0 0 0 0 0 0 1 1 1))
         ((equal i 66) '(1 1 1 0
   1 0 1 0 1 1 0 1 1 0 1 0 0 1 1 1 1 1 0 1
   1 1 0 1 0 1 1 0 1 1 0 0 1 1 0 1 1 1 1 0
   0 0 0 0 1 1 1 0 1 0 1 1 0 0 0 1 1 1 1 0))
         ((equal i 67) '(1 1 1 1
   0 1 0 1 0 1 1 1 1 1 0 1 0 1 0 0 1 1 1 1
   0 1 1 1 1 1 1 1 1 1 1 0 1 1 1 0 0 1 1 0
   1 1 1 0 1 1 0 1 0 0 0 1 0 1 1 1 1 0 0 0))
         ((equal i 68) '(0 0 0 0
   0 1 1 0 1 1 1 1 0 0 0 0 0 1 1 0 0 1 1 1
   1 0 1 0 1 0 1 0 0 1 1 1 0 0 1 0 0 0 0 1
   0 1 1 1 0 1 1 0 1 1 1 1 1 0 1 1 1 0 1 0))
         ((equal i 69) '(0 0 0 0
   1 0 1 0 0 1 1 0 0 0 1 1 0 1 1 1 1 1 0 1
   1 1 0 0 0 1 0 1 1 0 1 0 0 0 1 0 1 1 0 0
   1 0 0 0 1 0 0 1 1 0 0 0 1 0 1 0 0 1 1 0))
         ((equal i 70) '(0 0 0 1
   0 0 0 1 0 0 1 1 1 1 1 1 1 0 0 1 1 0 0 0
   0 0 0 0 0 1 0 0 1 0 1 1 1 1 1 0 1 1 1 1
   1 0 0 1 0 0 0 0 1 1 0 1 1 0 1 0 1 1 1 0))
         ((equal i 71) '(0 0 0 1
   1 0 1 1 0 1 1 1 0 0 0 1 0 0 0 0 1 0 1 1
   0 0 1 1 0 1 0 1 0 0 0 1 0 0 1 1 0 0 0 1
   1 1 0 0 0 1 0 0 0 1 1 1 0 0 0 1 1 0 1 1))
         ((equal i 72) '(0 0 1 0
   1 0 0 0 1 1 0 1 1 0 1 1 0 1 1 1 0 1 1 1
   1 1 1 1 0 1 0 1 0 0 1 0 0 0 1 1 0 0 0 0
   0 1 0 0 0 1 1 1 1 1 0 1 1 0 0 0 0 1 0 0))
         ((equal i 73) '(0 0 1 1
   0 0 1 0 1 1 0 0 1 0 1 0 1 0 1 0 1 0 1 1
   0 1 1 1 1 0 1 1 0 1 0 0 0 0 0 0 1 1 0 0
   0 1 1 1 0 0 1 0 0 1 0 0 1 0 0 1 0 0 1 1))
         ((equal i 74) '(0 0 1 1
   1 1 0 0 1 0 0 1 1 1 1 0 1 0 1 1 1 1 1 0
   0 0 0 0 1 0 1 0 0 0 0 1 0 1 0 1 1 1 0 0
   1 0 0 1 1 0 1 1 1 1 1 0 1 0 1 1 1 1 0 0))
         ((equal i 75) '(0 1 0 0
   0 0 1 1 0 0 0 1 1 1 0 1 0 1 1 0 0 1 1 1
   1 1 0 0 0 1 0 0 1 0 0 1 1 1 0 0 0 0 0 1
   0 0 0 0 0 0 0 0 1 1 0 1 0 1 0 0 1 1 0 0))
         ((equal i 76) '(0 1 0 0
   1 1 0 0 1 1 0 0 0 1 0 1 1 1 0 1 0 1 0 0
   1 0 1 1 1 1 1 0 1 1 0 0 1 0 1 1 0 0 1 1
   1 1 1 0 0 1 0 0 0 0 1 0 1 0 1 1 0 1 1 0))
         ((equal i 77) '(0 1 0 1
   1 0 0 1 0 1 1 1 1 1 1 1 0 0 1 0 1 0 0 1
   1 0 0 1 1 1 0 0 1 1 1 1 1 1 0 0 0 1 1 0
   0 1 0 1 0 1 1 1 1 1 1 0 0 0 1 0 1 0 1 0))
         ((equal i 78) '(0 1 0 1
   1 1 1 1 1 1 0 0 1 0 1 1 0 1 1 0 1 1 1 1
   1 0 1 0 1 0 1 1 0 0 1 1 1 0 1 0 1 1 0 1
   0 1 1 0 1 1 1 1 1 0 1 0 1 1 1 0 1 1 0 0))
         ((equal i 79) '(0 1 1 0
   1 1 0 0 0 1 0 0 0 1 0 0 0 0 0 1 1 0 0 1
   1 0 0 0 1 1 0 0 0 1 0 0 1 0 1 0 0 1 0 0
   0 1 1 1 0 1 0 1 1 0 0 0 0 0 0 1 0 1 1 1))
         (t   nil)))


(defthm wordp-K-512
(implies (and (integerp i) (<= 0 i) (<= i 79))
  (wordp (k-512 i) 64)))


; initial hash values for sha-384
(defun h-384()
'((1 1 0 0
   1 0 1 1 1 0 1 1 1 0 1 1 1 0 0 1 1 1 0 1
   0 1 0 1 1 1 0 1 1 1 0 0 0 0 0 1 0 0 0 0
   0 1 0 1 1 0 0 1 1 1 1 0 1 1 0 1 1 0 0 0)
(0 1 1 0
   0 0 1 0 1 0 0 1 1 0 1 0 0 0 1 0 1 0 0 1
   0 0 1 0 1 0 1 0 0 0 1 1 0 1 1 0 0 1 1 1
   1 1 0 0 1 1 0 1 0 1 0 1 0 0 0 0 0 1 1 1)
(1 0 0 1
   0 0 0 1 0 1 0 1 1 0 0 1 0 0 0 0 0 0 0 1
   0 1 0 1 1 0 1 0 0 0 1 1 0 0 0 0 0 1 1 1
   0 0 0 0 1 1 0 1 1 1 0 1 0 0 0 1 0 1 1 1)
(0 0 0 1
   0 1 0 1 0 0 1 0 1 1 1 1 1 1 1 0 1 1 0 0
   1 1 0 1 1 0 0 0 1 1 1 1 0 1 1 1 0 0 0 0
   1 1 1 0 0 1 0 1 1 0 0 1 0 0 1 1 1 0 0 1)
(0 1 1 0
   0 1 1 1 0 0 1 1 0 0 1 1 0 0 1 0 0 1 1 0
   0 1 1 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 0 0
   0 0 0 0 0 0 0 0 1 0 1 1 0 0 1 1 0 0 0 1)
(1 0 0 0
   1 1 1 0 1 0 1 1 0 1 0 0 0 1 0 0 1 0 1 0
   1 0 0 0 0 1 1 1 0 1 1 0 1 0 0 0 0 1 0 1
   1 0 0 0 0 0 0 1 0 1 0 1 0 0 0 1 0 0 0 1)
(1 1 0 1
   1 0 1 1 0 0 0 0 1 1 0 0 0 0 1 0 1 1 1 0
   0 0 0 0 1 1 0 1 0 1 1 0 0 1 0 0 1 1 1 1
   1 0 0 1 1 0 0 0 1 1 1 1 1 0 1 0 0 1 1 1)
(0 1 0 0
   0 1 1 1 1 0 1 1 0 1 0 1 0 1 0 0 1 0 0 0
   0 0 0 1 1 1 0 1 1 0 1 1 1 1 1 0 1 1 1 1
   1 0 1 0 0 1 0 0 1 1 1 1 1 0 1 0 0 1 0 0))
)

(defthm wordp-h-384
 (and  (wvp (h-384) 64) (equal (len (h-384)) 8 )))


; initial hash values for sha-512
(defun h-512()
'((0 1 1 0
   1 0 1 0 0 0 0 0 1 0 0 1 1 1 1 0 0 1 1 0
   0 1 1 0 0 1 1 1 1 1 1 1 0 0 1 1 1 0 1 1
   1 1 0 0 1 1 0 0 1 0 0 1 0 0 0 0 1 0 0 0)
(1 0 1 1
   1 0 1 1 0 1 1 0 0 1 1 1 1 0 1 0 1 1 1 0
   1 0 0 0 0 1 0 1 1 0 0 0 0 1 0 0 1 1 0 0
   1 0 1 0 1 0 1 0 0 1 1 1 0 0 1 1 1 0 1 1)
(0 0 1 1
   1 1 0 0 0 1 1 0 1 1 1 0 1 1 1 1 0 0 1 1
   0 1 1 1 0 0 1 0 1 1 1 1 1 1 1 0 1 0 0 1
   0 1 0 0 1 1 1 1 1 0 0 0 0 0 1 0 1 0 1 1)
(1 0 1 0
   0 1 0 1 0 1 0 0 1 1 1 1 1 1 1 1 0 1 0 1
   0 0 1 1 1 0 1 0 0 1 0 1 1 1 1 1 0 0 0 1
   1 1 0 1 0 0 1 1 0 1 1 0 1 1 1 1 0 0 0 1)
(0 1 0 1
   0 0 0 1 0 0 0 0 1 1 1 0 0 1 0 1 0 0 1 0
   0 1 1 1 1 1 1 1 1 0 1 0 1 1 0 1 1 1 1 0
   0 1 1 0 1 0 0 0 0 0 1 0 1 1 0 1 0 0 0 1)
(1 0 0 1
   1 0 1 1 0 0 0 0 0 1 0 1 0 1 1 0 1 0 0 0
   1 0 0 0 1 1 0 0 0 0 1 0 1 0 1 1 0 0 1 1
   1 1 1 0 0 1 1 0 1 1 0 0 0 0 0 1 1 1 1 1)
(0 0 0 1
   1 1 1 1 1 0 0 0 0 0 1 1 1 1 0 1 1 0 0 1
   1 0 1 0 1 0 1 1 1 1 1 1 1 0 1 1 0 1 0 0
   0 0 0 1 1 0 1 1 1 1 0 1 0 1 1 0 1 0 1 1)
(0 1 0 1
   1 0 1 1 1 1 1 0 0 0 0 0 1 1 0 0 1 1 0 1
   0 0 0 1 1 0 0 1 0 0 0 1 0 0 1 1 0 1 1 1
   1 1 1 0 0 0 1 0 0 0 0 1 0 1 1 1 1 0 0 1))
)

(defthm wordp-h-512
 (and  (wvp (h-512) 64) (equal (len (h-512)) 8 )))


;----sha-512

(defun prepare-512-ac ( j m-i)
(declare (xargs :measure (acl2-count (- 80 j))))
  (if (and  (integerp j) (<= 16 j) (wvp m-i 64))
      (cond ((<= 80 j) m-i)
            ((<= j 79)
             (prepare-512-ac (1+ j)
                      (append m-i (list (plus 64 (s-1-512 (nth (- j 2) m-i))
                                       (nth (- j 7) m-i)
                                       (s-0-512 (nth (- j 15) m-i))
                                       (nth (- j 16) m-i)))))))
      nil))


(defun prepare-512 (m-i)
  (if (wordp m-i 1024)
      (prepare-512-ac 16 (parsing m-i 64))
      nil))


(defthm wvp-prepare-512-ac
  (implies (and  (integerp j) (<= 16 j) (wvp  m 64))
       (wvp (prepare-512-ac j m) 64))
:hints (("goal" :in-theory (disable s-1-512 s-0-512 nth binary-plus ))))


(defthm len-prepare-512-ac
  (implies (and  (wvp  m 64) (integerp j) (<= 16 j) (<= j (len m) ))
       (equal (len (prepare-512-ac  j m))
              (if  (<= j 80)
                   (+ (- 80 j) (len m))
                   (len m))))
:hints (("goal" :in-theory (disable s-1-512 s-0-512 nth binary-plus ))))


(defthm wvp-prepare-512
  (implies (wordp  m 1024)
           (wvp (prepare-512  m) 64))
:hints (("goal" :in-theory (disable prepare-512-ac ))))


(defthm len-prepare-512
  (implies (wordp m 1024)
           (equal (len (prepare-512 m)) 80))
:hints (("goal" :in-theory (disable prepare-512-ac))))


(defun temp-1-512 (j working-variables m-i-ext)
 (if (and  (equal (len working-variables) 8) (wvp working-variables 64)
           (integerp j) (<= 0 j)
           (wvp m-i-ext 64)  (equal (len m-i-ext) 80))
    (plus 64 (nth 7 working-variables)
             (sigma-1-512 (nth 4 working-variables))
             (Ch (nth 4 working-variables)
             (nth 5 working-variables)
             (nth 6 working-variables))
             (k-512 j)
             (nth j m-i-ext) )
    nil))


(defthm wordp-temp-1-512
 (implies (and  (wvp l 64) (equal (len l) 8)
                (integerp j) (<= 0 j) (< j 80)
                (wvp  m 64) (equal (len m) 80))
          (wordp (temp-1-512 j l m ) 64))
:hints
(("goal"
  :in-theory (disable sigma-1-512 ch k-512 nth binary-plus wordp ))))


(defun temp-2-512 ( working-variables )
 (if (and (equal (len working-variables) 8) (wvp working-variables 64))
     (plus 64 (sigma-0-512 (nth 0 working-variables))
              (Maj (nth 0 working-variables)
              (nth 1 working-variables)
              (nth 2 working-variables)) )
     nil))


(defthm wordp-temp-2-512
 (implies (and  (wvp l 64) (equal (len l) 8))
          (wordp (temp-2-512  l ) 64))
:hints (("goal" :in-theory (disable sigma-0-512 maj binary-plus  nth ))))


(defun digest-one-block-512-ac ( j working-variables m-i-ext)
(declare (xargs :measure (acl2-count (- 80 j))))
    (if (and (equal (len working-variables) 8)  (wvp working-variables 64)
             (integerp j) (<= 0 j)
             (wvp m-i-ext 64) (equal (len m-i-ext) 80))
        (if (<= 80 j)
             working-variables
            (digest-one-block-512-ac (+ 1 j)
                      (list (plus 64 (temp-1-512 j working-variables  m-i-ext)
                                     (temp-2-512  working-variables ))
                            (nth 0 working-variables)
                            (nth 1 working-variables)
                            (nth 2 working-variables)
                            (plus 64 (nth 3 working-variables)
                                     (temp-1-512 j working-variables m-i-ext) )
                            (nth 4 working-variables)
                            (nth 5 working-variables)
                            (nth 6 working-variables))
                         m-i-ext) )
      nil))


(defun digest-one-block-512 (hash-values m-i-ext)
   (if (and  (wvp hash-values 64) (equal (len hash-values) 8)
             (wvp m-i-ext 64) (equal (len m-i-ext) 80))
       (digest-one-block-512-ac 0 hash-values  m-i-ext)
       nil))


(defthm wvp-digest-one-block-512-ac
 (implies (and (wvp l 64) (equal (len l) 8)
               (integerp j) (<= 0 j)
               (wvp m 64) (equal (len m) 80))
          (wvp (digest-one-block-512-ac j l m ) 64))
:hints (("goal" :in-theory (disable  temp-1-512 temp-2-512 nth binary-plus))))


(defthm len-digest-one-block-512-ac
 (implies (and  (wvp l 64) (equal (len l) 8)
                (integerp j) (<= 0 j)
                (wvp m 64) (equal (len m) 80))
          (equal (len (digest-one-block-512-ac j l m )) 8))
:hints (("goal" :in-theory (disable temp-1-512 temp-2-512 nth binary-plus ))))


(defthm wvp-digest-one-block-512
 (implies (and  (wvp l 64) (equal (len l) 8)
                (wvp m 64) (equal (len m) 80))
          (wvp (digest-one-block-512 l m ) 64))
:hints
(("goal"
  :in-theory (disable digest-one-block-512-ac))))


(defthm len-digest-one-block-512
 (implies (and (wvp l 64) (equal (len l) 8)
               (wvp m 64) (equal (len m) 80))
          (equal (len (digest-one-block-512  l m )) 8))
:hints
(("goal"
  :in-theory (disable digest-one-block-512-ac ))))


(defun intermediate-hash-512 ( l1 l2)
 (if (and  (wvp l1 64) (equal (len l1) 8)
           (wvp l2 64) (equal (len l2) 8) )
     (list (plus 64 (nth 0 l1) (nth 0 l2) )
           (plus 64 (nth 1 l1) (nth 1 l2) )
           (plus 64 (nth 2 l1) (nth 2 l2) )
           (plus 64 (nth 3 l1) (nth 3 l2) )
           (plus 64 (nth 4 l1) (nth 4 l2) )
           (plus 64 (nth 5 l1) (nth 5 l2) )
           (plus 64 (nth 6 l1) (nth 6 l2) )
           (plus 64 (nth 7 l1) (nth 7 l2) ))
    nil))


(defthm wvp-intermediate-hash-512
 (implies (and  (wvp l1 64) (equal (len l1) 8)
           (wvp l2 64) (equal (len l2) 8) )
  (wvp (intermediate-hash-512 l1 l2 ) 64))
:hints (("goal"  :in-theory (disable binary-plus wordp nth ))))


(defthm len-intermediate-hash-512
 (implies (and  (wvp l1 64) (equal (len l1) 8)
           (wvp l2 64) (equal (len l2) 8) )
  (equal (len (intermediate-hash-512 l1 l2 )) 8)))


(defun digest-512 ( m hash-values)
  (if (and (wvp m 1024) (wvp hash-values 64) (equal (len hash-values) 8)  )
      (if (endp m)  hash-values
          (digest-512 (cdr m)
              (intermediate-hash-512 hash-values
                       (digest-one-block-512 hash-values
                              (prepare-512  (car m) )))))
       nil) )


(defthm wvp-digest-512
 (implies (and (wvp m 1024) (wvp hash-values 64)
            (equal (len hash-values) 8))
      (wvp (digest-512 m hash-values ) 64) )
:hints
(("goal"
  :in-theory (disable intermediate-hash-512
             digest-one-block-512 prepare-512 ))))


(defthm len-digest-512
 (implies (and (wvp m 1024) (wvp hash-values 64) (not (endp m))
            (equal (len hash-values) 8))
      (equal (len (digest-512 m hash-values )) 8) )
:hints
(("goal"
  :in-theory (disable intermediate-hash-512
             digest-one-block-512 prepare-512 ))))


(defun sha-512 ( m)
  (if (and (bvp m)  (< (len m) (expt 2 128)))
      (digest-512 (parsing (padding-512 m) 1024) (h-512))
      nil))


(defthm wvp-sha-512
(implies (and (bvp m) (< (len m) (expt 2 128)))
         (wvp (sha-512 m) 64) )
:hints(("goal"  :in-theory (disable digest-512 parsing padding-512))))


(defthm len-sha-512
(implies (and (bvp m) (< (len m) (expt 2 128)))
         (equal (len (sha-512 m)) 8 ))
:hints
(("goal"
  :use (:instance len-digest-512 (m (parsing (padding-512 m) 1024))
                  (hash-values (h-512)))
  :in-theory (disable digest-512 parsing padding-512))))


; sha-384

(defun sha-384 ( m)
  (if (bvp m)
      (let ((res  (digest-512 (parsing (padding-512 m) 1024) (h-384))))
           (list (nth 0 res)
                 (nth 1 res)
                 (nth 2 res)
                 (nth 3 res)
                 (nth 4 res)
                 (nth 5 res) ))
      nil))


(defthm wvp-sha-384
(implies (and (bvp m) (< (len m) (expt 2 128)))
         (wvp (sha-384 m) 64) )
:hints
(("goal"
   :in-theory (disable digest-512 parsing padding-512 wordp nth)
   :use (:instance len-digest-512 (m (parsing (padding-512 m) 1024))
             (hash-values (h-384))))))


(defthm len-sha-384
(implies (and (bvp m) (< (len m) (expt 2 128)))
         (equal (len (sha-384 m)) 6 ))
:hints
(("goal"
  :use (:instance len-digest-512 (m (parsing (padding-512 m) 1024))
                (hash-values (h-384)))
  :in-theory (disable digest-512 parsing padding-512))))
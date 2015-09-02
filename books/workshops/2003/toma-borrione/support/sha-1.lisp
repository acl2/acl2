;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHA-1
; Message digest functions and theorems
;------------------------------------------

;I strongly recommend after charging the book to do :comp t in order to accelerate the computation

; For a message M with length less than (expt 2 64) sha-1 returns a message digest of 160 bits (five words each of 32 bits).

;For message "abc"
;ACL2 !>(sha-1 '(0 1 1 0 0 0 0 1 0 1 1 0 0 0 1 0 0 1 1 0 0 0 1 1 ))

;((1 0 1 0 1 0 0 1 1 0 0 1
;    1 0 0 1 0 0 1 1 1 1 1 0 0 0 1 1 0 1 1 0)
; (0 1 0 0 0 1 1 1 0 0 0 0
;    0 1 1 0 1 0 0 0 0 0 0 1 0 1 1 0 1 0 1 0)
; (1 0 1 1 1 0 1 0 0 0 1 1
;    1 1 1 0 0 0 1 0 0 1 0 1 0 1 1 1 0 0 0 1)
; (0 1 1 1 1 0 0 0 0 1 0 1
;    0 0 0 0 1 1 0 0 0 0 1 0 0 1 1 0 1 1 0 0)
; (1 0 0 1 1 1 0 0 1 1 0 1 0
;    0 0 0 1 1 0 1 1 0 0 0 1 0 0 1 1 1 0 1))
;For the message "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" (448 bits)
;ACL2 !>(sha-1 '(0 1 1 0 0 0 0 1
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

;((1 0 0 0 0 1 0 0 1 0 0 1
;    1 0 0 0 0 0 1 1 1 1 1 0 0 1 0 0 0 1 0 0)
; (0 0 0 1 1 1 0 0 0 0 1 1
;    1 0 1 1 1 1 0 1 0 0 1 0 0 1 1 0 1 1 1 0)
; (1 0 1 1 1 0 1 0 1 0 1 0
;    1 1 1 0 0 1 0 0 1 0 1 0 1 0 1 0 0 0 0 1)
; (1 1 1 1 1 0 0 1 0 1 0 1
;    0 0 0 1 0 0 1 0 1 0 0 1 1 1 1 0 0 1 0 1)
; (1 1 1 0 0 1 0 1 0 1 0 0 0
;    1 1 0 0 1 1 1 0 0 0 0 1 1 1 1 0 0 0 1))

(IN-PACKAGE "ACL2")

(include-book "parsing")
(include-book "sha-functions")


; constants of sha-1


(defun K-1 (i)
 (if (and (integerp i)  (<= 0 i))
     (cond ((and (<= 0 i) (<= i 19))
             '(0 1 0 1 1 0 1 0 1 0 0 0
              0 0 1 0 0 1 1 1 1 0 0 1 1 0 0 1 1 0 0 1))
           ((and (<= 20 i) (<= i 39))
             '(0 1 1 0 1 1 1 0 1 1 0 1
              1 0 0 1 1 1 1 0 1 0 1 1 1 0 1 0 0 0 0 1))
           ((and (<= 40 i) (<= i 59))
             '(1 0 0 0 1 1 1 1 0 0 0 1
              1 0 1 1 1 0 1 1 1 1 0 0 1 1 0 1 1 1 0 0))
           ((and (<= 60 i) (<= i 79))
             '(1 1 0 0 1 0 1 0 0 1 1 0
              0 0 1 0 1 1 0 0 0 0 0 1 1 1 0 1 0 1 1 0)))
      nil))


(defthm wordp-K-1
(implies (and (integerp i) (<= 0 i) (<= i 79))
  (wordp (k-1 i) 32)))


; initial hash values for sha-1

(defun H-1 ()
    '((0 1 1 0 0 1 1 1 0 1 0 0
       0 1 0 1 0 0 1 0 0 0 1 1 0 0 0 0 0 0 0 1)
      (1 1 1 0 1 1 1 1 1 1 0 0
       1 1 0 1 1 0 1 0 1 0 1 1 1 0 0 0 1 0 0 1)
      (1 0 0 1 1 0 0 0 1 0 1 1
       1 0 1 0 1 1 0 1 1 1 0 0 1 1 1 1 1 1 1 0)
      (0 0 0 1 0 0 0 0 0 0 1 1
       0 0 1 0 0 1 0 1 0 1 0 0 0 1 1 1 0 1 1 0)
      (1 1 0 0 0 0 1 1 1 1 0 1
       0 0 1 0 1 1 1 0 0 0 0 1 1 1 1 1 0 0 0 0)))

(defthm wordp-h-1
 (and  (wvp (h-1) 32) (equal (len (h-1)) 5 )))


;constant of sha-1

(defun mask ()
  '(0 0 0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1))

(defthm wordp-mask
 (wordp (mask ) 32))


;---sha-1

;--- first method


(defun temp (j working-variables m-i-ext)
      (if (and (wvp working-variables 32) (equal (len working-variables) 5)
               (integerp j) (<= 0 j)
               (wvp  m-i-ext 32) (equal (len  m-i-ext) 80))
          (plus 32 (rotl 5 (nth 0 working-variables) 32)
                   (Ft j (nth 1 working-variables)
                   (nth 2 working-variables)
                   (nth 3 working-variables))
                   (nth 4 working-variables)
                   ( K-1 j)
                   (nth j  m-i-ext))
          nil))


(defthm wordp-temp
 (implies (and (wvp l 32) (equal (len l) 5)
               (integerp j) (<= 0 j) (< j 80)
               (wvp m 32) (equal (len m) 80))
          (wordp (temp j l m ) 32))
:hints
(("goal"
  :in-theory (disable k-1 ft rotl binary-plus rotl->rotr nth ))))


;prepare the schedule message

(defun prepare-ac ( j m-i)
(declare (xargs :measure (acl2-count (- 80 j))))
  (if (and  (integerp j) (<= 16 j)
             (wvp  m-i 32))
      (cond ((<= 80 j)  m-i)
            ((<= j 79)
             (prepare-ac (1+ j)
                        (append  m-i
                               (list (rotl 1 (bv-xor (nth (- j 3)  m-i)
                                                     (nth (- j 8)  m-i)
                                                     (nth (- j 14) m-i)
                                                     (nth (- j 16) m-i)) 32))))))
      nil))

(defun prepare (m-i)
  (if (wordp m-i 512)
      (prepare-ac 16 (parsing m-i 32))
      nil))

(defthm wvp-prepare-ac
  (implies (and  (integerp j) (<= 16 j) (wvp  m 32))
           (wvp (prepare-ac j m) 32))
:hints
(("goal"
  :in-theory (disable rotl binary-bv-xor rotl->rotr))))


(defthm len-prepare-ac
  (implies (and  (wvp  m 32) (integerp j) (<= 16 j) (<= j (len m) ))
           (equal (len (prepare-ac  j m))
                  (if (<= j 80)
                      (+ (- 80 j) (len m))
                      (len m))))
:hints
(("goal"
  :in-theory (disable rotl binary-bv-xor rotl->rotr))))


(defthm wvp-prepare
  (implies (wordp  m 512)
           (wvp (prepare  m) 32))
:hints (("goal" :in-theory (disable prepare-ac ))))


(defthm len-prepare
  (implies (wordp m 512)
           (equal (len (prepare m)) 80))
:hints (("goal" :in-theory (disable prepare-ac))))


; one step of digest
(defun digest-one-block-ac ( j working-variables m-i-ext)
(declare (xargs :measure (acl2-count (- 80 j))))
    (if (and (wvp working-variables 32) (equal (len working-variables ) 5)
             (integerp j) (<= 0 j)
             (wvp m-i-ext 32) (equal (len m-i-ext) 80))
        (if (<= 80 j)
            working-variables
            (digest-one-block-ac (+ 1 j)
                        (list  (temp j  working-variables m-i-ext)
                               (nth 0 working-variables)
                               (rotl 30 (nth 1 working-variables) 32)
                               (nth 2 working-variables)
                               (nth 3 working-variables))
                         m-i-ext) )
      nil))


(defun digest-one-block (hash-values m-i-ext)
   (if (and  (wvp hash-values 32) (equal (len hash-values) 5)
             (wvp m-i-ext 32) (equal (len m-i-ext) 80))
       (digest-one-block-ac 0 hash-values  m-i-ext)
       nil))


(defthm wvp-digest-one-block-ac
 (implies (and  (wvp l 32) (equal (len l) 5)
                (integerp j) (<= 0 j)
                (wvp m 32) (equal (len m) 80))
          (wvp (digest-one-block-ac j l m ) 32))
:hints
(("goal"
  :in-theory (disable  temp nth rotl rotl->rotr))))


(defthm len-digest-one-block-ac
 (implies (and (wvp l 32) (equal (len l) 5)
               (integerp j) (<= 0 j)
               (wvp m 32) (equal (len m) 80))
          (equal (len (digest-one-block-ac j l m )) 5))
:hints
(("goal"
  :in-theory (disable  temp nth rotl rotl->rotr ))))


(defthm wvp-digest-one-block
 (implies (and  (wvp l 32) (equal (len l) 5)
                (wvp m 32) (equal (len m) 80))
          (wvp (digest-one-block l m ) 32))
:hints
(("goal"
  :in-theory (disable digest-one-block-ac))))


(defthm len-digest-one-block
 (implies (and (wvp l 32) (equal (len l) 5)
               (wvp m 32) (equal (len m) 80))
          (equal (len (digest-one-block  l m )) 5))
:hints
(("goal"
  :in-theory (disable digest-one-block-ac ))))


;intermediate hash
(defun intermediate-hash ( l1 l2)
 (if (and  (wvp l1 32) (equal (len l1) 5)
           (wvp l2 32) (equal (len l2) 5) )
     (list (plus 32 (nth 0 l1) (nth 0 l2) )
           (plus 32 (nth 1 l1) (nth 1 l2) )
           (plus 32 (nth 2 l1) (nth 2 l2) )
           (plus 32 (nth 3 l1) (nth 3 l2) )
           (plus 32 (nth 4 l1) (nth 4 l2) ))
     nil))


(defthm wvp-intermediate-hash
 (implies (and  (wvp l1 32) (equal (len l1) 5)
                (wvp l2 32) (equal (len l2) 5) )
          (wvp (intermediate-hash l1 l2 ) 32))
:hints
(("goal"
  :in-theory (disable binary-plus wordp nth ))))


(defthm len-intermediate-hash
 (implies (and  (wvp l1 32) (equal (len l1) 5)
                (wvp l2 32) (equal (len l2) 5) )
          (equal (len (intermediate-hash l1 l2 )) 5)))


(defun digest ( m hash-values)
  (if (and (wvp m 512) (wvp hash-values 32) (equal (len hash-values) 5))
      (if (endp m)  hash-values
          (digest (cdr m)
               (intermediate-hash hash-values
                     (digest-one-block hash-values (prepare (car m))))))
       nil) )


(defthm wvp-digest
 (implies (and (wvp m 512) (wvp hash-values 32)
               (equal (len hash-values) 5))
          (wvp (digest m hash-values ) 32) )
:hints
(("goal"
  :in-theory (disable intermediate-hash digest-one-block prepare parsing ))))


(defthm len-digest
 (implies (and (wvp m 512) (wvp hash-values 32) (not (endp m))
               (equal (len hash-values) 5))
          (equal (len (digest m hash-values )) 5) )
:hints
(("goal"
  :in-theory (disable intermediate-hash digest-one-block prepare  ))))


(defun sha-1 ( m)
  (if (and (bvp m) (< (len m) (expt 2 64)))
      (digest (parsing (padding-1-256 m) 512) (h-1))
      nil))


(defthm wvp-sha-1
(implies (and (bvp m) (< (len m) (expt 2 64)))
         (wvp (sha-1 m) 32) )
:hints(("goal"  :in-theory (disable digest parsing padding-1-256))))


(defthm len-sha-1
(implies (and (bvp m) (< (len m) (expt 2 64)))
         (equal (len (sha-1 m)) 5 ))
:hints(("goal"
:use (:instance len-digest (m (parsing (padding-1-256 m) 512)) (hash-values (h-1)))
:in-theory (disable digest parsing padding-1-256 ))))


; --- second method of sha-1 (no preparing of the message)

(defun s (j)
  (if (and (integerp j) (<= 0 j))
      (bv-int-big-endian (bv-and (int-bv-big-endian j) (mask)))
      nil ))


;(defthm integerp-s
; (implies (and  (integerp j) (<= 0 j))
;  (integerp (s j)))
;:hints (("goal" :in-theory (disable bv-int-big-endian int-bv-big-endian mask ))
;))

(defun temp-1 (j working-variables m-i)
  (if (and (wvp working-variables 32) (equal (len working-variables) 5)
           (integerp j) (<= 0 j)
           (wvp  m-i 32) (equal (len  m-i) 16))
      (plus 32 (rotl 5 (nth 0 working-variables) 32)
               (Ft j (nth 1 working-variables)
               (nth 2 working-variables)
               (nth 3 working-variables))
               (nth 4 working-variables)
               (nth  (s j)  m-i)
               (K-1 j) )
      nil))

;(defthm wordp-temp-1
; (implies (and  (wvp l 32) (equal (len l) 5)
;             (integerp j) (<= 0 j) (< j 80)
;             (wvp m 32) (equal (len m) 16))
;  (wordp (temp-1 j l m ) 32))
;:hints (("goal" :in-theory (disable k-1 ft rotl binary-plus rotl->rotr nth ))
;))

(defun wo (j  m-i )
 (if (and (integerp j) (<= 0 j)
          (wvp  m-i 32))
     (rotl 1 (bv-xor
              (nth (bv-int-big-endian (bv-and (int-bv-big-endian (+ 13 (s j)))
                                              (mask)))  m-i)
              (nth (bv-int-big-endian (bv-and (int-bv-big-endian (+ 8  (s j)))
                                              (mask)))  m-i)
              (nth (bv-int-big-endian (bv-and (int-bv-big-endian (+ 2  (s j)))
                                              (mask)))  m-i)
              (nth (bv-int-big-endian (bv-and (int-bv-big-endian j)
                                              (mask)))  m-i)) 32)
      nil))


(defun digest-one-block-1 ( j working-variables  m-i )
(declare (xargs :measure (acl2-count (- 80 j))))
    (if (and (wvp working-variables 32) (equal (len working-variables) 5)
             (integerp j) (<= 0 j)
             (wvp   m-i 32) (equal (len  m-i) 16))
        (if (<= 80 j)
             working-variables
            (if (>= j 16)
                (digest-one-block-1 (+ 1 j)
                        (list (temp-1 j working-variables (repl (s j)
                                       (wo j  m-i)  m-i))
                              (nth 0 working-variables)
                              (rotl 30 ( nth 1 working-variables) 32)
                              (nth 2 working-variables)
                              (nth 3 working-variables))
                        (repl  (s j) (wo j  m-i)  m-i) )
                (digest-one-block-1 (+ 1 j)
                        (list  (temp-1 j  working-variables m-i )
                               (nth 0 working-variables)
                               (rotl 30 (nth 1 working-variables) 32)
                               (nth 2 working-variables)
                               (nth 3 working-variables))
                         m-i ) ))
      nil))


(defun digest-1 ( m hash-values)
  (if (and (wvp m 512) (wvp hash-values 32) (equal (len hash-values) 5)  )
      (if (endp  m)  hash-values
          (digest-1 (cdr  m)
             (intermediate-hash hash-values
                 (digest-one-block-1 0 hash-values (parsing (car  m) 32)))))
       nil) )


(defun sha-1-2 (  m)
  (if (and (bvp m) (< (len m) (expt 2 64)))
      (digest-1 (parsing (padding-1-256 m) 512) (h-1))
      nil))

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)

(include-book "des")

(defconst *message*
  '(#x01 #x23 #x45 #x67 #x89 #xAB #xCD #xEF))

(defconst *ip-message-bits*
  '(1 1 0 0 1 1 0 0 0 0 0 0 0 0 0 0
      1 1 0 0 1 1 0 0 1 1 1 1 1 1 1 1
      1 1 1 1 0 0 0 0 1 0 1 0 1 0 1 0
      1 1 1 1 0 0 0 0 1 0 1 0 1 0 1 0))

(assert!
 (equal (IP (bytes-to-8bits-msb *message*))
        *ip-message-bits*))

(defconst *expanded-message-right*
  '(0 1 1 1 1 0 1 0 0 0 0 1 0 1 0 1 0 1 0 1 0 1 0 1
      0 1 1 1 1 0 1 0 0 0 0 1 0 1 0 1 0 1 0 1 0 1 0 1))

(assert!
  (equal (expand (cdr (cons (prefix-nth *ip-message-bits* 32)
                            (get-nth *ip-message-bits* 32))))
         *expanded-message-right*))

(defconst *xored-message*
  '(0 1 1 0 0 0 0 1 0 0 0 1 0 1 1 1 1 0 1 1 1 0 1 0
      1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 0 1 0 0 1 1 1))

(defconst *key*
  '(#x13 #x34 #x57 #x79 #x9B #xBC #xDF #xF1))

(defconst *key-bits*
  '(0 0 0 1 0 0 1 1 0 0 1 1 0 1 0 0
      0 1 0 1 0 1 1 1 0 1 1 1 1 0 0 1
      1 0 0 1 1 0 1 1 1 0 1 1 1 1 0 0
      1 1 0 1 1 1 1 1 1 1 1 1 0 0 0 1))

(assert!
  (equal (bytes-to-8bits-msb *key*)
         *key-bits*))

(defconst *key-pc-1-bits*
  '(1 1 1 1 0 0 0 0 1 1 0 0 1 1
      0 0 1 0 1 0 1 0 1 0 1 1 1 1
      0 1 0 1 0 1 0 1 0 1 1 0 0 1
      1 0 0 1 1 1 1 0 0 0 1 1 1 1))

(defconst *key-shifted-0*
  '(1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1
      0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1))

(assert!
  (equal (permuted-choice-1 *key-bits*)
         *key-pc-1-bits*))

(defconst *key-shifted-1*
  '(1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1
      1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0))

(defconst *key-round-1-bits*
  '(0 0 0 1 1 0 1 1 0 0 0 0
      0 0 1 0 1 1 1 0 1 1 1 1
      1 1 1 1 1 1 0 0 0 1 1 1
      0 0 0 0 0 1 1 1 0 0 1 0))

(assert!
  (and (equal (get-round-key *key-shifted-0* 0 t)
              *key-shifted-1*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-0* 0 t))
              *key-round-1-bits*)))

(assert!
  (equal (xor-bit-list *expanded-message-right*
                       *key-round-1-bits*)
         *xored-message*))

(defconst *S-boxes-output*
  '(0 1 0 1 1 1 0 0 1 0 0 0 0 0 1 0
      1 0 1 1 0 1 0 1 1 0 0 1 0 1 1 1))

(assert!
  (equal (apply-S-boxes (48-to-6bit-groups *xored-message*)
                        *S-boxes*)
         *S-boxes-output*))

(defconst *permuted-output*
  '(0 0 1 0 0 0 1 1 0 1 0 0 1 0 1 0
      1 0 1 0 1 0 0 1 1 0 1 1 1 0 1 1))

(assert!
  (equal (permute *S-boxes-output*)
         *permuted-output*))

(defconst *xored-left-feistel*
  '(1 1 1 0 1 1 1 1 0 1 0 0 1 0 1 0
      0 1 1 0 0 1 0 1 0 1 0 0 0 1 0 0))

(assert!
  (equal (xor-bit-list (car (cons (prefix-nth *ip-message-bits* 32)
                                  (get-nth *ip-message-bits* 32)))
                       *permuted-output*)
         *xored-left-feistel*))

(defconst *key-shifted-2*
  '(1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1
      0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1))

(defconst *key-round-2-bits*
  '(0 1 1 1 1 0 0 1 1 0 1 0
      1 1 1 0 1 1 0 1 1 0 0 1
      1 1 0 1 1 0 1 1 1 1 0 0
      1 0 0 1 1 1 1 0 0 1 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-1* 1 t)
              *key-shifted-2*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-1* 1 t))
              *key-round-2-bits*)))

(defconst *key-shifted-3*
  '(0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1
      0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1))

(defconst *key-round-3-bits*
  '(0 1 0 1 0 1 0 1 1 1 1 1
      1 1 0 0 1 0 0 0 1 0 1 0
      0 1 0 0 0 0 1 0 1 1 0 0
      1 1 1 1 1 0 0 1 1 0 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-2* 2 t)
              *key-shifted-3*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-2* 2 t))
              *key-round-3-bits*)))

(defconst *key-shifted-4*
  '(0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0
      0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1))

(defconst *key-round-4-bits*
  '(0 1 1 1 0 0 1 0 1 0 1 0
      1 1 0 1 1 1 0 1 0 1 1 0
      1 1 0 1 1 0 1 1 0 0 1 1
      0 1 0 1 0 0 0 1 1 1 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-3* 3 t)
              *key-shifted-4*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-3* 3 t))
              *key-round-4-bits*)))

(defconst *key-shifted-5*
  '(1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0
      0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1))

(defconst *key-round-5-bits*
  '(0 1 1 1 1 1 0 0 1 1 1 0
      1 1 0 0 0 0 0 0 0 1 1 1
      1 1 1 0 1 0 1 1 0 1 0 1
      0 0 1 1 1 0 1 0 1 0 0 0))

(assert!
  (and (equal (get-round-key *key-shifted-4* 4 t)
              *key-shifted-5*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-4* 4 t))
              *key-round-5-bits*)))

(defconst *key-shifted-6*
  '(0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1
      1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1))

(defconst *key-round-6-bits*
  '(0 1 1 0 0 0 1 1 1 0 1 0
      0 1 0 1 0 0 1 1 1 1 1 0
      0 1 0 1 0 0 0 0 0 1 1 1
      1 0 1 1 0 0 1 0 1 1 1 1))

(assert!
  (and (equal (get-round-key *key-shifted-5* 5 t)
              *key-shifted-6*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-5* 5 t))
              *key-round-6-bits*)))

(defconst *key-shifted-7*
  '(1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0
      0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0))

(defconst *key-round-7-bits*
  '(1 1 1 0 1 1 0 0 1 0 0 0
      0 1 0 0 1 0 1 1 0 1 1 1
      1 1 1 1 0 1 1 0 0 0 0 1
      1 0 0 0 1 0 1 1 1 1 0 0))

(assert!
  (and (equal (get-round-key *key-shifted-6* 6 t)
              *key-shifted-7*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-6* 6 t))
              *key-round-7-bits*)))

(defconst *key-shifted-8*
  '(0 0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1
      1 0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1))

(defconst *key-round-8-bits*
  '(1 1 1 1 0 1 1 1 1 0 0 0
      1 0 1 0 0 0 1 1 1 0 1 0
      1 1 0 0 0 0 0 1 0 0 1 1
      1 0 1 1 1 1 1 1 1 0 1 1))

(assert!
  (and (equal (get-round-key *key-shifted-7* 7 t)
              *key-shifted-8*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-7* 7 t))
              *key-round-8-bits*)))

(defconst *key-shifted-9*
  '(0 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0
      0 0 1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1))

(defconst *key-round-9-bits*
  '(1 1 1 0 0 0 0 0 1 1 0 1
      1 0 1 1 1 1 1 0 1 0 1 1
      1 1 1 0 1 1 0 1 1 1 1 0
      0 1 1 1 1 0 0 0 0 0 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-8* 8 t)
              *key-shifted-9*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-8* 8 t))
              *key-round-9-bits*)))

(defconst *key-shifted-10*
  '(0 1 0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1
      1 1 1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0))

(defconst *key-round-10-bits*
  '(1 0 1 1 0 0 0 1 1 1 1 1
      0 0 1 1 0 1 0 0 0 1 1 1
      1 0 1 1 1 0 1 0 0 1 0 0
      0 1 1 0 0 1 0 0 1 1 1 1))

(assert!
  (and (equal (get-round-key *key-shifted-9* 9 t)
              *key-shifted-10*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-9* 9 t))
              *key-round-10-bits*)))

(defconst *key-shifted-11*
  '(0 1 0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1
      1 1 0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1))

(defconst *key-round-11-bits*
  '(0 0 1 0 0 0 0 1 0 1 0 1
      1 1 1 1 1 1 0 1 0 0 1 1
      1 1 0 1 1 1 1 0 1 1 0 1
      0 0 1 1 1 0 0 0 0 1 1 0))

(assert!
  (and (equal (get-round-key *key-shifted-10* 10 t)
              *key-shifted-11*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-10* 10 t))
              *key-round-11-bits*)))

(defconst *key-shifted-12*
  '(0 1 0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1
      0 0 0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1))

(defconst *key-round-12-bits*
  '(0 1 1 1 0 1 0 1 0 1 1 1
      0 0 0 1 1 1 1 1 0 1 0 1
      1 0 0 1 0 1 0 0 0 1 1 0
      0 1 1 1 1 1 1 0 1 0 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-11* 11 t)
              *key-shifted-12*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-11* 11 t))
              *key-round-12-bits*)))

(defconst *key-shifted-13*
  '(0 1 1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1
      0 1 1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0))

(defconst *key-round-13-bits*
  '(1 0 0 1 0 1 1 1 1 1 0 0
      0 1 0 1 1 1 0 1 0 0 0 1
      1 1 1 1 1 0 1 0 1 0 1 1
      1 0 1 0 0 1 0 0 0 0 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-12* 12 t)
              *key-shifted-13*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-12* 12 t))
              *key-round-13-bits*)))

(defconst *key-shifted-14*
  '(1 1 1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1
      1 1 1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1))

(defconst *key-round-14-bits*
  '(0 1 0 1 1 1 1 1 0 1 0 0
      0 0 1 1 1 0 1 1 0 1 1 1
      1 1 1 1 0 0 1 0 1 1 1 0
      0 1 1 1 0 0 1 1 1 0 1 0))

(assert!
  (and (equal (get-round-key *key-shifted-13* 13 t)
              *key-shifted-14*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-13* 13 t))
              *key-round-14-bits*)))

(defconst *key-shifted-15*
  '(1 1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1
      1 0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1))

(defconst *key-round-15-bits*
  '(1 0 1 1 1 1 1 1 1 0 0 1
      0 0 0 1 1 0 0 0 1 1 0 1
      0 0 1 1 1 1 0 1 0 0 1 1
      1 1 1 1 0 0 0 0 1 0 1 0))

(assert!
  (and (equal (get-round-key *key-shifted-14* 14 t)
              *key-shifted-15*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-14* 14 t))
              *key-round-15-bits*)))

(defconst *key-shifted-16*
  '(1 1 1 1 0 0 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 0 1 0 1 1 1 1
      0 1 0 1 0 1 0 1 0 1 1 0 0 1 1 0 0 1 1 1 1 0 0 0 1 1 1 1))

(defconst *key-round-16-bits*
  '(1 1 0 0 1 0 1 1 0 0 1 1
      1 1 0 1 1 0 0 0 1 0 1 1
      0 0 0 0 1 1 1 0 0 0 0 1
      0 1 1 1 1 1 1 1 0 1 0 1))

(assert!
  (and (equal (get-round-key *key-shifted-15* 15 t)
              *key-shifted-16*)
       (equal (permuted-choice-2 (get-round-key *key-shifted-15* 15 t))
              *key-round-16-bits*)))

(defconst *pre-final-perm-message*
  '(0 0 0 0 1 0 1 0 0 1 0 0 1 1 0 0 1 1 0 1 1 0 0 1 1 0 0 1 0 1 0 1
      0 1 0 0 0 0 1 1 0 1 0 0 0 0 1 0 0 0 1 1 0 0 1 0 0 0 1 1 0 1 0 0))

(assert!
  (let ((half-parts (encrypt-decrypt-64bit-block1 (cons (prefix-nth *ip-message-bits* 32)
                                                        (get-nth *ip-message-bits* 32))
                                                  *key-pc-1-bits* 0 t)))
    (equal (append (car half-parts)
                   (cdr half-parts))
           *pre-final-perm-message*)))

(defconst *final-permuted-cipher*
  '(1 0 0 0 0 1 0 1 1 1 1 0 1 0 0 0 0 0 0 1 0 0 1 1 0 1 0 1 0 1 0 0
      0 0 0 0 1 1 1 1 0 0 0 0 1 0 1 0 1 0 1 1 0 1 0 0 0 0 0 0 0 1 0 1))

(assert!
  (equal (IP-inverse *pre-final-perm-message*)
         *final-permuted-cipher*))

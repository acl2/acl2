(in-package "ACL2")

(include-book "centaur/gl/gl" :dir :system)
(include-book "../util/byte-operations")


; (set-print-base 16 state)

;
; This table specifies the input permutation on a 64-bit block.
; The meaning is as follows: the first bit of the output is taken from the 58th
; bit of the input the second bit from the 50th bit, and so on, with the last
; bit of the output taken from the 7th bit of the input.
;

(defconst *IP-table*
  '(58 50 42 34 26 18 10 2 60 52 44 36 28 20 12 4
      62 54 46 38 30 22	14 6 64	56 48 40 32 24 16 8
      57 49 41 33 25 17	9 1 59 51 43 35	27 19 11 3
      61 53 45 37 29 21	13 5 63	55 47 39 31 23 15 7))

;
; The final permutation is the inverse of the initial permutation
; the table is interpreted similarly.
;

(defconst *IP-inverse-table*
  '(40 8 48 16 56 24 64 32 39 7 47 15 55 23 63 31
      38 6 46 14 54 22 62 30 37	5 45 13	53 21 61 29
      36 4 44 12 52 20 60 28 35	3 43 11	51 19 59 27
      34 2 42 10 50 18 58 26 33	1 41 9 49 17 57	25))

;
; The expansion function is interpreted as for the initial and final
; permutations. Note that some bits from the input are duplicated at the output
; e.g. the fifth bit of the input is duplicated in both the sixth and eighth
; bit of the output. Thus, the 32-bit half-block is expanded to 48 bits.
;

(defconst *expand-table*
  '(32 1 2 3 4 5 4 5 6 7 8 9 8 9 10 11 12 13 12 13 14
       15 16 17 16 17 18 19 20 21 20 21 22 23 24 25 24
       25 26 27 28 29 28 29 30 31 32 1))

;
; The P permutation shuffles the bits of a 32-bit half-block.
;

(defconst *permute-table*
  '(16 7 20 21 29 12 28 17 1 15 23 26 5 18 31 10
       2 8 24 14 32 27 3 9 19 13 30 6 22 11 4 25))

;
; The Left and Right halves of the table show which bits from the input key
; form the left and right sections of the key schedule state. Note that only
; 56 bits of the 64 bits of the input are selected; the remaining eight were
; specified for use as parity bits.
;

(defconst *permuted-choice-1-left-table*
  '(57 49 41 33 25 17 9 1 58 50 42 34 26 18
       10 2 59 51 43 35 27 19 11 3 60 52 44 36))

(defconst *permuted-choice-1-right-table*
  '(63 55 47 39 31 23 15 7 62 54 46 38 30 22
       14 6 61 53 45 37 29 21 13 5 28 20 12 4))

;
; This permutation selects the 48-bit subkey for each round from the
; 56-bit key-schedule state.
;

(defconst *permuted-choice-2-table*
  '(14 17 11 24 1 5 3 28 15 6 21 10 23 19 12 4
       26 8 16 7 27 20 13 2 41 52 31 37 47 55 30 40
       51 45 33 48 44 49 39 56 34 53 46 42 50 36 29 32))

;
; This table lists the eight S-boxes used in DES. Each S-box replaces
; a 6-bit input with a 4-bit output. Given a 6-bit input, the 4-bit
; output is found by selecting the row using the outer two bits, and
; the column using the inner four bits. For example, an input 011011
; has outer bits 01 and inner bits 11011; noting that the first row
; is "00" and the first column is 0000, the corresponding output for
; S-box S5 would be 1001 (=9), the value in the second row, 14th column.
;

(defconst *S1-table*
  '((14 4 13 1 2 15 11 8 3 10 6 12 5 9 0 7)
    (0 15 7 4 14 2 13 1 10 6 12 11 9 5 3 8)
    (4 1 14 8 13 6 2 11 15 12 9 7 3 10 5 0)
    (15 12 8 2 4 9 1 7 5 11 3 14 10 0 6 13)))

(defconst *S2-table*
  '((15 1 8 14 6 11 3 4 9 7 2 13 12 0 5 10)
    (3 13 4 7 15 2 8 14 12 0 1 10 6 9 11 5)
    (0 14 7 11 10 4 13 1 5 8 12 6 9 3 2 15)
    (13 8 10 1 3 15 4 2 11 6 7 12 0 5 14 9)))

(defconst *S3-table*
  '((10	0 9 14 6 3 15 5 1 13 12 7 11 4 2 8)
    (13 7 0 9 3 4 6 10 2 8 5 14 12 11 15 1)
    (13 6 4 9 8 15 3 0 11 1 2 12 5 10 14 7)
    (1 10 13 0 6 9 8 7 4 15 14 3 11 5 2 12)))

(defconst *S4-table*
  '((7 13 14 3 0 6 9 10 1 2 8 5 11 12 4 15)
    (13 8 11 5 6 15 0 3 4 7 2 12 1 10 14 9)
    (10 6 9 0 12 11 7 13 15 1 3 14 5 2 8 4)
    (3 15 0 6 10 1 13 8 9 4 5 11 12 7 2 14)))

(defconst *S5-table*
  '((2 12 4 1 7 10 11 6 8 5 3 15 13 0 14 9)
    (14	11 2 12 4 7 13 1 5 0 15 10 3 9 8 6)
    (4 2 1 11 10 13 7 8 15 9 12 5 6 3 0 14)
    (11 8 12 7 1 14 2 13 6 15 0 9 10 4 5 3)))

(defconst *S6-table*
  '((12 1 10 15 9 2 6 8 0 13 3 4 14 7 5 11)
    (10 15 4 2 7 12 9 5 6 1 13 14 0 11 3 8)
    (9 14 15 5 2 8 12 3 7 0 4 10 1 13 11 6)
    (4 3 2 12 9 5 15 10 11 14 1 7 6 0 8 13)))

(defconst *S7-table*
  '((4 11 2 14 15 0 8 13 3 12 9 7 5 10 6 1)
    (13 0 11 7 4 9 1 10 14 3 5 12 2 15 8 6)
    (1 4 11 13 12 3 7 14 10 15 6 8 0 5 9 2)
    (6 11 13 8 1 4 10 7 9 5 0 15 14 2 3 12)))

(defconst *S8-table*
  '((13 2 8 4 6 15 11 1 10 9 3 14 5 0 12 7)
    (1 15 13 8 10 3 7 4 12 5 6 11 0 14 9 2)
    (7 11 4 1 9 12 14 2 0 6 10 13 15 3 5 8)
    (2 1 14 7 4 10 8 13 15 12 9 0 3 5 6 11)))

;
; The following constant is defined to be a list of the S-boxes in order from 1
; to 8, so that successive 6-bit groups of a 48bit number can be successively
; put through the appropriate S-box.
;

(defconst *S-boxes*
  (cons *S1-table*
        (cons *S2-table*
              (cons *S3-table*
                    (cons *S4-table*
                          (cons *S5-table*
                                (cons *S6-table*
                                      (cons *S7-table*
                                            (cons *S8-table* nil)))))))))

;
; Before the round subkey is selected, each half of the key schedule state is
; rotated left by a number of places. This table specifies the number of places
; rotated.
;

(defconst *key-rotation*
  '(1 1 2 2 2 2 2 2 1 2 2 2 2 2 2 1 0))

;
; A generic method that applies a generic table to a bit-list.
; This method reads each member of the table and chooses the corresponding bit
; from the input x-bits to construct a new list of bits.
;

(defun apply-table (x-bits table)
  (if (atom table)
      nil
    (cons (Nth (- (car table)
		  1)
               x-bits)
          (apply-table x-bits
                       (cdr table)))))

;
; Wrapper over the apply-table method that works on a 64-bit input and a 64-bit
; table (*IP-table*) that performs the initial permutation of a message block.
;

(defun IP(x-bits)
  (if (not (64-bitp x-bits))
      nil
    (apply-table x-bits
                   *IP-table*)))

;
; Methods that are necessary for the theorem below regarding IP being a permutation
;

(defun mem (e x)
  (if (atom x)
      nil
    (or (equal e (car x))
	(mem e (cdr x)))))

(defun del (e x)
  (if (atom x)
      nil
    (if (equal e (car x))
	(cdr x)
      (cons (car x)
	    (del e
		 (cdr x))))))

(defun perm (x y)
  (if (atom x)
      (atom y)
    (and (member (car x) y)
	 (perm (cdr x)
	       (del (car x)
		    y)))))

;
; This theorem tries to prove that the result of IP on a list of 64
; bits is a permutation of the same list.
; NOT PROVEN

;(defthm IP-is-a-permutation
;  (implies (64-bitp x-bits)
;	   (perm x-bits
;		 (IP x-bits))))

;
; Test case for the above theorem
;
(defthm IP-test-case-1
  (perm (string-to-bits-msb "abcdefgh")
	(IP (string-to-bits-msb "abcdefgh"))))

;
; Wrapper over the apply-table method that works on a 64-bit input and a 64-bit
; table (*IP-inverse-table*) that performs the inverse initial permutation of a
; message block.
;

(defun IP-inverse(x-bits)
  (if (not (64-bitp x-bits))
      nil
    (apply-table x-bits
                   *IP-inverse-table*)))

;
; Theorem stating that IP-inverse is also a permutation of the input
; NOT PROVEN

;(defthm IP-inverse-is-a-permutation
;  (implies (64-bitp x-bits)
;	   (perm x-bits
;		 (IP-inverse x-bits))))

;
; Test case for the above theorem
;
(defthm IP-inverse-test-case-1
  (perm (string-to-bits-msb "abcdefgh")
	(IP-inverse (string-to-bits-msb "abcdefgh"))))

;
; Theorem that states that IP-inverse inverts the permutation of IP
; and returns the original list
;

(defun gen (n)
  (declare (xargs :guard (natp n)
                  :measure (nfix n)))
  (cond ((zp n)
         nil)
        (t
         (cons (GL::g-number (list (list (- 128 (* 2 n))
                                         (- 128 (- (* 2 n) 1)))))
               (gen (- n 1))))))

(defconst *gl-const*
  (gen 64))

(def-gl-thm IP-inverse-inverts-IP-gl
  :hyp (64-bitp x)
  :concl (equal (IP-inverse (IP x))
		x)
  :g-bindings `((x ,*gl-const*)))

;
; Test case for the above theorem
;
(defthm IP-inverse-IP-test-case-1
  (equal (string-to-bits-msb "abcdefgh")
	 (IP-inverse (IP (string-to-bits-msb "abcdefgh")))))

;
; Wrapper over the apply-table method that works on a 32-bit input and a 48-bit
; table (*expand-table*) that performs the expansion of a block.
;

(defun expand(x-bits)
  (if (not (32-bitp x-bits))
      nil
    (apply-table x-bits
                   *expand-table*)))

;
; Theorem stating that the result of an expand operation returns 48 bits
;

(defthm expand-returns-48bits
  (implies (32-bitp x-bits)
	   (equal (len (expand x-bits))
		  48)))

;
; Wrapper over the apply-table method that works on a 32-bit input and a 32-bit
; table (*permute-table*) that performs the permutation of a block.
;

(defun permute(x-bits)
  (if (not (32-bitp x-bits))
      nil
    (apply-table x-bits
                   *permute-table*)))

;
; Theorem to prove that permute is a permutation
; NOT PROVEN

;(defthm permute-is-a-permutation
;  (implies (32-bitp x-bits)
;	   (perm x-bits
;		 (permute x-bits))))

;
; Test case for the above theorem
;
(defthm permute-test-case-1
  (perm (string-to-bits-msb "abcd")
	(permute (string-to-bits-msb "abcd"))))

;
; Wrapper over the apply-table method that works on a 64-bit key and returns a 56-bit
; key by using two tables (left and right) that performs the construction of the
; appended subkey.
;

(defun permuted-choice-1(key-bits)
  (if (not (64-bitp key-bits))
      nil
    (append (apply-table key-bits
                         *permuted-choice-1-left-table*)
            (apply-table key-bits
                         *permuted-choice-1-right-table*))))
;
; Wrapper over the apply-table method that works on a 64-bit key and a 28-bit
; table (*permuted-choice-1-table*) that performs the construction of the right
; half of the subkey.
;

(defun permuted-choice-2(key-bits)
  (if (not (56-bitp key-bits))
      nil
    (apply-table key-bits
                 *permuted-choice-2-table*)))

;
; This method gets the row to look for in the S-boxes by constructing it from
; the 1st and last bits of the 6-bit input.
;

(defun get-xx(x-bits)
  (+ (* (Nth 0 x-bits) 2)
     (Nth 5 x-bits)))

;
; This method gets the column to look for in the S-boxes by constructing it from
; the middle 4 bits of the 6-bit input.
;

(defun get-yyyy(x-bits)
  (+ (* (Nth 1 x-bits) 8)
     (* (Nth 2 x-bits) 4)
     (* (Nth 3 x-bits) 2)
     (Nth 4 x-bits)))

;
; A generic method to apply a particular substitution table to a 6-bit input
;

(defun apply-subst-table(x-bits table)
  (if (not (6-bitp x-bits))
      nil
    (number-to-4bits-msb (Nth (get-yyyy x-bits)
                              (Nth (get-xx x-bits)
                                   table)))))

;
; Code to shift a bit-list based on whether it is encryption or decryption
; In case of encryption this method should left shift a bit-list by num places
; In case of decryption this method should right shift the bit list by num places
;

(defun rotate-bits(x-bits num encrypt)
  (if encrypt
      (append (get-nth x-bits num)
              (prefix-nth x-bits num))
    (append (get-nth x-bits (- (len x-bits)
                               num))
            (prefix-nth x-bits (- (len x-bits)
                                  num)))))


;
; This method gets the rotation list corresponding to the current index
; In case of encryption it is *key-rotation* while in case of decryption it is
; (reverse (*key-rotation*)) as keys are repeated in the reverse order.
;

(defun get-key-rotation-list (encrypt)
  (if (not (booleanp encrypt))
      nil
    (if encrypt
        *key-rotation*
      (reverse *key-rotation*))))

;
; This method gets the next subkey or round-key according to the number of
; rotations that need to be applied to the current key to get to it. The number
; of rotations is retrieved from the constant *key-rotation*. The current key
; kCurr is supposed to be of the form (kCurrLeft . kCurrRight) where each of
; kCurrLeft and kCurrRight are bit-lists of 28 bits.
;

(defun get-round-key (kCurr round encrypt)
  (let* ((kLeft (prefix-nth kCurr 28))
        (kRight (get-nth kCurr 28))
        (key-rotation-list (get-key-rotation-list encrypt))
        (num-shift (Nth round key-rotation-list)))
    (append (rotate-bits kLeft num-shift encrypt)
            (rotate-bits kRight num-shift encrypt))))

;
; This method applies the 8 S-boxes in sequence to the 8 6-bit groups.
; The constant *S-boxes* that is passed in as subst-tables is arranged in such
; a way that its structure matches the order of the 6-bit groups exactly.
;

(defun apply-S-boxes(6-bit-groups subst-tables)
  (if (atom 6-bit-groups)
      nil
    (append (apply-subst-table (car 6-bit-groups)
                               (car subst-tables))
            (apply-S-boxes (cdr 6-bit-groups)
                           (cdr subst-tables)))))
;
; Method to group a 48-bit list input 8 groups of 6 bits each
;

(defun 48-to-6bit-groups(x-bits)
  (declare (xargs :measure (len x-bits)))
  (if (atom x-bits)
      nil
    (if (<= (len x-bits) 6)
        (cons x-bits nil)
      (cons (prefix-nth x-bits 6)
            (48-to-6bit-groups (get-nth x-bits 6))))))

;
; A method that calls bits-to-nbit-groups to partition the bit list into 64 bit
; blocks.
;

(defun bits-to-64bit-blocks(x-bits)
  (declare (xargs :measure (len x-bits)))
  (if (atom x-bits)
      nil
    (if (<= (len x-bits) 64)
        (cons x-bits nil)
      (cons (prefix-nth x-bits 64)
            (bits-to-64bit-blocks (get-nth x-bits 64))))))

;
; The code for the feistel function (F). Following are the steps involved:
; Expansion 32-bit half-block is expanded to 48 bits using the expansion
; permutation.  Key mixing The result is combined with a subkey using an XOR
; operation.  Substitution The block is divided into eight 6-bit pieces before
; processing by the S-boxes, or substitution boxes.  Permutation Finally, the
; 32 outputs from the S-boxes are rearranged according to a fixed permutation,
; the P-box.
;

(defun feistel-fn (half-block-bits subkey-48)
  (if (or (not (32-bitp half-block-bits))
          (not (48-bitp subkey-48)))
      nil
    (let* ((expanded-bits (expand half-block-bits))
           (xor-bits (xor-bit-list expanded-bits
                                   subkey-48))
           (6bit-groups (48-to-6bit-groups xor-bits))
           (S-boxes-output (apply-S-boxes 6bit-groups *S-boxes*)))
      (permute S-boxes-output))))

;
; In the following two functions, the 64bit block is arranged as following:
; (LeftBlock . RightBlock). Thus the left block is the car and the right block
; is the cdr of 64bit-block.

; key-bits is the 56 bit representation of the 64 bit key from which every 8th bit
; has already been discarded.

; Initially the block is passed through an initial permutation. Then for
; 16 rounds, the left half the block is XORed with the output of the
; feistel function (with the round key for that round) on the right half of the
; block and this becomes the next right half for the next round. The right half
; of this round becomes the left half of the next round. At the end, the output
; is passed through a final permutation (which is the inverse of the intial
; permutation) ad then output as the ciphertext.
;

(defun encrypt-decrypt-64bit-block1 (64bit-block key-bits iteration encrypt)
  (declare (xargs :measure (nfix(- 16 iteration))))
  (if (or (not (natp iteration))
          (not (booleanp encrypt)))
      nil
    (if (< iteration 16)
        (let* ((shifted-key-bits (get-round-key key-bits
                                                iteration
                                                encrypt))
               (subkey-iter (permuted-choice-2 shifted-key-bits))
               (feistel-output (feistel-fn (cdr 64bit-block)
                                           subkey-iter))
               (new-car (cdr 64bit-block))
               (new-cdr (xor-bit-list (car 64bit-block)
                                      feistel-output))
               (new-64bit-block (cons new-car
                                      new-cdr)))
          (encrypt-decrypt-64bit-block1 new-64bit-block
                                        shifted-key-bits
                                        (+ iteration 1)
                                        encrypt))
      (cons (cdr 64bit-block)
            (car 64bit-block)))))

(defun encrypt-decrypt-64bit-block (64bit-block key-bits encrypt)
  (if (or (not (64-bitp 64bit-block))
          (not (56-bitp key-bits))
          (not (booleanp encrypt)))
      nil
    (let* ((initial-permuted-bits (IP 64bit-block))
           (block-bits-proper (cons (prefix-nth initial-permuted-bits
                                                32)
                                    (get-nth initial-permuted-bits
                                             32)))
           (encrypted-before-final (encrypt-decrypt-64bit-block1 block-bits-proper
                                                                 key-bits
                                                                 0
                                                                 encrypt)))
      (IP-inverse (append (car encrypted-before-final)
                          (cdr encrypted-before-final))))))

;
; This method iterates through all the 64bit groups formed from the message and
; encrypts them by calling the encrypt-64bit-block method for each of them and
; finally constructing a hexadecimal list out of the output bits.
;

(defun DES-encrypt-decrypt (message-64bit-blocks key-56bit encrypt)
  (if (atom message-64bit-blocks)
      nil
    (append (encrypt-decrypt-64bit-block (car message-64bit-blocks)
						       key-56bit
						       encrypt)
	    (DES-encrypt-decrypt (cdr message-64bit-blocks)
				 key-56bit
				 encrypt))))

;
; The top level routine for the DES encryption of a string message with a
; string key. The message should be in multiples of 64bit in length while the
; key should be 64-bit in length. Also, the initial modification of the key
; (permuted-choice-1) is also done in this method, before sending to the next
; method.
;

(defun DES (message-bytes key-bytes encrypt)
  (if (not (booleanp encrypt))
      nil
    (let ((message-bits (bytes-to-8bits-msb message-bytes))
          (key-bits (bytes-to-8bits-msb key-bytes)))
      (if (or (not (64-bit-multiplep message-bits))
              (not (64-bitp key-bits)))
          nil
        (let* ((message-64bit-blocks (bits-to-64bit-blocks message-bits))
               (key-56bit (permuted-choice-1 key-bits)))
	  (bits-to-bytes (DES-encrypt-decrypt message-64bit-blocks
							 key-56bit
							 encrypt)))))))

;
; Test case for DES correctness: (equal (DES-dec (DES-enc (m k)) k) m)
;

(defconst *message-1*
  '(#x87 #x87 #x87 #x87 #x87 #x87 #x87 #x87))

(defconst *key-1*
  '(#x0E #x32 #x92 #x32 #xEA #x6D #x0D #x73))

(defconst *cipher-1*
  '(0 0 0 0 0 0 0 0))

(local
 (defthm example-single-des
   (and (equal (DES *message-1* *key-1* t)
               *cipher-1*)
        (equal (DES *cipher-1* *key-1* nil)
               *message-1*))))

;
; 3-DES is just DES applied 3 times to the same block of data using a key of
; length thrice the key length of DES (i.e 128 bits).
; (3-DES-enc m K) = (DES-enc (DES-dec (DES-enc m k1) k2) k3)
; (3-DES-dec m K) = (DES-dec (DES-enc (DES-dec m k1) k2) k3)
; when K = k1 | k2 | k3
;

(defun 3-DES (message-bytes key-bytes encrypt)
  (if (or (not (booleanp encrypt))
          (not (equal (len key-bytes) 24)))
      nil
    (DES (DES (DES message-bytes
                   (prefix-nth key-bytes 8)
                   encrypt)
              (prefix-nth (get-nth key-bytes 8)
                          8)
              (not encrypt))
         (get-nth key-bytes 16)
         encrypt)))

;
; 3-DES encryption of a message with k1 = k2 = k3 is the same as
; DES encryption of the message
;

(defconst *3-DES-key-1*
  (append (append *key-1* *key-1*)
          *key-1*))

(local
 (defthm example-triple-des
   (and (equal (3-DES *message-1* *3-DES-key-1* t)
               (DES *message-1* *key-1* t))
        (equal (3-DES *cipher-1* *3-DES-key-1* nil)
               (DES *cipher-1* *key-1* nil)))))




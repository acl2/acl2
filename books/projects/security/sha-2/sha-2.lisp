(in-package "ACL2")

(include-book "../util/byte-operations")

; (set-print-base 16 state)

;
; Constant to initialize the final hash. These values will be incremented
; after every iteration of a loop in Sha-main-loop. These are the first 32 bits
; of the fractional parts of the square roots of the first 8 primes 2..19.
;

(defconst *h*
  '(#x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19))

;
; Constants that are used in the main loop. These are the first 32 bits of the
; fractional parts of the cube roots of the first 64 primes 2..311
;

(defconst *k*
  '(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5 #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
    #xd807aa98 #x12835b01 #x243185be #x550c7dc3 #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
    #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
    #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7 #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
    #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13 #x650a7354 #x766a0abb #x81c2c92e #x92722c85
    #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3 #xd192e819 #xd6990624 #xf40e3585 #x106aa070
    #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5 #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
    #x748f82ee #x78a5636f #x84c87814 #x8cc70208 #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2))


;
; Method to append 1 followed by k zeros and the length of the message in 64
; bit format at the end of the message to create a block of 512 bits.
;

(defun append-one-and-k-zeros-and-len (message-bytes)
  (let* ((len (len message-bytes))
         (bitlen (+ 64                                ; 64 bit for the length
                    (+ 1                              ; 1 bit for the '1' that is appended
                       (* len 8))))                   ; length in bits
         (k (- (* (ceiling bitlen 512) 512) bitlen))  ; number of 0's to follow the '1'
         (num-to-append (expt 2 k))                   ; append '1' followed by k zeros
         (bytes-to-append (reverse (make-bytes num-to-append)))
         (message-bytes-appended (append message-bytes bytes-to-append))
         (len-bytes (reverse (make-bytes (* len 8))))
         (zero-padding (make-list-n 0 (- 8 (len len-bytes)))))
    (append message-bytes-appended (append zero-padding len-bytes))))

;
; Theorems about the append-one-and-k-zeros-and-len method.
; Theorem ideas provided by by David L. Rager.
;

;
; Theorem stating that in case of the empty string, the appended message
; length would be 64 bytes.
;

(defthm append-message-0bytes
  (implies (and (consp message-bytes)
		(equal (len message-bytes)
		       0))
	   (equal (len (append-one-and-k-zeros-and-len message-bytes))
		  64)))

;
; Theorem that states that all appended messages would have a length that is
; a multiple of 64 bytes.
; NOT PROVEN

;(defthm append-message-multiple-64
;  (implies (consp message-bytes)
;	   (equal (mod (len (append-one-and-k-zeros-and-len message-bytes))
;		       64)
;		  0)))

;
; A lemma that seems like should be helpful in admitting the theorems below
;

(defthm new-temp-lemma
  (implies (and (equal (len x) n1)
		(equal (len y) n2)
		(equal (len z) n3))
	   (equal (len (append (append x y) z))
		  (+ n1 n2 n3))))

;
; A hint to help us admit the following theorems, provided by
; David Rager.
;

(defthm help-lemma-for-append-55
  (implies (and (consp message-bytes)
		(equal (len message-bytes) 55))
	   (equal (len (append (append message-bytes '(128))
			       '(0 0 0 0 0 0 1 184)))
		  64))
  :hints (("Goal"
	   :use ((:instance new-temp-lemma
				   (x message-bytes)
				   (y '(128))
				   (z '(0 0 0 0 0 0 1 184))
				   (n1 (len message-bytes))
				   (n2 (len '(128)))
				   (n3 (len '(0 0 0 0 0 0 1 184)))))
	   :in-theory (disable new-temp-lemma))))

;
; Theorem stating that a message of 55 bytes would also have an appended length
; of 64 bytes.
;

(defthm append-message-55bytes
  (implies (and (consp message-bytes)
		(equal (len message-bytes)
	              55))
	   (equal (len (append-one-and-k-zeros-and-len message-bytes))
		  64)))

;
; A hint to help us admit the following theorem, on the same lines as h
;

(defthm help-lemma-for-append-56
  (IMPLIES (AND (CONSP MESSAGE-BYTES)
		(EQUAL (LEN MESSAGE-BYTES) 56))
	   (EQUAL (LEN (APPEND (APPEND MESSAGE-BYTES '(128 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
			       '(0 0 0 0 0 0 1 192)))
		  128))
  :hints (("Goal"
	   :use ((:instance new-temp-lemma
				   (x message-bytes)
				   (y '(128 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
				   (z '(0 0 0 0 0 0 1 192))
				   (n1 (len message-bytes))
				   (n2 (len '(128 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
				   (n3 (len '(0 0 0 0 0 0 1 192)))))
	   :in-theory (disable new-temp-lemma))))

;
; Theorem stating that a message of 56 bytes would have an appended length of
; 128 bytes - this is the first extreme case where the appended length is of
; 128 bytes.
;

(defthm append-message-56bytes
  (implies (and (consp message-bytes)
		(equal (len message-bytes)
	              56))
	   (equal (len (append-one-and-k-zeros-and-len message-bytes))
		  128)))

;
; A hint to help us admit the following theorem
;

(defthm help-lemma-for-append-119
  (implies (and (consp message-bytes)
		(equal (len message-bytes) 119))
	   (equal (len (append (append message-bytes '(128))
			       '(0 0 0 0 0 0 3 184)))
		  128))
  :hints (("Goal"
	   :use ((:instance new-temp-lemma
				   (x message-bytes)
				   (y '(128))
				   (z '(0 0 0 0 0 0 3 184))
				   (n1 (len message-bytes))
				   (n2 (len '(128)))
				   (n3 (len '(0 0 0 0 0 0 3 184)))))
	   :in-theory (disable new-temp-lemma))))

;
; Theorem stating that a message of 119 bytes would have an appended length of
; 128 bytes - this is the other extreme case.
;

(defthm append-message-119bytes
  (implies (and (consp message-bytes)
                (equal (len message-bytes)
                       119))
           (equal (len (append-one-and-k-zeros-and-len message-bytes))
                  128)))

;
; A couple of theorems to prove the correctness of append-one-and-k-zeros-and-len. This
; states that any message with 0 < size <= 55 results in an appended message of
; length 64 bytes and any message with 56 <= size <= 119 results in an appended
; message of length 128 bytes.
; NOT PROVEN

;; (defthm append-message-correct-64
;;   (implies (and (consp message-bytes)
;;                 (>= (len message-bytes) 0)
;;                 (<= (len message-bytes) 55))
;;            (equal (len (append-one-and-k-zeros-and-len message-bytes))
;;                   64)))

;; (defthm append-message-correct-128
;;   (implies (and (consp message-bytes)
;;                 (>= (len message-byte) 56)
;;                 (<= (len message-bytes) 119))
;;            (equal (len (append-one-and-k-zeros-and-len message-bytes))
;;                   128)))

;
; This method expands the sixteen 32-bit words into sixty-four 32-bit words:

;     for i from 16 to 63
;         s0 := (w[i-15] rightrotate 7) xor (w[i-15] rightrotate 18) xor (w[i-15] rightshift 3)
;         s1 := (w[i-2] rightrotate 17) xor (w[i-2] rightrotate 19) xor (w[i-2] rightshift 10)
;         w[i] := w[i-16] + s0 + w[i-7] + s1
;

(defun sha-expand-loop (message-blocks index end)
  (declare (xargs :measure (nfix (- end index))))
  (if (or (not (natp end))
	  (not (natp index))
          (> index end)
          (atom message-blocks))
      nil
      (let* ((s0 (xor-number (xor-number (rightrotate (Nth (- index 15)
                                                          message-blocks)
                                                     7)
                                        (rightrotate (Nth (- index 15)
                                                          message-blocks)
                                                     18))
                            (ash (Nth (- index 15)
                                      message-blocks)
                                 -3)))
            (s1 (xor-number (xor-number (rightrotate (Nth (- index 2)
                                                          message-blocks)
                                                     17)
                                        (rightrotate (Nth (- index 2)
                                                          message-blocks)
                                                     19))
                            (ash (Nth (- index 2)
                                      message-blocks)
                                 -10)))
            (new-message-blocks (append message-blocks
                                        (cons (add-32bit (add-32bit (Nth (- index 16)
                                                                         message-blocks)
                                                                    (Nth (- index 7)
                                                                         message-blocks))
                                                         (add-32bit s0 s1))
                                              nil))))
        (if (equal index end)
            new-message-blocks
          (sha-expand-loop new-message-blocks
                           (+ index 1)
                           end)))))

;
; Theorem that sha-expand-loop expands an array of 16 bytes to an
; array of 64 bytes.
; NOT PROVEN

;(defthm sha-expand-loop-64-bytes
;  (implies (and (consp message-blocks)
;		(equal (len message-blocks)
;		       16))
;	   (equal (len (sha-expand-loop message-blocks
;					 16
;					 63))
;		  64)))

; The implementation of the Main loop of Sha. Works based on the following algorithm:

;    Initialize hash value for this chunk:
;    a := h0 b := h1 c := h2 d := h3 e := h4 f := h5 g := h6 h := h7

;    Main loop:
;    for i from 0 to 63
;        S0 := (a rightrotate 2) xor (a rightrotate 13) xor (a rightrotate 22)
;        maj := (a and b) xor (a and c) xor (b and c)
;        t2 := S0 + maj
;        S1 := (e rightrotate 6) xor (e rightrotate 11) xor (e rightrotate 25)
;        ch := (e and f) xor ((not e) and g)
;        t1 := h + S1 + ch + k[i] + w[i]

;        h := g g := f f := e e := d + t1 d := c c := b b := a a := t1 + t2

;    Add this chunk's hash to result so far:
;    h0 := h0 + a h1 := h1 + b h2 := h2 + c h3 := h3 + d h4 := h4 + e
;    h5 := h5 + f h6 := h6 + g h7 := h7 + h


(defun sha-main-loop1(message-blocks-32 index a b c d e f g h h_arr)
  (if (atom message-blocks-32)
      nil
      (let* ((S0 (xor-number (xor-number (rightrotate a 2)
					 (rightrotate a 13))
			     (rightrotate a 22)))
	     (maj (xor-number (xor-number (and-number a b)
					  (and-number a c))
			      (and-number b c)))
	     (t2 (add-32bit S0 maj))
	     (S1 (xor-number (xor-number (rightrotate e 6)
					 (rightrotate e 11))
			     (rightrotate e 25)))
	     (ch (xor-number (and-number e f)
			     (and-number g
					 (not-number e))))
	     (t1 (add-32bit (add-32bit h S1)
                            (add-32bit ch
                                       (add-32bit (Nth index *k*)
                                                  (car message-blocks-32))))))
	(let* ((new_h g)
	       (new_g f)
	       (new_f e)
	       (new_e (add-32bit d t1))
	       (new_d c)
	       (new_c b)
	       (new_b a)
	       (new_a (add-32bit t1 t2)))
	  (if (null (cdr message-blocks-32))
	      (let* ((new_h_arr (update-nth 0
					    (add-32bit (Nth 0 h_arr)
                                                       new_a)
					    h_arr))
		     (new_h_arr (update-nth 1
					    (add-32bit (Nth 1 h_arr)
                                                       new_b)
					    new_h_arr))
		     (new_h_arr (update-nth 2
					    (add-32bit (Nth 2 h_arr)
                                                       new_c)
					    new_h_arr))
		     (new_h_arr (update-nth 3
					    (add-32bit (Nth 3 h_arr)
                                                       new_d)
					    new_h_arr))
		     (new_h_arr (update-nth 4
					    (add-32bit (Nth 4 h_arr)
                                                       new_e)
					    new_h_arr))
		     (new_h_arr (update-nth 5
					    (add-32bit (Nth 5 h_arr)
                                                       new_f)
					    new_h_arr))
		     (new_h_arr (update-nth 6
					    (add-32bit (Nth 6 h_arr)
                                                       new_g)
					    new_h_arr))
		     (new_h_arr (update-nth 7
					    (add-32bit (Nth 7 h_arr)
                                                       new_h)
					    new_h_arr)))
		new_h_arr)
	    (sha-main-loop1 (cdr message-blocks-32)
                            (+ index 1)
                            new_a new_b new_c new_d new_e new_f new_g new_h h_arr))))))

;
; This is the main loop of the Sha-2 encryption scheme, which initializes the
; values of a,b,c,d,e,f,g,h and calls the sha-main-loop1 method
;

(defun sha-main-loop (message-blocks-32 h_arr)
  (if (atom message-blocks-32)
      nil
      (let ((a (Nth 0 h_arr))
	    (b (Nth 1 h_arr))
	    (c (Nth 2 h_arr))
	    (d (Nth 3 h_arr))
	    (e (Nth 4 h_arr))
	    (f (Nth 5 h_arr))
	    (g (Nth 6 h_arr))
	    (h (Nth 7 h_arr)))
	(sha-main-loop1 message-blocks-32 0 a b c d e f g h h_arr))))

;
; This is the function which is called to expand the 16x32 bit blocks into
; 64x32 bit blocks and then it calls the main loop on the 64x32 bit list
;

(defun sha-loop (message-bytes h_arr)
  (sha-main-loop (sha-expand-loop (bytes-to-32bit-blocks message-bytes)      ;; Expands the bytes to blocks of 4 bytes
                                  16 63)                                      ;; Iterates from 16 to 63
                 h_arr))

;
; This method iterates over a list of lists of 64 bytes
; and calls sha-expand-loop.
;

(defun sha-encrypt1 (multiple-64-byte-blocks h_arr)
  (if (atom multiple-64-byte-blocks)
      nil
      (if (null (cdr multiple-64-byte-blocks))
          (sha-loop (car multiple-64-byte-blocks) h_arr)
          (let ((new_h_arr (sha-loop (car multiple-64-byte-blocks)
                                            h_arr)))
            (sha-encrypt1 (cdr multiple-64-byte-blocks)
                          new_h_arr)))))

;
; This method initializes the h_arr to the
; const *h* array and calls sha-encrypt1
;

(defun sha-encrypt (multiple-64-byte-blocks)
  (let ((h_arr *h*))
    (sha-encrypt1 multiple-64-byte-blocks h_arr)))

;
; The top level Sha-2 method that works on a string S. It converts the string
; to bytes, appends 1 and k zeros and the 64-bit length to the message (makes
; it multiple of 512 bits). Then it splits the resulting list of bytes into a
; list of 64 byte (512 bits) lists.
;

(defun sha-2 (S)
  (if (not (stringp S))
      nil
      (let* ((message-bytes (string-to-bytes S))
             (appended-bytes (append-one-and-k-zeros-and-len message-bytes))
             (multiple-64-byte-blocks (bytes-to-multiple-64-byte-blocks appended-bytes)))
        (sha-encrypt multiple-64-byte-blocks))))

;
; A few test cases from known Sha-256 values (source: wikipedia article on Sha-2)
;

(defthm sha-256-test-case-1
  (equal (sha-2 "")
	 '(#xe3b0c442 #x98fc1c14 #x9afbf4c8 #x996fb924
		      #x27ae41e4 #x649b934c #xa495991b #x7852b855)))

(defthm sha-256-test-case-2
  (equal (sha-2 "The quick brown fox jumps over the lazy dog")
	 '(#xd7a8fbb3 #x07d78094 #x69ca9abc #xb0082e4f
		      #x8d5651e4 #x6d3cdb76 #x2d02d0bf #x37c9e592)))

(defthm sha-256-test-case-3
  (equal (sha-2 "The quick brown fox jumps over the lazy dog.")
	 '(#xef537f25 #xc895bfa7 #x82526529 #xa9b63d97
		      #xaa631564 #xd5d789c2 #xb765448c #x8635fb6c)))



(in-package "ACL2")
; cert_param: (non-acl2r)
(include-book "arithmetic-5/top" :dir :system)
;
; Converts a list of characters to bytes
;

(defun charlist-to-bytes(charlist)
  (if (atom charlist)
      nil
      (cons (char-code (car charlist))
	    (charlist-to-bytes(cdr charlist)))))

;
; Converts an entire string into a list of bytes
;

(defun string-to-bytes(S)
  (charlist-to-bytes(coerce S 'LIST)))

;
; Theorem asserting that the length of the string is essentially same as the
; length of the list of bytes representing it.
;
(defthm coerce-produces-chars
  (implies (stringp S)
           (character-listp (coerce S 'LIST))))

(defthm num-chars-equals-num-bytes
  (implies (character-listp cl)
           (equal (len cl)
                  (len
                   (charlist-to-bytes cl)))))

;
; This does not go through unless I include (> (len S) 0)
;
;(defthm string-length-equals-num-bytes
;  (implies (stringp S)
;           (equal (len S)
;                  (len (string-to-bytes S)))))

;
; Converts a large integer into a list of bytes (little-endian)
;

(defun make-bytes(number-int)
  (declare (xargs :guard (natp number-int)))
  (if (< number-int 256)
      (cons number-int nil)
      (cons (mod number-int 256)
            (make-bytes (ash number-int -8)))))


(defun make-bytes-msb(number-int)
  (declare (xargs :guard (natp number-int)))
  (reverse (make-bytes number-int)))

;
; This method constructs a list consisting of length x and consisting of only
; the item n repeated x times.
;

(defun make-list-n (n x)
  (if (or (zp x)
          (not (atom n)))
      nil
      (cons n (make-list-n n (- x 1)))))


(defthm length-x-make-list-n
  (implies (and (natp x)
                (natp n))
           (equal (len (make-list-n n x))
                  x)))

;
; Verifies if the input is a bit (0 or 1)
;

; Deleted by Matt K. on 6/10/2013 because bitp is defined in
; ihs/basic-definitions.lisp, which is now included under centaur/gl/gl.lisp,
; and both the latter book and this one are included in ../des/des.lisp
; (defun bitp(e)
;   (if (consp e)
;       nil
;       (or (equal e 0)
;           (equal e 1))))
; So here is the definition from ihs/basic-definitions.lisp:

;; [Jared] changing this to just include the basic-definitions book from IHS.
;; It's very lightweight, and this way we don't duplicate the definition and
;; have to maintain it in two places.

(include-book "ihs/basic-definitions" :dir :system)

;
; Computes the logical XOR of two single bits
;

(defun xor-bit(x y)
  (if (and (atom x)
           (atom y)
           (bitp x)
           (bitp y))
      (if (equal x y)
          0
          1)
      nil))

;
; Computes the logical AND of two single bits
;

(defun and-bit(x y)
  (if (and (atom x)
           (atom y)
           (bitp x)
           (bitp y))
      (if (equal x y)
	  x
          0)
      nil))

;
; Computes the complement of a single bit
;

(defun not-bit(x)
  (if (and (atom x)
           (bitp x))
      (if (equal x 1)
	  0
          1)
      nil))

;
; This method verifies if the input is a bit-list
;

(defun bit-listp(x)
  (if (atom x)
      nil
      (if (null (cdr x))
          (bitp (car x))
          (and (bitp (car x))
               (bit-listp (cdr x))))))


;
; n-bitp is a generic method that verifies if a list has n bits
; The other methods are just wrappers that are used for better readability of
; the code, and therefore directly call n-bitp.
;

(defun n-bitp(x-bits n)
  (and (bit-listp x-bits)
       (equal (len x-bits)
              n)))

(defun 64-bitp(x-bits)
  (n-bitp x-bits 64))

(defun 56-bitp(x-bits)
  (n-bitp x-bits 56))

(defun 48-bitp(x-bits)
  (n-bitp x-bits 48))

(defun 32-bitp(x-bits)
  (n-bitp x-bits 32))

(defun 28-bitp(x-bits)
  (n-bitp x-bits 28))

(defun 8-bitp(x-bits)
  (n-bitp x-bits 8))

(defun 6-bitp(x-bits)
  (n-bitp x-bits 6))

;
; This methods verifies if the bit-list being provided to it has a length that
; is a multiple of 64.
;

(defun 64-bit-multiplep(x-bits)
  (and (bit-listp x-bits)
       (equal 0
              (mod (len x-bits)
                   64))))

(defun 8-bit-multiplep(x-bits)
  (and (bit-listp x-bits)
       (equal 0
	      (mod (len x-bits)
		   8))))


;
; This method computes a logical compliment of two bit lists
;

(defun not-bit-list(x)
  (if (bit-listp x)
      (cons (not-bit (car x))
            (not-bit-list (cdr x)))
      nil))

;
; Correctness for not-bit
;
(defthm not-not-bit
  (implies (bitp x)
           (equal (not-bit (not-bit x))
                  x)))

;
; Correctness theorem for not-bit-list
;
(defthm not-not-bit-list
  (implies (bit-listp x)
           (equal (not-bit-list (not-bit-list x))
                  x)))

;
; This method computes a logical AND of two bit lists
;

(defun and-bit-list(x y)
  (if (and (bit-listp x)
           (bit-listp y))
      (cons (and-bit (car x) (car y))
            (and-bit-list (cdr x) (cdr y)))
      nil))


;
; Correctness theorem for and-bit
;
(defthm and-bit-correct
  (implies (and (bitp x)
                (bitp y))
           (and (equal (and-bit x y)
                       (and-bit y x))
                (equal (and-bit x x)
                       x)
                (equal (and-bit y y)
                       y))))

;
; Correctness theorem for and-bit-list
;
(defthm and-bit-list-correct
  (implies (and (bit-listp x)
                (bit-listp y))
           (and (equal (and-bit-list x y)
                       (and-bit-list y x))
                (equal (and-bit-list x x)
                       x)
                (equal (and-bit-list y y)
                       y))))

;
; This method computes a logical XOR of two bit lists
;

(defun xor-bit-list(x y)
  (if (atom x)
      (if (bit-listp y)
          y
          nil)
      (if (atom y)
          (if (bit-listp x)
              x
              nil)
          (cons (xor-bit (car x) (car y))
                (xor-bit-list (cdr x) (cdr y))))))

;
; Correctness theorem for xor-bit
;
(defthm xor-bit-correct
  (implies (and (bitp x)
                (bitp y))
           (and (equal (xor-bit x y)
                  (xor-bit y x))
                (equal (xor-bit x x)
                       0)
                (equal (xor-bit y y)
                       0))))

;
; Correctness theorem for xor-bit-list
; NOT YET PROVED
;
;(defthm xor-bit-list-correct
;  (implies (and (bit-listp x)
;                (bit-listp y))
;           (and (equal (xor-bit-list x y)
;                       (xor-bit-list y x))
;                (equal (bits-to-number (xor-bit-list x x))
;                       0)
;                (equal (bits-to-number (xor-bit-list y y))
;                       0))))

;
; This method is the reverse of bits-to-number and computes
; bit list out of a number.
;

(defun number-to-bits(x)
  (if (not (natp x))
      nil
      (if (< x 2)
          (cons x nil)
          (cons (mod x 2) (number-to-bits (floor x 2))))))


(defun number-to-32bits(x)
  (if (not (natp x))
      nil
      (let* ((bit-list (number-to-bits x))
             (len-list (len bit-list)))
        (append bit-list
                (make-list-n 0
                             (- 32 len-list))))))

(defun number-to-8bits(x)
  (if (or (not (natp x))
          (> x 255))
      nil
      (let* ((bit-list (number-to-bits x))
             (len-list (len bit-list)))
        (append bit-list
                (make-list-n 0
                             (- 8 len-list))))))

(defun number-to-4bits(x)
  (if (or (not (natp x))
          (> x 15))
      nil
      (let* ((bit-list (number-to-bits x))
             (len-list (len bit-list)))
        (append bit-list
                (make-list-n 0
                             (- 4 len-list))))))

(defun number-to-4bits-msb(x)
  (reverse (number-to-4bits x)))
;
; Method to convert a list of bytes to bits using the number-to-bits method
;

(defun bytes-to-8bits-msb(bytes)
  (if (atom bytes)
      nil
    (append (reverse (number-to-8bits (car bytes)))
            (bytes-to-8bits-msb (cdr bytes)))))

;
; Method to convert a string to bits using the number-to-bits method
;

(defun string-to-bits-msb(S)
  (if (not (stringp S))
      nil
    (let ((bytes (string-to-bytes S)))
      (bytes-to-8bits-msb bytes))))

;
; This method is the reverse of number-to-bits and computes
; the decimal equivalent of a bit list.
;

(defun bits-to-number1(x exp)
  (if (not (bit-listp x))
      nil
      (let ((val (* (car x)
                    (expt 2 exp))))
        (if (null (cdr x))
            val
            (+ val
               (bits-to-number1 (cdr x)
                            (+ 1 exp)))))))


(defun bits-to-number(x)
  (bits-to-number1 x 0))

;
; Theorem to prove correctness of number-to-bits and bits-to-number
; NOT PROVED YET
;
;(defthm bits-number-correct
;  (implies (natp x)
;           (equal (bits-to-number (number-to-bits x))
;                  x)))

;
; A method that computes the logical-XOR of two numbers
; In our case these will be two 32-bit numbers
;

(defun xor-number(x y)
  (bits-to-number (xor-bit-list (number-to-32bits x)
                                (number-to-32bits y))))

;
; A method that computes the logical-AND of two numbers
; In our case these will be two 32-bit numbers
;

(defun and-number(x y)
  (bits-to-number (and-bit-list (number-to-32bits x)
                                (number-to-32bits y))))

;
; A method that converts a number into its bit complement
; In our case this will be a 32-bit number
;

(defun not-number(x)
  (bits-to-number (not-bit-list (number-to-32bits x))))

;
; Method for getting a list out of the remaining items
; after removing the first n items
;

(defun get-nth(x n)
  (if (< n 0)
      nil
     (if (atom x)
         nil
         (if (= n 0)
             x
             (get-nth (cdr x)
                      (- n 1))))))

;
; Correctness of get-nth
;
(defthm get-nth-correct
  (implies (and (natp n)
                (consp x)
                (> (len x)
                   n))
           (equal (+ n (len (get-nth x n)))
                  (len x))))

;
; Method for getting a list out of the first n items from
; a list of items.
;

(defun prefix-nth(x n)
  (if (<= n 0)
      nil
      (if (atom x)
          nil
          (cons (car x)
                (prefix-nth (cdr x)
                            (- n 1))))))

;
; Correctness of prefix-nth
;
(defthm prefix-nth-correct
  (implies (and (natp n)
                (consp x)
                (> (len x)
                   n))
           (equal (len (prefix-nth x n))
                  n)))

;
; Correctness of get-nth and prefix-nth
;

(defthm get-nth-prefix-correct
  (implies (and (natp n)
                (consp x)
                (< n
                   (len x)))
           (and (equal (append (prefix-nth x n)
                             (get-nth x n))
                       x)
                (equal (len (append (prefix-nth x n)
                                  (get-nth x n)))
                       (len x)))))


;
; Following methods deal with converting a list of large bits
; (with 8bit boundaries) into a string.
;

;
; This method takes in 8 bits and converts it into a byte
;

(defun 8bits-to-byte (x)
  (if (not (8-bitp x))
      nil
    (+ (* (Nth 0 x) 128)
       (* (Nth 1 x) 64)
       (* (Nth 2 x) 32)
       (* (Nth 3 x) 16)
       (* (Nth 4 x) 8)
       (* (Nth 5 x) 4)
       (* (Nth 6 x) 2)
       (* (Nth 7 x) 1))))



;
; Lemma to help acl2 admit the following method
; and another method at the end of the file
;
(defthm get-nth-posp-reduces-length
  (implies (and (consp message)
                (posp n))
           (< (len (get-nth message n))
              (len message))))

;
; This method takes a list of bits and groups them into smaller
; inner lists of 8 bits each.
;

(defun bits-to-8bits (x)
  (declare (xargs :measure (len x)))
  (if (atom x)
      nil
    (if (<= (len x) 8)
	(cons x nil)
      (cons (prefix-nth x 8)
	    (bits-to-8bits (get-nth x 8))))))

;
; This method takes a list of 8bit groups and converts this list into
; a list of bytes
;

(defun 8bits-to-bytes (x)
  (if (atom x)
      nil
    (cons (8bits-to-byte (car x))
	  (8bits-to-bytes (cdr x)))))

;
; A method to convert a list of bits to bytes
;
(defun bits-to-bytes (x)
  (if (atom x)
      nil
    (8bits-to-bytes (bits-to-8bits x))))

;
; A method which converts each byte in a list into a character using the
; built in code-char function
;

(defun bytes-to-charlist (x)
  (if (atom x)
      nil
    (cons (code-char (car x))
	  (bytes-to-charlist (cdr x)))))

;
; An uber level function that converts a bigendian list of bits (multiple
; of 8 bits) to a string by first converting them into groups of 8, converting
; these groups into bytes, converting these bytes into characters and then
; using coerce to force this character list to a string.
;

(defun bigendian-bits-to-string (x)
  (if (not (8-bit-multiplep x))
      nil
    (let* ((8bit-groups (bits-to-8bits x))
	  (bytes (8bits-to-bytes 8bit-groups))
	  (charlist (bytes-to-charlist bytes)))
      (coerce charlist 'string))))

;
; This method rotates a list of bits to the right by n bits
; This is called by rightrotate, after converting a number to bits
;

(defun rightrotate-bits (bit-list n)
  (if (< n 0)
      nil
      (if (atom bit-list)
          nil
          (append (get-nth bit-list n)
                  (prefix-nth bit-list n)))))

;
; David Rager's Lemma - this is required to admit the below theorem.
;
(defthm get-nth-lemma-rotate
  (implies (true-listp x)
           (equal (get-nth x
                           (len x))
                  nil)))

;
; Correctness of rightrotate
;

(defthm rightrotate-bits-correct
  (implies (true-listp x)
           (equal (rightrotate-bits x (len x))
                  x)))

;
; This method rotates a number to the right by n bits
; The number here is a decimal representation of a 32bit integer
;

(defun rightrotate(number n)
  (let ((bit-list (number-to-32bits number)))
    (bits-to-number (rightrotate-bits bit-list n))))

;
; Addition modulo (expt 2 32)
;
(defun add-32bit (x y)
  (if (and (natp x)
           (natp y))
      (mod (+ x y)
           (expt 2 32))
      nil))

;
; This method converts a list of bytes and converts it to 32bit numbers
;

(defun bytes-to-32bit-blocks1(byte-list currval m)
  (if (atom byte-list)
      nil
      (let ((val (+ (* currval 256)
                    (car byte-list))))
        (if (null (cdr byte-list))
            (cons val nil)
            (if (equal 1 m)
                (cons val (bytes-to-32bit-blocks1 (cdr byte-list)
                                                  0 4))
                (bytes-to-32bit-blocks1 (cdr byte-list) val (- m 1)))))))

(defun bytes-to-32bit-blocks(byte-list)
  (bytes-to-32bit-blocks1 byte-list 0 4))


;
; This routine splits a list of bytes into a list of lists
; which contain 64 bytes each = 512 bits.
;

(defun bytes-to-multiple-64-byte-blocks (message-bytes)
  (declare (xargs :measure (len message-bytes)))
  (if (atom message-bytes)
      nil
      (if (<= (len message-bytes) 64)
          (cons message-bytes nil)
          (cons (prefix-nth message-bytes 64)
                (bytes-to-multiple-64-byte-blocks (get-nth message-bytes 64))))))


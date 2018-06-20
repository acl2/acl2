; From Jun Sawada, July 2005.

;; Book for Radix conversion
;; Main functions that are defined in this books are:
;;  (int2hex x len)
;;      Converting a signed integer to a hexadecimal string of length len.
;;      It includes uppercase letters from A to F in the resulting string.
;;  (nat2hex x)
;;      Converting a natural number to a hexadecimal string
;;      It includes uppercase letters from A to F in the resulting string.
;;  (int2oct x len)
;;      Converting a signed integer to a octagonal string of length len.
;;  (nat2oct x)
;;      Converting a signed integer to a octagonal string.
;;  (int2bin x len)
;;      Converting a signed integer to a binary string of length len.
;;  (nat2bin x)
;;      Converting a natural number to a binary string.
;;  (int2digits x len base)
;;      Converting a signed integer to a string of digits of length len.
;;      Base is used for the conversion.
;;  (nat2digits x base)
;;      Converting a natural number to a string of digits, using base
;;      for the conversion.
(in-package "RADIX")
;; These books are included to prove some guards.
(local (include-book "arithmetic-3/bind-free/top" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

;; Returns the maximum integer that is not larger than the log of x with base,
;; In TeX format, $\lfloor\log_{base}(x)\rfloor$.
;; Thus (ilog 10 3) = 2
(defun ilog (x base)
  (declare (xargs :guard (and (natp x) (natp base) (<= 2 base))))
  (if (or (zp x) (zp base) (< base 2))  0
    (if (< x base) 0
      (1+ (ilog (floor x base) base)))))

(defun hex-digit (n cap)
  (declare (xargs :guard (and (natp n) (<= 0 n) (< n 16) (booleanp cap))))
  (if (< n 10)
      (digit-to-char n)
    (if cap
	(code-char (+ n -10 (char-code #\A)))
      (code-char (+ n -10 (char-code #\a))))))

(defun int2hex-lst (x len cap ans)
  (declare (xargs :guard (and (integerp x) (natp len) (booleanp cap)
			      (listp ans))))
  (if (zp len)
      ans
    (int2hex-lst (floor x 16) (1- len) cap
		 (cons (hex-digit (mod x 16) cap) ans))))


(defthm character-listp-int2hex-lst
  (implies (character-listp ans)
	   (character-listp (int2hex-lst x len cap ans))))

; (int2hex x len cap) converts an integer x to a hexadecimal
; string of length len. If cap is non-nil, it uses ABCDEF as opposed to
; abcdef.
(defun int2hex (x len cap)
  (declare (xargs :guard (and (integerp x) (natp len) (booleanp cap))))
  (coerce (int2hex-lst x len cap nil) 'string))


; Returns how many characters of hex-digits are needed to print natural
; number x.
(defun hex-print-size (x)
  (declare (xargs :guard (natp x)))
  (1+ (ilog x 16)))


; (nat2hex x cap) converts natural number x to a hexadecimal string.
; If cap is non-nil, ABCDEF are used in the hexadecimal representation.
(defun nat2hex (x cap)
  (declare (xargs :guard (and (booleanp cap) (natp x))))
  (int2hex x (hex-print-size x) cap))


(defun convert-radix-lst (x len base ans)
  (declare (xargs :guard (and (integerp x) (natp len)
			      (natp base) (<= 2 base) (<= base 10))))
  (if (zp len)
      ans
    (convert-radix-lst (floor x base) (1- len) base
		       (cons (digit-to-char (mod x base)) ans))))

(defthm character-listp-convert-radix-lst
  (implies (character-listp ans)
	   (character-listp (convert-radix-lst x len base ans))))

; (convert-radix x n r) converts an integer x to a digit-string of length n,
; using radix r. For example (convert-radix x 32 2) converts x to
; binary string of length 32.
(defun convert-int-radix (x n r)
  (declare (xargs :guard (and (integerp x) (natp n)
			      (natp r) (<= 2 r) (<= r 10))))
  (coerce (convert-radix-lst x n r nil) 'string))

; Returns how many digits are needed to represent natural number x
; using radix 'base'.
(defun radix-print-size (x base)
  (declare (xargs :guard (and (natp x) (natp base) (<= 2 base))))
  (1+ (ilog x base)))


; (nat2hex x cap) converts positive integer x to a hexadecimal string.
; If cap is non-nil, ABCDEF are used in the hexadecimal representation.
; Should convert-base be a better name?
(defun convert-nat-radix (x r)
  (declare (xargs :guard (and (natp x) (natp r) (<= 2 r) (<= r 10))))
  (convert-int-radix x (radix-print-size x r) r))


(defun nat2bin (x)
  (convert-nat-radix x 2))

(defun nat2oct (x)
  (convert-nat-radix x 8))

(defun int2bin (x len)
  (convert-int-radix x len 2))

(defun int2oct (x len)
  (convert-int-radix x len 8))

;; Following are examples to format the converted numbers.
;;
;;(fmx "~%hex of x is ~x0~%" (radix::int2hex 100 (radix::hex-print-size 100) t))
;;
;; Macro to print a non-negative integer in hex.
;(defmacro hexprint+ (x)
;  `(fmx "~%~@0~%" (radix::nat2hex ,x T)))

;; Print an integer in hex assuming that it is 32-bit word.
;(defmacro hexprintw (x)
;  `(fmx "~%~@0~%" (radix::int2hex ,x 8 T)))

;;; Print an integer in hex assuming that is is 64 bit word (quad-word).
;(defmacro hexprintq (x)
;  `(fmx "~%~@0~%" (radix::int2hex ,x 16 T)))

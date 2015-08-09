; Section 10.5 Binary Adder and Multiplier

(in-package "ACL2")
; Binary Addition and Multiplication with Bit Vectors

(defun band (p q) (if p (if q t nil) nil))
(defun bor  (p q) (if p t (if q t nil)))
(defun bxor (p q) (if p (if q nil t) (if q t nil)))

(defun bmaj (p q c)
  (bor (band p q)
       (bor (band p c)
            (band q c))))

(defun full-adder (p q c)
  (mv (bxor p (bxor q c))
      (bmaj p q c)))

(defun serial-adder (x y c)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (endp x) (endp y))
      (list c)
    (mv-let (sum cout)
	    (full-adder (car x) (car y) c)
	    (cons sum (serial-adder (cdr x) (cdr y) cout)))))

;     11  (3)
;   1100 (12)
; +    1  (1)
; ------
;  10000 (16)

; (serial-adder '(t t nil) '(nil nil t t) t)

(defun n (v)
  (cond ((endp v) 0)
        ((car v) (+ 1 (* 2 (n (cdr v)))))
        (t (* 2 (n (cdr v))))))

; (n (serial-adder '(t t nil) '(nil nil t t) t))

(defthm serial-adder-correct-nil-nil
  (equal (n (serial-adder x nil nil))
         (n x)))

(defthm serial-adder-correct-nil-t
  (equal (n (serial-adder x nil t))
	 (+ 1 (n x))))

(defthm serial-adder-correct
  (equal (n (serial-adder x y c))
         (+ (n x) (n y) (if c 1 0))))


(defun multiplier (x y p)
  (if (endp x)
      p
    (multiplier (cdr x)
		(cons nil y)
		(if (car x)
		    (serial-adder y p nil)
		  p))))

;      1001      (9)
;    x 1010   x (10)
;    ------   ------
;     10010     (90)
;   1001000
; ---------
;   1011010

; (multiplier '(t nil nil t) '(nil t nil t) nil)
; (n (multiplier '(t nil nil t) '(nil t nil t) nil))

(defthm complete-*
  (equal (* y (* x z))
	 (* x (* y z)))
  :hints (("Goal"
	   :use ((:instance associativity-of-* (y x) (x y))
		 (:instance associativity-of-*))
	   :in-theory (disable associativity-of-*))))

(defthm multiplier-correct
  (equal (n (multiplier x y p))
         (+ (* (n x) (n y)) (n p))))

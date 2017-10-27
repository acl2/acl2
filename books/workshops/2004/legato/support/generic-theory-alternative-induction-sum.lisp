(in-package "ACL2")
(include-book "../../../../arithmetic-3/bind-free/top")
(include-book "../../../../arithmetic-3/floor-mod/floor-mod")
(include-book "generic-theories")

;;; The following program sums the integers from 1 to N on the early Mostek
;;; 6502 microprocessor.  A is an 8-bit wide accumulator. N is a single byte
;;; of data in memory.  C is a carry flag.  We prove that the limited (8-bit)
;;; precision computation delivers the correct result, provided N*(N+1)/2
;;; is less than 256 and N is greater than 0.

;;;       LDA #0     ; load A immediate with the constant 0
;;;       CLC        ; clear the carry flag
;;; LOOP  ADC N      ; add with carry N to A
;;;       DEC N      ; decrement N
;;;       BNE LOOP   ; branch if N is non-zero to LOOP

;;; Provide semantics for the 6502 DEC instruction.

(defun dec (x)
  (if (zp x)
      255
    (1- x)))

;;; Mechanically derived weakest precondition at location LOOP

(defun wp-loop (n a c ns)
  (declare (xargs :measure (dec n)))
  (if (equal (dec n) 0)
      (equal (mod (+ c (+ a n)) 256)
             (floor (* ns (1+ ns)) 2))
    (wp-loop (dec n)
             (mod (+ c (+ a n)) 256)
             (floor (+ c (+ a n)) 256)
             ns)))

;;; Weakest precondition at beginning of program

(defun wp-1 (n ns)
  (wp-loop n 0 0 ns))

;;; Represent state as a list.

(defun n (s) (car s))
(defun a (s) (cadr s))
(defun c (s) (caddr s))
(defun ns(s) (cadddr s))

;;; Instantiate the theory for the alternative induction that decrements
;;; NS by 1 and A by NS.  This choice is motivated by leaving q1
;;; invariant and commuting with sigma1.

(defthm wp-loop-fn1-as-fn2
  (implies (and (not (zp n))
                (not (zp ns))
                (equal c 0)
                (< (+ a (floor (* n (+ 1 n)) 2)) 256)
                (natp a)
                (<= ns a))
           (equal (wp-loop n a c ns)
                  (wp-loop n (- a ns) c (+ -1 ns))))
  :hints
  (("Goal"
    :use
    (:instance
     (:functional-instance
      fn1-as-fn2
      (fn1 (lambda (s) (wp-loop (n s) (a s) (c s) (ns s))))
      (fn2 (lambda (s) (wp-loop (n s) (a s) (c s) (ns s))))
      (b1 (lambda (s) (equal (dec (n s)) 0)))
      (b2 (lambda (s) (equal (dec (n s)) 0)))
      (q1 (lambda (s) (equal (mod (+ (c s) (a s) (n s)) 256)
                             (floor (* (ns s) (+ 1 (ns s))) 2))))
      (q2 (lambda (s) (equal (mod (+ (c s) (a s) (n s)) 256)
                             (floor (* (ns s) (+ 1 (ns s))) 2))))
      (sigma1 (lambda (s)
                (list (dec (n s))
                      (mod (+ (c s) (a s) (n s)) 256)
                      (floor (+ (c s) (a s) (n s)) 256)
                      (ns s))))
      (sigma2 (lambda (s)
                (list (dec (n s))
                      (mod (+ (c s) (a s) (n s)) 256)
                      (floor (+ (c s) (a s) (n s)) 256)
                      (ns s))))
      (p (lambda (s)
           (and (not (zp (n s)))
                (not (zp (ns s)))
                (< (+ (a s) (floor (* (n s) (+ 1 (n s))) 2)) 256)
                (natp (a s))
                (<= (ns s) (a s))
                (equal (c s) 0))))
      (id-alt (lambda (s)
                (list (n s)
                      (- (a s) (ns s))
                      (c s)
                      (+ -1 (ns s)))))
      (measure1 (lambda (s) (if (zp (n s)) 256 (n s)))))
     (s (list n a c ns))))))

;;; Program correctness result

(defthm wp-loop-is-correct
  (implies (and (< (floor (* n (+ 1 n)) 2) 256)
                (not (zp n))
                (equal ns n))
           (wp-1 n ns)))

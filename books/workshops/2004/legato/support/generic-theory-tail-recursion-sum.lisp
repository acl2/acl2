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

;;; Represent the "a" component directly and "s" by a list.

(defun n (s) (car s))
(defun c (s) (cadr s))
(defun ns (s) (caddr s))

;;; Define the instantiation of h from the generic theory.

(defun wp-loop-h (s)
  (declare (xargs :measure (dec (n s))))
  (if (equal (dec (n s)) 0)
      0
    (+ (n s) (wp-loop-h (list (dec (n s)) (c s) (ns s))))))

;;;; Instantiate the generic theory

(defthm wp-loop-g=h
  (implies (and (not (zp n))
                (natp ns)
                (natp a)
                (equal c 0)
                (< (+ a (floor (* n (+ 1 n)) 2)) 256))
           (equal (wp-loop n a c ns)
                  (if (equal (dec n) 0)
                      (equal (mod (+ a n) 256)
                             (floor (* ns (+ 1 ns)) 2))
                    (equal (mod (+ 1 a (wp-loop-h (list n c ns))) 256)
                           (floor (* ns (+ 1 ns)) 2)))))
  :hints
  (("Goal"
    :use
    (:instance
     (:functional-instance
      g=h
      (bb (lambda (s) (equal (dec (n s)) 0)))
      (qt (lambda (a s) (equal (mod (+ a (n s)) 256)
                               (floor (* (ns s) (+ 1 (ns s))) 2))))
      (g (lambda (a s) (wp-loop (n s) a (c s) (ns s))))
      (measure-g (lambda (s) (dec (n s))))
      (tau (lambda (s) (list (dec (n s)) (c s) (ns s))))
      (rho (lambda (a s) (mod (+ a (c s) (n s)) 256)))
      (rhoh (lambda (a s) (+ a (n s))))
      (h (lambda (s) (wp-loop-h s)))
      (rt (lambda (a s) (and (not (zp (n s)))
                             (natp (ns s))
                             (natp a)
                             (equal (c s) 0)
                             (< (+ a (floor (* (n s) (+ 1 (n s))) 2)) 256))))
      (id (lambda () 0))
      (op (lambda (a x s) (if (equal (dec (n s)) 0)
                              a
                            (+ a x))))
      (hs (lambda (s) (if (equal (dec (n s)) 0)
                          s
                        (list 1 (c s) (ns s))))))
     (s (list n c ns))))))

;;; Derive a closed form expression for wp-loop-h.

(defthm wp-loop-h-closed
  (implies (not (zp (n s)))
           (equal (wp-loop-h s)
                  (+ -1 (floor (* (n s) (+ 1 (n s))) 2))))
  :hints
  (("Goal"
    :in-theory (disable prefer-positive-addends-equal))))

;;; Program correctness result

(defthm wp-loop-is-correct
  (implies (and (not (zp n))
                (equal ns n)
                (< (floor (* n (+ 1 n)) 2) 256))
           (wp-1 n ns)))

(in-package "ACL2")
(include-book "../../../../arithmetic-3/bind-free/top")
(include-book "../../../../arithmetic-3/floor-mod/floor-mod")
(include-book "generic-theories")

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

;;; The following is a Floyd-Hoare correctness specification for the multiply
;;; program.
;;;
;;;      { F1=F1SAVE ^ F1<256 ^ F2<256 ^ LOW<256 }
;;;
;;;         LDX #8     load the X register immediate with the value 8
;;;         LDA #0     load the A register immediate with the value 0
;;; LOOP    ROR F1     rotate F1 right circular through the carry flag
;;;         BCC ZCOEF  branch on carry flag clear to ZCOEF
;;;         CLC        clear the carry flag
;;;         ADC F2     add with carry F2 to the contents of A
;;; ZCOEF   ROR A      rotate A right circular through the carry flag
;;;         ROR LOW    rotate LOW right circular through the carry flag
;;;         DEX        decrement the X register by 1
;;;         BNE LOOP   branch if X is non-zero to LOOP
;;;
;;;      { LOW + 256*A = F1SAVE*F2 }

;;; Provide semantics for the Mostek 6502 DEX instruction.  The semantics of
;;; the remaining functions are built into the weakest precondition generation
;;; program.

(defun dec (x)
  (if (zp x)
      255
    (1- x)))

;;; This is a mechanically derived.weakest precondition at location ZCOEF.

(defun wp-zcoef (f1 x c low a f1save f2)
  (declare (xargs :measure (dec x)))
  (if (equal (dec x) 0)
      (equal
       (+ (* (+ (* 128 c) (floor a 2)) 256)
          (+ (* 128 (mod a 2))
             (floor low 2)))
       (* f1save f2))
    (wp-zcoef
     (+ (* 128 (mod low 2))
        (floor f1 2))
     (dec x)
     (*
      (mod f1 2)
      (floor
       (+ (+ (* 128 c) (floor a 2)) f2)
       256))
     (+ (* 128 (mod a 2))
        (floor low 2))
     (if (equal (mod f1 2) 0)
         (+ (* 128 c) (floor a 2))
       (mod
        (+ (+ (* 128 c) (floor a 2))
           f2)
        256))
     f1save
     f2)))

;;; This is the weakest precondition at the beginning of the program.

(defun wp-zcoef-1 (f1 c low f2)
  (wp-zcoef
   (+ (* 128 c) (floor f1 2))
   8
   0
   low
   (* (mod f1 2) f2)
   f1
   f2))

;;; Generalize wp-zcoef to capture properties of the constants 128 and 256.

(defun wp-zcoef-g (f1 x c low a result f2 i)
  (declare (xargs :measure (dec x)))
  (if (equal (dec x) 0)
      (equal
       (+ (* (+ (* (expt 2 (1- i)) c) (floor a 2)) (expt 2 i))
          (+ (* (expt 2 (1- i)) (mod a 2))
             (floor low 2)))
       result)
    (wp-zcoef-g
     (+ (* (expt 2 (1- i)) (mod low 2))
        (floor f1 2))
     (dec x)
     (*
      (mod f1 2)
      (floor
       (+ (+ (* (expt 2 (1- i)) c) (floor a 2)) f2)
       (expt 2 i)))
     (+ (* (expt 2 (1- i)) (mod a 2))
        (floor low 2))
     (if (equal (mod f1 2) 0)
         (+ (* (expt 2 (1- i)) c) (floor a 2))
       (mod
        (+ (+ (* (expt 2 (1- i)) c) (floor a 2))
           f2)
        (expt 2 i)))
     result
     f2
     i)))

;;; Replace wp-zcoef by the more general function.

(defthm wp-zcoef-g-instance
  (equal (wp-zcoef f1 x c low a f1save f2)
         (wp-zcoef-g f1 x c low a (* f1save f2) f2 8)))

;;; The remaining events in this file illustrate the use of the tail
;;; recursion generic theory.

;;; Partition the state into two halves, an "a" component that does the
;;; effective computation, and an "s" component that drives the computation.

;;; The "a" component is packaged into a long integer.

(defun low (a i) (mod a (expt 2 i)))
(defun a (a i) (mod (floor a (expt 2 i)) (expt 2 i)))
(defun c (a i) (floor a (expt 2 (* 2 i))))

;;; The "s" component is represented by a list.

(defun x (s) (car s))
(defun f1 (s) (cadr s))
(defun f2 (s) (caddr s))
(defun result (s) (cadddr s))
(defun i (s) (car (cddddr s)))

;;; Define the instantiation the generic function h.  wp-zcoef-h multiplies
;;; in the standard way, except that it delivers twice the product.

(defun wp-zcoef-h (s)
  (declare (xargs :measure (dec (x s))))
  (if (equal (dec (x s)) 0)
      0
    (* 2 (+ (wp-zcoef-h
             (list (dec (x s))
                   (floor (f1 s) 2)
                   (f2 s)
                   (result s)
                   (i s)))
            (if (equal (mod (f1 s) 2) 0)
                0
              (nfix (f2 s)))))))

;;; Compute (hs s), the bottom object under tau.

(defun btm-s (s)
  (declare (xargs :measure (dec (x s))))
  (if (equal (dec (x s)) 0)
      s
    (btm-s (list (dec (x s))
                 (floor (f1 s) 2)
                 (f2 s)
                 (result s)
                 (i s)))))

(set-irrelevant-formals-ok t)

;;; Define an induction hint patterned after two copies of wp-zcoef-g.

(defun ind-2 (f1 x c low a f1p xp cp lowp ap f2 i)
  (declare (xargs :measure (dec x)))
  (if (equal (dec x) 0)
      0
    (ind-2
     (+ (* (expt 2 (1- i)) (mod low 2))
        (floor f1 2))
     (dec x)
     (*
      (mod f1 2)
      (floor
       (+ (+ (* (expt 2 (1- i)) c) (floor a 2)) f2)
       (expt 2 i)))
     (+ (* (expt 2 (1- i)) (mod a 2))
        (floor low 2))
     (if (equal (mod f1 2) 0)
         (+ (* (expt 2 (1- i)) c) (floor a 2))
       (mod
        (+ (+ (* (expt 2 (1- i)) c) (floor a 2))
           f2)
        (expt 2 i)))
     (+ (* (expt 2 (1- i)) (mod lowp 2))
        (floor f1p 2))
     (dec xp)
     (*
      (mod f1p 2)
      (floor
       (+ (+ (* (expt 2 (1- i)) cp) (floor ap 2)) f2)
       (expt 2 i)))
     (+ (* (expt 2 (1- i)) (mod ap 2))
        (floor lowp 2))
     (if (equal (mod f1p 2) 0)
         (+ (* (expt 2 (1- i)) cp) (floor ap 2))
       (mod
        (+ (+ (* (expt 2 (1- i)) cp) (floor ap 2))
           f2)
        (expt 2 i)))
     f2
     i)))

(defthm mod-expt-2
  (implies (and (natp a)
                (natp b)
                (not (zp i)))
           (equal (mod (+ a (* 2 b)) (expt 2 i))
                  (+ (mod a 2) (* 2 (mod (+ b (floor a 2)) (expt 2 (1- i)))))))
  :hints (("Goal"
           :in-theory (enable mod))
          ("Subgoal 1'"
           :use (:instance floor-floor-integer-alt
                           (x (+ 1 (* 2 b) (* 2 k)))
                           (i 2)
                           (j (expt 2 (+ -1 i))))
           :in-theory (disable floor-floor-integer-alt))))

(defthm equal-odd-even
  (implies (and (equal (mod a 2) (mod b 2))
                (integerp a)
                (integerp b))
           (not (equal (+ 1 a) b))))

;;; This lemma reduces an equality check between two difference
;;; applications of wp-zcoef-g to equality checks on its arguments.

(defthm equal-wp-zcoef-g
  (implies (and (equal (mod f1 (expt 2 (1- x)))
                       (mod f1p (expt 2 (1- x))))
                (equal x xp)
                (equal (+ (* c (expt 2 i)) a)
                       (+ (* cp (expt 2 i)) ap))
                (equal low lowp)
                (<= x i)
                (not (zp x))
                (natp f1)
                (natp x)
                (natp c)
                (natp low)
                (natp a)
                (natp f2)
                (natp i)
                (natp f1p)
                (natp xp)
                (natp cp)
                (natp lowp)
                (natp ap))
           (equal (equal (wp-zcoef-g f1 x c low a result f2 i)
                         (wp-zcoef-g f1p xp cp lowp ap result f2 i))
                  t))
  :hints (("Goal"
           :nonlinearp t
           :induct (ind-2 f1 x c low a f1p xp cp lowp ap f2 i)
           :in-theory (disable (:rewrite mod-zero . 1)))))

(defthm btm-s-destruct
  (implies (and (not (zp (x s)))
                (natp (cadr s))
                (natp (caddr s))
                (natp (cadddr s))
                (natp (cadddr (cdr s))))
           (and (equal (car (btm-s s)) 1)
                (equal (cadr (btm-s s))
                       (floor (f1 s) (expt 2 (1- (x s)))))
                (equal (caddr (btm-s s)) (f2 s))
                (equal (cadddr (btm-s s)) (result s))
                (equal (car (cddddr (btm-s s))) (i s)))))

(defthm floor-mod-rewrite
  (implies (and (natp a)
                (natp b)
                (equal c (floor a b)))
           (and (equal (+ (mod a b) (* b c)) a)
                (equal (+ (* b c) (mod a b)) a))))

(defthm to-mod
  (implies (and (integerp i)
                (< 0 i)
                (natp a))
           (equal (* (expt 2 (+ -1 i)) (floor a (expt 2 i)))
                  (- (floor a 2) (mod (floor a 2) (expt 2 (+ -1 i)))))))

(defthm floor-+-expt
  (implies (and (integerp a)
                (integerp b)
                (natp i)
                (natp j))
           (equal (floor (+ a (* b (expt 2 i)))
                         (expt 2 j))
                  (if (< i j)
                      (floor (+ b (floor a (expt 2 i)))
                             (expt 2 (- j i)))
                    (+ (floor a (expt 2 j))
                       (* b (expt 2 (- i j)))))))
  :hints (("Goal"
           :use ((:instance floor-floor-integer-alt
                            (x (+ a (* b (expt 2 i))))
                            (i (expt 2 i))
                            (j (expt 2 (- j i))))
                 (:instance floor-floor-integer-alt
                            (x (+ a (* b (expt 2 i))))
                            (i (expt 2 j))
                            (j (expt 2 (- i j)))))
           :in-theory (disable floor-floor-integer-alt))))

(defthm mod-*-arg2-general
  (implies (and (equal b (floor a x))
                (not (zp x))
                (not (zp y))
                (integerp a))
           (equal (+ (mod a x)
                     (* x (mod b y)))
                  (mod a (* x y))))
  :hints
  (("Goal"
    :nonlinearp t)))

(set-default-hints nil)

(defthm wp-zcoef-g=h
  (implies (and (natp f1)
                (not (zp x))
                (natp i)
                (<= x i)
                (natp f2)
                (< f2 (expt 2 i))
                (< low (expt 2 i))
                (natp c)
                (natp a)
                (natp low)
                (natp result))
           (equal
            (wp-zcoef-g f1 x c low a result f2 i)
            (if (equal (dec x) 0)
                (equal (+ (* (+ (* (expt 2 (1- i)) c)
                                (floor a 2))
                             (expt 2 i))
                          (+ (* (expt 2 (1- i))
                                (mod a  2))
                             (floor low 2)))
                       result)
              (let ((a (floor (+ low
                                 (* a (expt 2 i))
                                 (* c (expt 2 i) (expt 2 i))
                                 (* (expt 2 i)
                                    (wp-zcoef-h (list x f1 f2 result i))))
                              (expt 2 (1- x)))))
                (equal (+ (* (+ (* (expt 2 (1- i)) (c a i))
                                (floor (a a i) 2))
                             (expt 2 i))
                          (+ (* (expt 2 (1- i))
                                (mod (a a i) 2))
                             (floor (low a i) 2)))
                       result)))))
  :hints
  (("Goal"
    :use
    (:instance
     (:functional-instance
      g=h
      (bb (lambda (s) (equal (dec (x s)) 0)))
      (qt (lambda (a s)
            (equal (+ (* (+ (* (expt 2 (1- (i s))) (c a (i s)))
                            (floor (a a (i s)) 2))
                         (expt 2 (i s)))
                      (+ (* (expt 2 (1- (i s)))
                            (mod (a a (i s)) 2))
                         (floor (low a (i s)) 2)))
                   (result s))))
      (g (lambda (a s) (wp-zcoef-g
                        (f1 s)
                        (x s)
                        (c a (i s))
                        (low a (i s))
                        (a a (i s))
                        (result s)
                        (f2 s)
                        (i s))))
      (measure-g (lambda (s) (dec (x s))))
      (tau (lambda (s)
             (list (dec (x s))
                   (floor (f1 s) 2)
                   (f2 s)
                   (result s)
                   (i s))))
      (rho (lambda (a s)
             (if (equal (mod (f1 s) 2) 0)
                 (floor a 2)
               (+ (floor a 2)
                  (* (f2 s)
                     (expt 2 (i s)))))))
      (rhoh (lambda (a s)
              (if (equal (mod (f1 s) 2) 0)
                  (* 2 a)
                (* 2 (+ a
                        (f2 s))))))
      (h (lambda (s) (wp-zcoef-h s)))
      (rt (lambda (a s)
            (and (natp (f1 s))
                 (not (zp (x s)))
                 (natp (i s))
                 (<= (x s) (i s))
                 (natp (f2 s))
                 (< (f2 s) (expt 2 (i s)))
                 (natp a))))
      (id (lambda () 0))
      (op (lambda (a x s)
            (if (equal (dec (x s)) 0)
                a
              (floor (+ a (* (expt 2 (i s)) x)) (expt 2 (1- (x s)))))))
      (hs (lambda (s) (btm-s s))))
     (s (list x f1 f2 result i))
     (a (+ low (* a (expt 2 i)) (* c (expt 2 i) (expt 2 i))))))
   ("Subgoal 12"
    :use ((:instance equal-wp-zcoef-g
                     (f1p f1)
                     (xp x)
                     (cp (+ c (floor (+ low (* a (expt 2 i))) (* (expt 2 i) (expt 2 i)))))
                     (lowp low)
                     (ap (mod a (expt 2 i))))
          (:instance floor-floor-integer-alt
                     (x (+ low (* a (expt 2 i))))
                     (i (expt 2 i))
                     (j (expt 2 i))))
    :in-theory (disable floor-floor-integer-alt
                        equal-wp-zcoef-g
                        (:definition wp-zcoef-g)
                        (:definition btm-s)
                        (:rewrite prefer-positive-addends-<)
                        (:rewrite prefer-positive-addends-equal)
                        (:definition wp-zcoef-h)))
   ("Subgoal 2"
    :expand (wp-zcoef-g (cadr s)
                        (car s)
                        (floor a (expt 2 (* 2 (cadddr (cdr s)))))
                        (mod a (expt 2 (cadddr (cdr s))))
                        (mod (floor a (expt 2 (cadddr (cdr s))))
                             (expt 2 (cadddr (cdr s))))
                        (cadddr s)
                        (caddr s)
                        (cadddr (cdr s))))))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(defthm wp-zcoef-h-multiplies
  (implies (and (not (zp (x s)))
                (<= (x s) (i s))
                (natp (car s))
                (natp (cadr s))
                (natp (caddr s))
                (natp (cadddr s))
                (natp (cadddr (cdr s))))
           (equal (wp-zcoef-h s)
                  (* 2 (f2 s) (mod (f1 s) (expt 2 (1- (x s)))))))
  :hints (("Goal"
           :in-theory (enable mod))
; Matt K. added the following 2/21/09 (after ACL2 v3-4) because of a heuristic
; change suggested by Robert Krug, in which the "pseudo-fn-count" is used in
; arith-term-order just as it has been in term-order.  That change exposed a
; known looping issue with the arithmetic-3 library, specifically the lemma
; disabled below.
          ("Subgoal *1/2.2'9'"
           :in-theory (disable prefer-positive-addends-equal))))

(defthm floor-mod-*-2-kb
  (implies (and (equal c (floor a 2))
                (equal b (* 2 d))
                (rationalp a)
                (rationalp d))
           (equal (+ (* b c)
                     (* d (mod a 2)))
                  (* d a))))

;;; Program correctness result

(defthm wp-zcoef-is-correct
  (implies (and (natp f2)
                (< f2 256)
                (natp f1)
                (< f1 256)
                (natp low)
                (< low 256)
                (natp c))
           (wp-zcoef-1 f1 c low f2)))

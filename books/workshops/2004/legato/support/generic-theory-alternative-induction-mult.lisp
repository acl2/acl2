(in-package "ACL2")
(include-book "../../../../arithmetic-3/bind-free/top")
(include-book "../../../../arithmetic-3/floor-mod/floor-mod")
(include-book "generic-theories")
(set-non-linearp nil)

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

;;; This is a mechanically derived weakest precondition at location ZCOEF.

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

;;; Transform wp-zcoef to an instance of the more general function.

(defthm wp-zcoef-g-instance
  (equal (wp-zcoef f1 x c low a f1save f2)
         (wp-zcoef-g f1 x c low a (* f1save f2) f2 8)))

;;; Since c effectively behaves as an extension of a, combining them into
;;;
;;;      ac = a + 2^i*c
;;;
;;; both simplifies the body of wp-zcoef-ac and enables easy expression of an
;;; alternate induction.

(defun wp-zcoef-ac (f1 x ac low result f2 i)
  (declare (xargs :measure (dec x)))
  (if (equal (dec x) 0)
      (equal (+ (floor low 2) (* ac (expt 2 (1- i))))
             result)
    (wp-zcoef-ac
     (+ (floor f1 2) (* (expt 2 (1- i)) (mod low 2)))
     (dec x)
     (if (equal (mod f1 2) 0)
         (floor ac 2)
       (+ f2 (floor ac 2)))
     (+ (floor low 2)
        (* (expt 2 (1- i)) (mod ac 2)))
     result
     f2
     i)))

;;; Use the alternative induction generic theory to prove an equivalence between
;;; wp-zcoef-g and wp-zcoef-ac.  Represent the state s as a list of state variables,
;;; and provide accessor functions.  Notice that the state includes all variables in
;;; wp-zcoef-g and wp-zcoef-ac.

(defun f1 (s) (car s))
(defun x (s) (cadr s))
(defun c (s) (caddr s))
(defun low (s) (cadddr s))
(defun a (s) (car (cddddr s)))
(defun result (s) (cadr (cddddr s)))
(defun f2 (s) (caddr (cddddr s)))
(defun i (s) (cadddr (cddddr s)))
(defun ac (s) (car (cddddr (cddddr s))))

;;; We now prove an instance of fn1-as-fn2.

(defthm wp-zcoef-g-as-ac
  (implies (and (not (zp x))
                (integerp i)
                (natp f1)
                (natp c)
                (natp low)
                (natp a)
                (natp result)
                (natp f2)
                (not (< i x)))
           (equal (wp-zcoef-g f1 x c low a result f2 i)
                  (wp-zcoef-ac f1 x (+ a (* c (expt 2 i))) low result f2 i)))
  :hints
  (("Goal"
    :nonlinearp t
    :in-theory (disable (:rewrite reduce-integerp-+)
                        (:rewrite floor-zero . 3)
                        (:rewrite floor-zero . 4)
                        (:rewrite mod-x-y-=-x . 4))
    :use
    (:instance
     (:functional-instance
      fn1-as-fn2
      (b1 (lambda (s) (equal (dec (x s)) 0)))
      (b2 (lambda (s) (equal (dec (x s)) 0)))
      (q1 (lambda (s) (equal (+ (* (+ (* (expt 2 (1- (i s))) (c s))
                                      (floor (a s) 2))
                                   (expt 2 (i s)))
                                (+ (* (expt 2 (1- (i s))) (mod (a s) 2))
                                   (floor (low s) 2)))
                             (result s))))
      (q2 (lambda (s) (equal (+ (floor (low s) 2)
                                (* (ac s) (expt 2 (1- (i s)))))
                             (result s))))
      (p (lambda (s) (and (not (zp (x s)))
                          (integerp (i s))
                          (natp (f1 s))
                          (natp (c s))
                          (natp (low s))
                          (natp (a s))
                          (natp (result s))
                          (natp (f2 s))
                          (natp (ac s))
                          (not (< (i s) (x s))))))
      (fn1 (lambda (s)
             (wp-zcoef-g (f1 s) (x s) (c s) (low s) (a s) (result s) (f2 s) (i s))))
      (fn2 (lambda (s)
             (wp-zcoef-ac (f1 s) (x s) (ac s) (low s) (result s) (f2 s) (i s))))
      (sigma1 (lambda (s)
                (list
                 (+ (* (expt 2 (1- (i s))) (mod (low s) 2))
                    (floor (f1 s) 2))
                 (dec (x s))
                 (if (equal (mod (f1 s) 2) 0)
                     0
                   (floor
                    (+ (+ (* (expt 2 (1- (i s))) (c s))
                          (floor (a s) 2))
                       (f2 s))
                    (expt 2 (i s))))
                 (+ (* (expt 2 (1- (i s))) (mod (a s) 2))
                    (floor (low s) 2))
                 (if (equal (mod (f1 s) 2) 0)
                     (+ (* (expt 2 (1- (i s))) (c s))
                        (floor (a s) 2))
                   (mod
                    (+ (+ (* (expt 2 (1- (i s))) (c s))
                          (floor (a s) 2))
                       (f2 s))
                    (expt 2 (i s))))
                 (result s)
                 (f2 s)
                 (i s)
                 (ac s))))
      (sigma2 (lambda (s)
                (list
                 (+ (* (expt 2 (1- (i s))) (mod (low s) 2))
                    (floor (f1 s) 2))
                 (dec (x s))
                 (if (equal (mod (f1 s) 2) 0)
                     0
                   (floor
                    (+ (+ (* (expt 2 (1- (i s))) (c s))
                          (floor (a s) 2))
                       (f2 s))
                    (expt 2 (i s))))
                 (+ (* (expt 2 (1- (i s))) (mod (ac s) 2))
                    (floor (low s) 2))
                 (if (equal (mod (f1 s) 2) 0)
                     (+ (* (expt 2 (1- (i s))) (c s))
                        (floor (a s) 2))
                   (mod
                    (+ (+ (* (expt 2 (1- (i s))) (c s))
                          (floor (a s) 2))
                       (f2 s))
                    (expt 2 (i s))))
                 (result s)
                 (f2 s)
                 (i s)
                 (if (equal (mod (f1 s) 2) 0)
                     (floor (ac s) 2)
                   (+ (f2 s) (floor (ac s) 2))))))
      (measure1 (lambda (s) (if (zp (x s)) 256 (x s))))
      (id-alt
       (lambda (s)
         (list
          (f1 s)
          (x s)
          (c s)
          (low s)
          (a s)
          (result s)
          (f2 s)
          (i s)
          (+ (a s) (* (c s) (expt 2 (i s))))))))
     (s (list f1 x c low a result f2 i 0))))))

;;; Needed for mod-+-1

(defthm equal-odd-even
  (implies (and (equal (mod a 2) (mod b 2))
                (integerp a)
                (integerp b))
           (not (equal (+ 1 a) b))))

;;; Needed for f2-induction

(defthm mod-+-1
  (implies (and (equal (mod a 2) 0)
                (natp i)
                (integerp a))
           (equal (mod (+ 1 a) (expt 2 i))
                  (if (equal i 0)
                      0
                    (+ 1 (mod a (expt 2 i))))))
  :hints (("Goal"
           :in-theory (disable simplify-mod-+-mod-weak))))

;;; We now look for a substitution id-alt, which leaves wp-zcoef-ac invariant.
;;; Since we will be proving that sigma1 and id-alt commute, we would indeed have
;;; a simple proof if sigma1 and id-alt altered disjoint sets of variables.  Only
;;; f2, result and i are left unchanged by sigma1.  Looking at the assembly
;;; language program, we see that a change in f2 only affects ac.  So if we
;;; decremented f2 and incremented ac whenever (f1 mod 2) = 1, the computation
;;; would be unchanged.  Notice that a single change in f2 could affect the
;;; computation on the next x - 1 iterations.  So it is necessary to add
;;; (* 2 (mod f1 (expt 2 (1- x)))) to ac.  This defines id-alt.

(defthm f2-induction
  (implies (and (not (zp f2))
                (not (zp x))
                (natp f1)
                (natp ac)
                (natp low)
                (natp result)
                (integerp i)
                (not (< i x)))
           (equal (wp-zcoef-ac f1 x ac low result f2 i)
                  (wp-zcoef-ac f1
                               x
                               (+ ac (* 2 (mod f1 (expt 2 (1- x)))))
                               low
                               result
                               (1- f2)
                               i)))
  :hints
  (("Goal"
    :nonlinearp t
    :in-theory (disable (:rewrite prefer-positive-addends-equal))
;       (:rewrite equal-odd-even))
    :use
    (:instance
     (:functional-instance
      fn1-as-fn2
      (b1 (lambda (s) (equal (dec (x s)) 0)))
      (b2 (lambda (s) (equal (dec (x s)) 0)))
      (q1 (lambda (s) (equal (+ (floor (low s) 2)
                                (* (ac s) (expt 2 (1- (i s)))))
                             (result s))))
      (q2 (lambda (s) (equal (+ (floor (low s) 2)
                                (* (ac s) (expt 2 (1- (i s)))))
                             (result s))))
      (p (lambda (s) (and (not (zp (f2 s)))
                          (not (zp (x s)))
                          (integerp (i s))
                          (natp (f1 s))
                          (natp (c s))
                          (natp (low s))
                          (natp (a s))
                          (natp (result s))
                          (natp (ac s))
                          (not (< (i s) (x s))))))
      (fn1 (lambda (s)
             (wp-zcoef-ac (f1 s) (x s) (ac s) (low s) (result s) (f2 s) (i s))))
      (fn2 (lambda (s)
             (wp-zcoef-ac (f1 s) (x s) (ac s) (low s) (result s) (f2 s) (i s))))
      (sigma1 (lambda (s)
                (list
                 (+ (* (expt 2 (1- (i s))) (mod (low s) 2))
                    (floor (f1 s) 2))
                 (dec (x s))
                 (c s)
                 (+ (* (expt 2 (1- (i s))) (mod (ac s) 2))
                    (floor (low s) 2))
                 (a s)
                 (result s)
                 (f2 s)
                 (i s)
                 (if (equal (mod (f1 s) 2) 0)
                     (floor (ac s) 2)
                   (+ (f2 s) (floor (ac s) 2))))))
      (sigma2 (lambda (s)
                (list
                 (+ (* (expt 2 (1- (i s))) (mod (low s) 2))
                    (floor (f1 s) 2))
                 (dec (x s))
                 (c s)
                 (+ (* (expt 2 (1- (i s))) (mod (ac s) 2))
                    (floor (low s) 2))
                 (a s)
                 (result s)
                 (f2 s)
                 (i s)
                 (if (equal (mod (f1 s) 2) 0)
                     (floor (ac s) 2)
                   (+ (f2 s) (floor (ac s) 2))))))
      (measure1 (lambda (s) (if (zp (x s)) 256 (x s))))
      (id-alt
       (lambda (s)
         (list
          (f1 s)
          (x s)
          (c s)
          (low s)
          (a s)
          (result s)
          (1- (f2 s))
          (i s)
          (+ (ac s) (* 2 (mod (f1 s) (expt 2 (1- (x s))))))))))
     (s (list f1 x 0 low 0 result f2 i ac))))
   ("Subgoal 3"
    :nonlinearp t
    :in-theory (disable   (:rewrite reduce-integerp-+)))
   ("Subgoal 2"
    :nonlinearp t
    :in-theory (disable   (:rewrite reduce-integerp-+)))))

;;; This is the base case for the alternative induction.  Its form is readily
;;; apparent, since the program simply right shifts ac and low x times when f2=0.

(defthm f2-induction-base-case
  (implies (and (equal f2 0)
                (not (zp x))
                (natp f1)
                (natp ac)
                (natp low)
                (natp result)
                (integerp i)
                (not (< i x)))
           (equal (wp-zcoef-ac f1 x ac low result f2 i)
                  (equal (+ (floor low (expt 2 x))
                            (* ac (expt 2 (- i x))))
                         result)))
  :hints
  (("Goal"
    :induct (wp-zcoef-ac f1 x ac low result f2 i)
    :do-not '(generalize))))

(set-irrelevant-formals-ok t)

;;; This is the induction hint corresponding to id-alt

(defun wp-ind-id-alt (f1 x ac f2)
  (if (zp f2)
      t
    (wp-ind-id-alt f1 x (+ ac (* 2 (mod f1 (expt 2 (1- x))))) (1- f2))))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

;;; Rewrite an arbitrary application of wp-zcoef-ac into the base case.

(defthm wp-zcoef-ac-as-0
  (implies
   (and (not (zp x))
        (natp f1)
        (natp ac)
        (natp low)
        (natp result)
        (natp f2)
        (integerp i)
        (not (< i x)))
   (equal (wp-zcoef-ac f1 x ac low result f2 i)
          (if (zp f2)
              (equal (+ (floor low (expt 2 x))
                        (* ac (expt 2 (- i x))))
                     result)
            (wp-zcoef-ac
             f1
             x
             (+ ac (* 2 f2 (mod f1 (expt 2 (1- x)))))
             low
             result
             0
             i))))
  :hints
  (("Goal"
    :nonlinearp t
    :induct (wp-ind-id-alt f1 x ac f2))))

;;; Finally, the correctness result.

(defthm mult-program-is-correct
  (implies (and (< low 256)
                (< f1 256)
                (< f2 256)
                (natp f1)
                (natp c)
                (natp low)
                (natp f2))
           (wp-zcoef-1 f1 c low f2)))

(in-package "ACL2")
(include-book "../../../../arithmetic-3/bind-free/top")
(include-book "../../../../arithmetic-3/floor-mod/floor-mod")

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

(defthm floor-mod-rewrite
  (and (implies (and (equal d (* b c))
                     (rationalp a)
                     (rationalp b)
                     (rationalp c))
                (equal (+ (* c (mod a b))
                          (* d (floor a b)))
                       (* c a)))
       (implies (and (equal d (* b c))
                     (rationalp a)
                     (rationalp b)
                     (rationalp c)
                     (rationalp e))
                (equal (+ (* c (mod a b))
                          (* d (floor a b))
                          e)
                       (+ (* c a) e)))))

(defun ind-hint (i)
  (if (zp i)
      0
    (ind-hint (1- i))))

(defthm hack
(IMPLIES (AND (EQUAL (EXPT 2 I) (+ 1 J))
              (INTEGERP J)
              (INTEGERP K)
              (< -1 J)
              (NOT (ZP I))
              (NOT (EQUAL I 1)))
         (not (EQUAL (+ 1 (MOD J (EXPT 2 (+ -1 I))))
                     (MOD (+ 1 J) (EXPT 2 (+ -1 I)))))))

(defthm mod-+-1
  (implies (and   (equal (mod a 2) 0)
                  (natp i)
                  (integerp a))
           (equal (mod (+ 1 a) (expt 2 i))
                  (if (equal i 0)
                      0
                    (+ 1 (mod a (expt 2 i))))))
  :hints (("Goal"
           :induct (ind-hint i)
           :do-not '(generalize))))

;;; Generalize the correctness theorem.

(defthm wp-zcoef-g-multiplies
  (implies (and (not (zp x))
                (integerp i)
                (<= x i)
                (natp f1)
                (natp low)
                (natp a)
                (natp c)
                (< low (expt 2 i))
                (natp f2)
                (< f2 (expt 2 i)))
           (equal (wp-zcoef-g f1 x c low a result f2 i)
                  (equal
                   (+ (floor (+ low (* (expt 2 i) a) (* (expt 2 i) (expt 2 i) c))
                             (expt 2 x))
                      (* f2
                         (mod f1 (expt 2 (1- x)))
                         (floor (expt 2 i) (expt 2 (1- x)))))
                   result)))
  :hints (("Subgoal *1/2.16"
           :nonlinearp t)
          ("Subgoal *1/2.15.1"
           :nonlinearp t)
          ("Subgoal *1/2.14.1"
           :nonlinearp t)
          ("Subgoal *1/2.13.1"
           :nonlinearp t)
          ("Subgoal *1/2.12"
           :nonlinearp t)
          ("Subgoal *1/2.11.1"
           :nonlinearp t)))

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

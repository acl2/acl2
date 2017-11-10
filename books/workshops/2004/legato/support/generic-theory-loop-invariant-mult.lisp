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

(set-irrelevant-formals-ok t)

;;; Define an induction hint which recurses on two copies of wp-zcoef-g.

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

;;; This lemma is needed to prove mod-+-1.

(defthm equal-odd-even
  (implies (and (equal (mod a 2) (mod b 2))
                (integerp a)
                (integerp b))
           (not (equal (+ 1 a) b))))

;;; This lemma is needed for equal-wp-zcoef-g.

(defthm mod-+-1
  (implies (and   (equal (mod a 2) 0)
                  (natp i)
                  (integerp a))
           (equal (mod (+ 1 a) (expt 2 i))
                  (if (equal i 0)
                      0
                    (+ 1 (mod a (expt 2 i))))))
  :hints (("Goal"
           :in-theory (disable simplify-mod-+-mod-weak))))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

;;; This lemma reduces an equality proof between two different
;;; applications of wp-zcoef-g to equality proof on its arguments.

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
           :in-theory (disable (:rewrite mod-zero . 1)))
          ("Subgoal *1/2.10.1'"

; Matt K. mod for April 2016 mod after adding type-set bit for {1}: I really
; hate adding this hint, but this was the final change needed in order to get
; the "everything" regression to pass, and this is a proof that one needn't
; expect to be preserved by heuristic changes.  If we were to change source
; function obj-table to substitute *1* for a term with type-set *ts-one*, then
; this proof would again go through; but other proofs would fail (see the
; comment in obj-table).  For possible evidence that this is a fragile proof,
; note that I was able to get a rewrite-stack overflow when messing around in
; the proof-builder.

           :cases ((equal j 1)))))

;;; The identification of an invariant.is the key user contribution.

(defun wp-zcoef-g-invariant (f1 x c low a result f2 i)
  (and (not (zp x))
       (<= x i)
       (< f2 (expt 2 i))
       (natp f1)
       (natp f2)
       (natp result)
       (natp i)
       (natp c)
       (natp low)
       (natp a)
       (equal (+ (floor low (expt 2 x))
                 (* a (expt 2 (- i x)))
                 (* c (expt 2 i) (expt 2 (- i x)))
                 (* f2
                    (mod f1 (expt 2 (1- x)))
                    (floor (expt 2 i) (expt 2 (1- x)))))
              result)))

(defthm expand-nth
  (implies (not (zp i))
           (equal (nth i s)
                  (nth (1- i) (cdr s)))))

(defthm equal-cancel
  (implies (and (acl2-numberp b)
                (acl2-numberp c))
           (equal (equal (+ a b) (+ a c))
                  (equal b c))))

(set-default-hints nil)

;;; Instantiate the generic loop invariant theory.

(defthm wp-zcoef-loop-invariant
  (implies (wp-zcoef-g-invariant f1 x c low a result f2 i)
           (wp-zcoef-g f1 x c low a result f2 i))
  :hints
  (("Goal" :induct t)
   (loop-invariant-hint
    'wp-zcoef-g
    '(wp-zcoef-g-invariant f1 x c low a result f2 i))))

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

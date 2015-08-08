
(in-package "ACL2")

(include-book "test-help" :ttags (sat sat-cl))

;; -----------------------------------------------------------------
; This section was added by Matt K. to test waterfall parallelism hacks,
; specifically, to allow clause processors that modify state.  SULFA-THM fails
; in ACL2(p) with waterfall-parallelism enabled unless we make some
; accommodation.

#+acl2-par
(defttag our-waterfall-parallelism-hacks)
#+acl2-par
(set-waterfall-parallelism-hacks-enabled t)
;; -----------------------------------------------------------------

;; -----------------------------------------------------------------
;; Definitions

(defun bv-not (n x)
  (if (zp n)
      nil
    (cons (not (car x))
          (bv-not (1- n) (cdr x)))))

(defun n-bleq (n x y)
  (if (zp n)
      t
    (and (iff (car x) (car y))
         (n-bleq (1- n) (cdr x) (cdr y)))))

(defun xor3 (x y z)
  (xor x (xor y z)))

(defun maj3 (x y z)
  (if x (or y z)
    (and y z)))

;; Returns a n+1 length sum of the first
;; n bits of a and b (plus the carray).
(defun v-adder (n c a b)
  (if (zp n)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (1- n)
                   (maj3 c (car a) (car b))
                   (cdr a) (cdr b)))))

(defun nth-cdr (n x)
  (if (zp n)
      x
    (nth-cdr (1- n) (cdr x))))

(defun nth-sublist (n lst)
  (if (zp n)
      nil
    (cons (car lst) (nth-sublist (1- n) (cdr lst)))))

(defun append-n (n x y)
  (if (zp n)
      y
    (cons (car x) (append-n (1- n) (cdr x) y))))

(defun n-nills (n)
  (if (zp n)
      nil
    (cons nil (n-nills (1- n)))))

(defun rev-n (n x ans)
  (if (zp n)
      ans
    (rev-n (1- n) (cdr x) (cons (car x) ans))))

(defun mux-n-help (n in rsel)
  (if (zp n)
      (car in)
    (if (car rsel)
        (mux-n-help (1- n) (nth-cdr (expt 2 (1- n)) in) (cdr rsel))
      (mux-n-help (1- n) in (cdr rsel)))))

(defun mux-n (n in sel)
  (mux-n-help n in (rev-n n sel nil)))

(defun mux-n-w-help (n w in)
  (if (zp n)
      nil
    (cons (car in) (mux-n-w-help (1- n) w (nth-cdr w in)))))

(defun mux-n-w1 (nw sn w in sel)
  (if (zp nw)
      nil
    (cons (mux-n sn (mux-n-w-help (expt 2 sn) w in) sel)
          (mux-n-w1 (1- nw) sn w (cdr in) sel))))

(defun mux-n-w (n w in sel)
  (mux-n-w1 w n w in sel))

(defun shift-mux-help (n w reg)
  (if (zp n)
      nil
    (append-n w reg (shift-mux-help (1- n) w (cons nil reg)))))

(defun shifter (sn rn rshift reg)
  (if (zp sn)
      reg
    (mux-n-w sn rn (shift-mux-help (expt 2 sn) rn reg) rshift)))

(defun increment (n x)
  (if (zp n)
      nil
    (if (car x)
        (cons nil (increment (1- n) (cdr x)))
      (cons t (cdr x)))))

(defun next_digit_counter_state (x)
  (if (n-bleq 4 x '(t nil nil t))
      (list '(nil nil nil nil) t)
    (list (increment 4 x) nil)))

(defun next_counter_state (n x)
  (let* ((curr_d_out (next_digit_counter_state (car x)))
         (curr_d_val (car curr_d_out))
         (curr_d_reset (cadr curr_d_out)))
    (if (zp n)
        nil
      (if curr_d_reset
          (cons curr_d_val (next_counter_state (1- n) (cdr x)))
        (cons curr_d_val (cdr x))))))

(defun valid_digit (a)
  (let ((a1 (cadr a))
        (a2 (caddr a))
        (a3 (cadddr a)))
    (not (and a3 (or a2 a1)))))

(defun valid_digits (n x)
  (if (zp n)
      t ;;(not (consp x))
    (and (valid_digit (car x))
         (valid_digits (1- n) (cdr x)))))

(defun n-nth (n x)
  (if (zp n)
      (car x)
    (n-nth (1- n) (cdr x))))

;; Return true if bv is a bit vector of length n.

(defun bvp (n bv)
  (if (zp n)
      (not bv)
    (and (consp bv)
         (booleanp (car bv))
         (bvp (1- n) (cdr bv)))))

;; A similar function, but in our decidable subset.
;; Note that we don't guarantee that the bit-vector
;; is boolean.  While that is a guard of most of our
;; functions, it should only be necessary when we need
;; to jump from n-bleq to equality---and booleanp
;; is not in our decidable subset.  Of course, it's
;; not a big deal to have a function with an unknown
;; definition...it just generates a bunch of ugly messages.

(defun bv-hyp (n bv)
  (if (zp n)
      (not bv)
    (bv-hyp (1- n) (cdr bv))))

;; Reverse an n bit list

(defun rev-n (n x ans)
  (if (zp n)
      ans
    (rev-n (1- n) (cdr x) (cons (car x) ans))))

;; Add pairs of A and B to list
(defun add-pairlist (A B list)
  (if (endp A)
      list
    (add-pairlist (cdr A) (cdr B)
                  (cons (cons (car A) (car B))
                        list))))

;; Whether a given signal is high
;; (usually represented as 't)
(defun highp (x)
  (if (consp x) nil (if x t nil)))

;; Whether a given signal is low
;; (represented as 'nil)
(defun lowp (x)
  (not x))

;; Whether a given signal is unknown
;; (usually represented as '(X))
(defun xValp (x)
  (consp x))

(defun xVal ()
  (cons 'x nil))

;; A tbit vector is represented as a list of values that
;; represent the following four values:
;;
;; under-constrained: 'x
;; nil: 'nil
;; true: anything else... generally true.
;;
;; We represent any value as equivalent to a value with nil
;; appended on the end.  Thus, a vector '(nil t x t) is equivalent
;; to the vector '(nil t x t nil nil nil).  This equivalence
;; leads to simpler functions that take advantage of the fact that
;; (car nil)=nil.  However, within a correctly typed-DE expression,
;; a bit vectur will take on a well-known length, and only be compared to
;; equal length vectors.

(defun bbit-and (x y)
  (if x (if y t nil) nil))

(defun tbit-and (x y)
  (cond
   ((or (lowp x) (lowp y))
    'nil)
   ((or (xValp x) (xValp y))
    (xval))
   (t 't)))

(defun concatn (n a b)
  (if (zp n)
      b
    (cons (car a) (concatn (- n 1) (cdr a) b))))

(defun uandn-help (n a)
  (if (zp n)
      t
    (if (car a)
        (uandn-help (- n 1) (cdr a))
      nil)))

(defun uandn (n a)
  (list (uandn-help n a)))

(defun bequiv (a b)
  (if a b (not b)))

(defun bbit-or (x y)
  (if x t (if y t nil)))

(defun tbit-or (x y)
  (cond
   ((or (highp x) (highp y))
    't)
   ((or (xValp x) (xValp y))
    (xval))
   (t 'nil)))

(defund unary-or-help (n lst)
  (if (zp n)
      nil
    (bbit-or (car lst) (unary-or-help (1- n) (cdr lst)))))

(defun unary-or (n x)
  (list (unary-or-help n x)))

(defund bv-and (n x y)
  (if (zp n)
      nil
    (cons (bbit-and (car x) (car y)) (bv-and (1- n) (cdr x) (cdr y)))))

(defund bv-or (n x y)
  (if (zp n)
      nil
    (cons (bbit-or (car x) (car y)) (bv-or (1- n) (cdr x) (cdr y)))))

(defun bbit-xor (x y)
  (if x (if y nil t) (if y t nil)))

(defun tbit-xor (x y)
  (cond
   ((and (lowp x) (lowp y))
    'nil)
   ((or (xValp x) (xValp y))
    (xval))
   ((or (lowp x) (lowp y))
    't)
   (t 'nil)))

(defund bv-xor (n x y)
  (if (zp n)
      nil
    (cons (bbit-xor (car x) (car y)) (bv-xor (1- n) (cdr x) (cdr y)))))

(defun bbit-not (x)
  (not x))

(defun tbit-not (x)
  (cond
   ((lowp x)
    't)
   ((xValp x)
    (xval))
   (t 'nil)))

(defun bv-eq (n x y)
  (uandn n (bv-not n (bv-xor n x y))))

(defun append-n (n x y)
  (if (zp n)
      y
    (cons (car x) (append-n (1- n) (cdr x) y))))

(defun a-n (n A B)
  (append-n n A B))

(defun bit-2-bool (n)
  (if (zp n) nil t))

(defund bv-const (w x)
  (if (zp w)
      nil
    (cons (bit-2-bool (mod x 2))
          (bv-const (1- w) (floor x 2)))))

(defun nth-sublist (n lst)
  (if (zp n)
      nil
    (cons (car lst) (nth-sublist (1- n) (cdr lst)))))

(defun get-sublist-h (lst lbit hbit)
  (if (zp lbit)
      (nth-sublist (1+ hbit) lst)
    (get-sublist-h (cdr lst) (1- lbit) (1- hbit))))


(defun np (x)
  (if (integerp x)
      (< x 0)
    t))

(defun nnfix (x)
  (if (np x)
      -1
    x))


(defun n-nils (n)
  (if (zp n)
      nil
    (cons nil (n-nils (1- n)))))


(defun nth-cdr (n x)
  (if (zp n)
      x
    (nth-cdr (1- n) (cdr x))))

(defun get-sublist (lst lbit hbit)
  (if (<= (nfix lbit) (nnfix hbit))
      (get-sublist-h lst lbit hbit)
    nil))

(defun g (lst lbit hbit)
  (get-sublist lst lbit hbit))

(defun update-sublist-h (lst lbit hbit val)
  (if (zp lbit)
      (append-n (1+ hbit)
                (get-sublist val lbit hbit)
                (nth-cdr (1+ hbit) lst))
    (cons (car lst)
          (update-sublist-h (cdr lst) (1- lbit) (1- hbit)
                            val))))

(defun update-sublist (lst lbit hbit val)
  (if (<= (nfix lbit) (nnfix hbit))
      (update-sublist-h lst lbit hbit val)
    lst))

(defun us (lst lbit hbit val)
  (update-sublist lst lbit hbit val))


(defund bv-decode-help (n rev-x)
  (declare (xargs :measure (nfix (1+ n))))
  (let ((len-h-ans (expt 2 (1- n)))) ;; half of the length of the answer
    (cond
     ((zp n)
      '(t))
     ((car rev-x)
      (append-n len-h-ans (n-nils len-h-ans) (bv-decode-help (1- n) (cdr rev-x))))
     (t
      (append-n len-h-ans (bv-decode-help (1- n) (cdr rev-x)) (n-nils len-h-ans))))))

(defund bv-duplicate (n w x)
  (cond
   ((zp n) nil)
   (t (append-n w x (bv-duplicate (1- n) w x)))))

(defund expand-mask (n flush_mask)
  (if (zp n)
      nil
    (if (car flush_mask)
        (a-n 32 (bv-duplicate 32 1 (bv-const 1 1))
             (expand-mask (1- n) (cdr flush_mask)))
      (a-n 32 (bv-duplicate 32 1 (bv-const 1 0))
           (expand-mask (1- n) (cdr flush_mask))))))

(defun true-bvp (x) (car x))

(defund submaskp (n x y)
  (cond ((zp n)
         t)
        ((or (not (car x)) (car y))
         (submaskp (1- n) (cdr x) (cdr y)))
        (t nil)))

(defun simple-mult1 (n sz a curr-b ans)
  (if (zp n)
      ans
    (simple-mult1
     (1- n)
     (1+ sz)
     (cdr a)
     (cons nil curr-b)
     (if (car a) (v-adder sz nil curr-b ans) ans))))

;; Multiply the n, bit, bit-vectors a and b using
;; n adders.
(defun simple-mult (n a b)
  (simple-mult1 n n a b nil))

;; -----------------------------------------------------------------
;; Theorems

;;(i-am-here)

(defthm SULFA-thm
  (true-bvp
   (bv-eq 1
          (uandn 8 (concatn 4 a b))
          (bv-and 1 (uandn 4 a) (uandn 4 b))))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;;(defthm general-thm
;;  (bequiv (uandn (+ x y) (concatn x a b))
;;          (and (uandn x a) (uandn y b))))

;; Start with something easy
(defthm n-bleq-2
  (n-bleq 2 x x)
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; (defthm n-bleq-2-false
;;   (n-bleq 2 x y)
;;   :hints (("Goal" :clause-processor (:function sat :hint nil))))

(defthm n-bleq-inst-2
  (n-bleq 2 (bv-not 4 x) (bv-not 4 x))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; Now I can prove things about Booleanp!
(defthm Booleanp-1
  (implies (not (Booleanp x))
           x)
    :hints (("Goal" :clause-processor (:function sat :hint nil)))
    :rule-classes nil)

;; (defthm Booleanp-2-false
;;   (implies (not (Booleanp x))
;;            (not x))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

;; (defthm Booleanp-2-false
;;   (implies (Booleanp x)
;;            (Booleanp y))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

;; (defthm Booleanp-2-false
;;   (implies (equal x 1)
;;            (Booleanp y))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

(defthm Booleanp-2
  (implies (equal x 1)
           (equal x 1))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-3
  (implies (and (equal x 1)
                (not (equal y nil))
                (not (equal y t)))
           (not (Booleanp y)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-4
  (implies (not (equal (car x) nil))
           (consp x))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; (defthm Booleanp-5-false
;;   (implies (consp x)
;;            (not (equal (car x) nil)))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

(defthm Booleanp-6
  (implies (and (equal (car x) 4)
                (equal (cdr x) 5))
           (equal x (cons 4 5)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-7
  (implies (equal x '0)
           (not (equal x '4)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; (defthm Booleanp-7-false
;;   (implies (and (equal (car x) nil)
;;                 (equal (cdr x) nil))
;;            (equal x (cons nil nil)))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

(defthm Booleanp-8
  (implies (and (equal (caar x) 0)
                (equal (cdar x) 1))
           (equal (car x) (cons 0 1)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; (defthm Booleanp-9-false
;;   (implies (and (equal (caar x) t)
;;                 (equal (cdar x) t))
;;            (equal (car x) (cons t 1)))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

;; (defthm Booleanp-9-false
;;   (implies (and (equal (caar x) 0)
;;                 (equal (cdar x) 1))
;;            (equal x (cons (cons 0 1) nil)))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))
;;   :rule-classes nil)

(defthm Booleanp-9
  (implies (and (equal (caar x) 0)
                (equal (cdar x) 1))
           x)
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-10
  (implies (and (equal (caar x) 4)
                (equal (cdar x) 5))
           (not (equal x 5)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-11
  (implies (and (equal (caar x) 4)
                (equal (cdar x) 5))
           (consp x))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-12
  (implies (eq (caar x) t)
           (not (eq (car x) (cons 6 7))))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

(defthm Booleanp-13
  (implies (eq (car x) (cons 6 (cons 7 nil)))
           (consp (cdar x)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

; Need some simple examples that test wierd cases, requiring
;; list axioms
;; ...

;; A Simple COI Check
(defthm 500th-bit-of-bv-not-not
  (iff (n-nth 500 (bv-not 1000 (bv-not 1000 x)))
       (n-nth 500 x))
     :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; Some examples from the TRIPS DSN-verification

#| ;; Commented because it takes a while
;; DEBUG---turn on
(defthm DSN-bv-or-expand-rewrite
  (true-bvp (bv-eq 256
                   (bv-or 256
                          (expand-mask 8 x)
                          (expand-mask 8 y))
                   (expand-mask 8 (bv-or 8 x y))))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))
|# ;|

(defthm DSN-submaskp-implies
  (implies (submaskp 256 x y)
           (submaskp 256 x (bv-or 256 y z)))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))

(defthm DSN-submaskp-implies-2
  (implies (submaskp 256 x z)
           (submaskp 256 x (bv-or 256 y z)))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))

; The rest are commented out by Matt K. because SBCL Version 1.0.16 with
; #+sb-thread has caused the following error on 32-bit linux running on a
; 64-bit machine, for the first of these:

; Error:  Heap exhausted: 1327104 bytes available, 12000016 requested. PROCEED WITH CAUTION!

; A similar error seems to occur for other forms after the first below, as
; well, so we comment them all out.

#||
(defthm n-bleq-1000
  (n-bleq 1000 x x)
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; 4 bit adder associativity
(defthm 4-bit-adder-associativity
  (n-bleq 4 (v-adder 4 nil (v-adder 4 nil a b) c)
          (v-adder 4 nil a (v-adder 4 nil b c)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; 32 bit adder associativity
(defthm 32-bit-adder-associativity
 (n-bleq 32 (v-adder 32 nil (v-adder 32 nil a b) c)
         (v-adder 32 nil a (v-adder 32 nil b c)))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))

#| ;; Commented because it takes a while
;; DEBUG---turn on
;; 200 Bit adder associativity
(defthm 200-bit-adder-associativity
 (n-bleq 200 (v-adder 200 nil (v-adder 200 nil a b) c)
         (v-adder 200 nil a (v-adder 200 nil b c)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))
|# ;|

;; 32x6 Shift-0
(defthm 32x6-Shift-0
 (implies
  (car (nth-cdr 5 shift0))
  (n-bleq 32
          (shifter 6 32 shift0 reg)
          (n-nills 32)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; 64x7 Shift-0
(defthm 64x7-Shift-0
 (implies
  (car (nth-cdr 6 shift0))
  (n-bleq 64 (shifter 7 64 shift0 reg)
          (n-nills 64)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; 32x4 Add-shift
(defthm 32x4-Add-shift
 (n-bleq 32
         (shifter 4 32 shift0 (shifter 4 32 shift1 reg))
         (shifter 5 32 (v-adder 4 nil shift0 shift1) reg))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

#| ;; Commented because it takes a while
;; DEBUG---turn on
;; 64x6 Add-shift
(defthm 64x6-Add-shift
 (n-bleq 64
         (shifter 6 64 shift0 (shifter 6 64 shift1 reg))
         (shifter 7 64 (v-adder 6 nil shift0 shift1) reg))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))
|# ;|

(defthm mult-4x4
 (n-bleq 8
         (simple-mult 4 a b)
         (simple-mult 4 b a))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))

#| ;; Commented because it takes a while
;; DEBUG---turn on
(defthm mult-8x8
 (n-bleq 16
         (simple-mult 8 a b)
         (simple-mult 8 b a))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))
|# ;|

;; 10 Digit Counter Invariant
(defthm 10-digit-counter-invariant
 (implies
  (valid_digits 10 x)
  (valid_digits 10 (next_counter_state 10 x)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; 100 Digit Counter Invariant
(defthm 100-digit-counter-invariant
 (implies
  (valid_digits 100 x)
  (valid_digits 100 (next_counter_state 100 x)))
  :hints (("Goal" :clause-processor (:function sat :hint nil))))
||#

;; 64x6 Add-shift False
;; (thm
;;  (n-bleq 64
;;          (shifter 6 64 shift0 (shifter 6 64 shift1 reg))
;;          (shifter 7 64 (v-adder 6 t shift0 shift1) reg))
;;   :hints (("Goal" :clause-processor (:function sat :hint nil)))


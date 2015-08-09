
(in-package "ACL2")

;; (include-book "/projects/hvg/SULFA/books/sat/sat")

;; This file contains the examples from our paper that we
;; were able to prove using our SAT based hint.
;; The theorems are given in block comments, since our
;; SAT extension is not available without modifying the
;; ACL2 source code.

;; For a description of the example and a description of
;; how this relates to our SAT system see our workshop paper,
;; A SAT-Based Procedure for Verifying Finite State Machines in ACL2.

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

;; 4 Bit Adder Associativity
;; (thm
;;   (n-bleq 4 (v-adder 4 nil (v-adder 4 nil a b) c)
;;           (v-adder 4 nil a (v-adder 4 nil b c)))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

;; 32 bit adder associativity
;; (thm
;;  (n-bleq 32 (v-adder 32 nil (v-adder 32 nil a b) c)
;;          (v-adder 32 nil a (v-adder 32 nil b c)))
;;  :hints (("Goal" :external (sat nil sat::$sat))))

;; 200 Bit adder associativity
;; (thm
;;  (n-bleq 200 (v-adder 200 nil (v-adder 200 nil a b) c)
;;          (v-adder 200 nil a (v-adder 200 nil b c)))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

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

;; 32x6 Shift-0
;; (thm
;;  (implies
;;   (car (nth-cdr 5 shift0))
;;   (n-bleq 32
;;           (shifter 6 32 shift0 reg)
;;           (n-nills 32)))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

;; 64x7 Shift-0
;; (thm
;;  (implies
;;   (car (nth-cdr 6 shift0))
;;   (n-bleq 64 (shifter 7 64 shift0 reg)
;;           (n-nills 64)))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

;; 32x4 Add-shift
;; (thm
;;  (n-bleq 32
;;          (shifter 4 32 shift0 (shifter 4 32 shift1 reg))
;;          (shifter 5 32 (v-adder 4 nil shift0 shift1) reg))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

;; 64x6 Add-shift
;; (thm
;;  (n-bleq 64
;;          (shifter 6 64 shift0 (shifter 6 64 shift1 reg))
;;          (shifter 7 64 (v-adder 6 nil shift0 shift1) reg))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

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
      (not (consp x))
    (and (valid_digit (car x))
         (valid_digits (1- n) (cdr x)))))

;; 100 Digit Counter Invariant
;; (thm
;;  (implies
;;   (valid_digits 100 x)
;;   (valid_digits 100 (next_counter_state 100 x)))
;;   :hints (("Goal" :external (sat nil sat::$sat))))

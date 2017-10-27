; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "abs")
(include-book "computed-hints")
(include-book "o-real-p")
(include-book "nsa")

;; Enable abs, <-cancel-divisors and divisor cancellation as needed.

(in-theory (disable equal-cancel-divisors <-cancel-divisors))

(set-default-hints '((staged-hints stable-under-simplificationp
                                   nil ;;restart on new id
                                   '((:in-theory (enable abs
                                                         equal-cancel-divisors <-cancel-divisors)))
                                   nil nil 0)))

;; Macro defining non-negative real

(defmacro nneg-realp (r)
  `(and (realp ,r)
        (<= 0 ,r)))

;; Macro defining the constraint on the variable eps.
;; In this case, we require that 0 < eps <= 1/100.

(defmacro small-realp (eps)
  `(and (realp ,eps)
        (<= ,eps 1/100)
        (< 0 ,eps)))

;; Define accessor function for accessing particular variables
;; from the state X

(defun getPosReq (X)
  (nth 0 X))

(defun getPreset (X)
  (nth 1 X))

(defun getPos (X)
  (nth 2 X))

(defun getPosAo (X)
  (nth 3 X))

(defun getTmr (X)
  (nth 4 X))

;; Define a function which creates a system state, consisting
;; of the variables of the system.

(defun make-state (posReq preset pos posAo tmr)
  (list posReq preset pos posAo tmr))

;; Define theorems relating the accessor function and the make
;; state functions.

(defthm state-thm
  (and
   (equal (getPosReq (make-state posReq preset pos posAo tmr)) posReq)
   (equal (getPreset (make-state posReq preset pos posAo tmr)) preset)
   (equal (getPos (make-state posReq preset pos posAo tmr)) pos)
   (equal (getPosAo (make-state posReq preset pos posAo tmr)) posAo)
   (equal (getTmr (make-state posReq preset pos posAo tmr)) tmr)))

;; Disable the accessor functions and make-state function and rely upon the
;; rewrite rules associated with above theorem.

(in-theory (disable getPosReq getPreset getPos getPosAo getTmr
                    make-state))

;; StateP is a predicate which recognizes whether some variable is a
;; state variable.

(defun statep (x)
  (equal x
         (make-state (getPosReq x)
                     (getPreset x)
                     (getPos x)
                     (getPosAo x)
                     (getTmr x))))

;; The system assignment function, Y, includes the definition of the
;; computer program,
;; the floor function representing the analog to digital conversion,
;; and the reset of the timer variable.

(defun Y (X)
  (make-state
   (getPosReq x)
   (getPreset x)
   (getPos x)
   ;;posAo
   (cond
    ((> (- (floor1 (getPos X)) (getposReq X)) 2)
     (- (getposAo X) 5))
    ((< (- (floor1 (getPos X)) (getposReq X)) -3)
     (+ (getposAo X) 5))
    (t (getposAo X)))
   ;;tmr
   0))

;; The step definition of the physical system, including timer

(defun sigma (X eps)
  (make-state
   (getPosReq x)
   (getPreset x)
   ;;pos
   (cond
    ((> (getPos X) (getPosAo X))
     (- (getpos X) eps))
    ((< (getPos X) (getPosAo X))
     (+ (getpos X) eps))
    (t (getPos X)))
   (getposAo X)
   ;;tmr
   (+ (getTmr X) eps)))

(defun B-Y (X)
  (>= (getTmr X) (getPreset X)))

;; The system step function, as define by the single step function
;; sigma, the assignment function Y, and assignment predicate B-Y.

(defun sys-step (X eps)
  (cond
   ((B-Y X) (Y X))
   (t       (sigma X eps))))

;; The positive clamp function "clamps" the given r to a non-negative value.
;; If the value is negative, it returns zero. Otherwise, it returns
;; the given value.
;; It should be noted that the function is continuous in r.

(defun pos-clamp (r)
  (if (<= 0 r)
      r 0))

;; A component function of the overall measure m.
;; Intuitively, this measure function measures that the difference
;; between pos and posAo decreases over time.
;; This measure is 'active' when the difference between pos and
;; posAo is large.

(defun m1 (X eps)
  (cond
   ((<= (abs (- (getPosAo X) (getPos X)))
        (+ eps (pos-clamp (- (getPreset X) (getTmr X))))) 0)
   (t (+ 1 (/ (- (abs (- (getPosAo X) (getPos X)))
                 (+ (- (getPreset X) (getTmr X)) eps))
              eps)))))

;; A component function of the overall measure m.
;; Intuitively, this measure function measures that the difference
;; between posReq and posAo decreases over time.

(defun m2 (X eps)
  (declare (ignore eps))
  (if (and
       (<= (- (getPosAo X) (getPosReq X)) 3)
       (>= (- (getPosAo X) (getPosReq X)) -3))
      0
    (abs (- (getPosAo X) (getPosReq X)))))

;; A component function of the overall measure m.
;; Intuitively, this measure function measures that the difference
;; between pos and posAo decreases over time.
;; This measure is 'active' when the difference between pos and
;; posAo is small.

(defun m3 (X eps)
  (if (<= (abs (- (getPos X) (getPosAo X))) eps)
      0
    (/ (abs (- (getPos X) (getPosAo X))) eps)))

;; A component function of the overall measure m.
;; Intuitively, this measure function measures that the
;; timer changes in each step. This is useful for showing a
;; decreasing measure while the other system variables are unchanging.

(defun m4 (X eps)
  (cond
   ((< (getPreset X) (getTmr X)) 0)
   (t (+ 1 (/ (- (getPreset X) (getTmr X)) eps)))))

;; The overall measure function

(defun m (X eps)
  (cond ((and
          (< (m1 x eps) 1)
          (< (m2 x eps) 1))
         (make-ord 1 (+ 1 (m3 x eps))
                   (m4 x eps)))
        ((< (m1 x eps) 1)
         (make-ord 2 (+ 1 (m2 x eps))
                   (make-ord 1 (+ 1 (m3 x eps))
                             (m4 x eps))))
        (t (make-ord 3 (+ 1 (m1 x eps)) (m4 x eps)))))

;; Definition of the domain of the system variables and constants.

(defun valid-state (X eps)
  (and (realp (getPos X))
       (realp (getPreset X))
       (realp (getTmr X))
       (integerp (getPosAo X))
       (integerp (getPosReq X))
       (<= 51/10 (getPreset X))
       (<= 0 (getTmr x))
       (<= (getTmr x) (+ (getpreset x) eps))))

;; Cuong Chau: Disable the following control output setting.
;; (set-inhibit-output-lst '(proof-tree prove))

;; By requirement A1, we must show that if the assignment
;; predicate is satisfied in the current step, it is
;; not satisfied in the next step.

(defthm step-A1-thm
  (implies
   (and
    (valid-state x eps)
    (B-Y x))
   (not (B-Y (Y X))))
  :rule-classes nil)

;; Since the computer executes every delta time
;; period which is greater than preset, and since this
;; preset is a positive, standard number, then
;; to satisfy requirement A2, we must show that
;; the assignment function is limited if the
;; state variables are limited and satisfy B-Y.

(defthm step-A2-thm
  (implies
   (and
    (valid-state x eps)
    (B-Y x)
    (i-limited (getPosAo x))
    (i-limited (getTmr x))
    (i-limited (getPos x))
    (i-limited (getPreset x))
    (i-limited (getPosReq x)))
   (and
    (i-limited (getPosAo (Y x)))
    (i-limited (getTmr (Y x)))
    (i-limited (getPos (Y x)))
    (i-limited (getPreset (Y x)))
    (i-limited (getPosReq (Y x)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable i-large))))

; Added by Matt K.: Avoids rewriter loop in m1-lt-1.
(local (in-theory (disable commutativity-2-of-+)))

;; A theorem that states the formula (< (m1 x eps) 1) is equal
;; to the corresponding safety predicate
;; Hence, we will use the shorter formula
;; (< (m1 x eps) 1) in the remainder of this session.

(defthm m1-lt-1
  (implies
   (and
    (valid-state x eps)
    (small-realp eps))
   (iff (< (m1 x eps) 1)
        (<= (abs (- (getPosAo X) (getPos X)))
            (+ eps (pos-clamp (- (getPreset X) (getTmr X)))))))
  :rule-classes nil)

;; A theorem that states the formula (< (m2 x eps) 1) is equal
;; to the corresponding safety predicate
;; Hence, we will use the shorter formula (< (m2 x eps) 1)
;; in the remainder of this session.

(defthm m2-lt-1
  (implies
   (and
    (valid-state x eps)
    (small-realp eps))
   (iff (< (m2 x eps) 1)
        (and
         (<= (- (getPosAo X) (getPosReq X)) 3)
         (>= (- (getPosAo X) (getPosReq X)) -3))))
  :rule-classes nil)

;; Check that a valid state is an ordinal real

(defthm ordinal-real-thm
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (not (and
              (< (m1 x eps) 1)
              (< (m2 x eps) 1)
              (<= (abs (- (getpos x) (getPosReq x))) (+ 3 (* 2 eps))))))
   (o-real-p (m x eps))))

;; If we start in valid state, then next state also satisfies valid state

(defthm valid-state-preserve
  (implies
   (and (valid-state x eps)
        (small-realp eps))
   (valid-state (sys-step x eps) eps)))

;; The following theorem shows that once m1 < 1, then it remains so
;; similarly, once m2 < 1, it remains so. These results
;; are used to show that if m1 < 1 and m2 < 1, then
;; -3-eps <= (abs (- pos PosReq)) <= 3+eps is true
;; for all ensuing states.

(defthm m-1-preserve
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (< (m1 x eps) 1))
   (< (m1 (sys-step x eps) eps) 1))
  :rule-classes :linear)

(defthm m-2-preserve
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (< (m1 x eps) 1)
        (< (m2 x eps) 1))
   (< (m2 (sys-step x eps) eps) 1))
  :rule-classes :linear)

(defthm pos-posReq-preserve
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (< (m1 x eps) 1)
        (< (m2 x eps) 1)
        (<= (abs (- (getpos x) (getPosReq x))) (+ 3 (* 2 eps))))
   (<= (abs (- (getpos (sys-step x eps))
               (getposReq (sys-step x eps)))) (+ 3 (* 2 eps))))
  :rule-classes :linear)

(defthm safety-property-preserve
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (< (m1 x eps) 1)
        (< (m2 x eps) 1)
        (<= (abs (- (getpos x) (getPosReq x))) (+ 3 (* 2 eps))))
   (and
    (valid-state (sys-step x eps) eps) ;; Cuong Chau: I changed "(valid-state x
    ;; eps)" to "(valid-state (sys-step x eps) eps)"
    (< (m1 (sys-step x eps) eps) 1)
    (< (m2 (sys-step x eps) eps) 1)
    (<= (abs (- (getpos (sys-step x eps))
                (getposReq (sys-step x eps)))) (+ 3 (* 2 eps)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable sys-step valid-state m1 m2))
          ("Subgoal 2" :use ((:instance pos-posReq-preserve)))))

;; The measure is decreasing on the real ordinals, with
;; comparison o<-1

(defthm m-1-decreases
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (not (< (m1 x eps) 1)))
   (o<-1 (m (sys-step x eps) eps) (m x eps))))

(defthm m-2-decreases
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (< (m1 x eps) 1)
        (not (< (m2 x eps) 1)))
   (o<-1 (m (sys-step x eps) eps) (m x eps))))

(defthm m-decreases
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (not (and
              (< (m1 x eps) 1)
              (< (m2 x eps) 1)
              (<= (abs (- (getpos x) (getPosReq x))) (+ 3 (* 2 eps))))))
   (o<-1 (m (sys-step x eps) eps) (m x eps))))

;; Cuong Chau: Disable the following control output setting.
;; (set-inhibit-output-lst '(proof-tree))

(in-theory (disable o<-1 o-floor1 o-real-p sys-step valid-state m m1 m2 m3))

;; Fix m so that it always returns an ordinal

(defun m-fix (x eps)
  (cond
   ((not (and (valid-state x eps)
              (small-realp eps)
              (not (and
                    (< (m1 x eps) 1)
                    (< (m2 x eps) 1)
                    (<= (abs (- (getpos x) (getPosReq x)))
                        (+ 3 (* 2 eps)))))))
    0)
   (t (o-floor1 (m x eps)))))

;; m-fix is an ordinal

(defthm m-fix-o-p
  (o-p (m-fix x eps)))

;; sys-step decreases, using measure m-fix

(defthm m-fix-decreases
  (implies
   (and (valid-state x eps)
        (small-realp eps)
        (not (and
              (< (m1 x eps) 1)
              (< (m2 x eps) 1)
              (<= (abs (- (getpos x) (getPosReq x)))
                  (+ 3 (* 2 eps))))))
   (o< (m-fix (sys-step x eps) eps) (m-fix x eps))))

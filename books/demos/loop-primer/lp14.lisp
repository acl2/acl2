; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; Note: Do not be fooled into thinking the theorem prover is proving theorems
; about DO Loop$s inductively without help!  Most of these theorems are mere
; calculations on constants.  We state them as theorems just to confirm the
; calculation delivers the desired result.

; -----------------------------------------------------------------
; LP14-1

(defthm lp14-1-version-1
  (equal (loop$ with ans = nil
                with i = 10
                do
                (cond ((zp i)
                       (return (reverse (cons i ans))))
                      (t (progn (setq ans (cons i ans))
                                (setq i (- i 1))))))
         '(10 9 8 7 6 5 4 3 2 1 0))
  :rule-classes nil)

(defthm lp14-1-version-2
  (equal (loop$ with ans = nil
                with i = 0
                do
                :measure (nfix (- 10 i))
                (cond ((>= i 10)
                       (return (cons i ans)))
                      (t (progn (setq ans (cons i ans))
                                (setq i (+ i 1))))))
         '(10 9 8 7 6 5 4 3 2 1 0))
  :rule-classes nil)


; -----------------------------------------------------------------
; LP14-2

(defthm lp14-2
  (equal (loop$ with ans = 0
                with i = 100
                do
                (cond ((zp i)
                       (return ans))
                      (t (progn (setq ans (+ i ans))
                                (setq i (- i 1))))))
         5050)
  :rule-classes nil)

; -----------------------------------------------------------------
; LP14-3

(defun sq (x) (* x x))

(defwarrant sq)

(defthm lp14-3
  (implies (warrant sq)
           (equal (loop$ with ans = 0
                         with i = 100
                         do
                         (cond ((zp i)
                                (return ans))
                               (t (progn (setq ans (+ (sq i) ans))
                                         (setq i (- i 1))))))
                   338350))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP14-4

(defthm lp14-4
  (equal (loop$ with temp = '(a b c xxx d e f)
                do
                (cond
                 ((endp temp) (return nil))
                 ((equal (car temp) 'xxx) (return temp))
                 (t (setq temp (cdr temp)))))
         '(xxx d e f))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP14-5

(defun do-loop$-member (e lst)
  (loop$ with temp = lst
         do
         (cond
          ((endp temp) (return nil))
          ((equal (car temp) e) (return temp))
          (t (setq temp (cdr temp))))))

(defthm lp14-5
  (equal (do-loop$-member e lst)
         (member e lst))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP14-6

(defun steps-for-member (e lst steps)
  (cond ((endp lst) (list steps nil))
        ((equal (car lst) e) (list steps lst))
        (t (steps-for-member e (cdr lst) (+ 1 steps)))))

(defthm lp14-6
  (equal (loop$ with temp = lst
                with steps = steps
                do
                (cond
                 ((endp temp) (return (list steps nil)))
                 ((equal (car temp) e) (return (list steps temp)))
                 (t (progn (setq steps (+ 1 steps))
                           (setq temp (cdr temp))))))
         (steps-for-member e lst steps))
  :rule-classes nil)

; -----------------------------------------------------------------
; LP14-7

(defthm lp14-7
  (implies (warrant do$)
           (equal (loop$ with ans = nil
                         with i = 3
                         do
                         (cond
                          ((zp i) (return ans))
                          (t (progn
                               (setq ans
                                     (loop$ with ans = ans
                                            with j = 4
                                            do
                                            (cond
                                             ((zp j) (return ans))
                                             (t (progn
                                                  (setq ans
                                                        (cons (cons i j) ans))
                                                  (setq j (- j 1)))))))
                               (setq i (- i 1))))))
                  '((1 . 1)
                    (1 . 2)
                    (1 . 3)
                    (1 . 4)
                    (2 . 1)
                    (2 . 2)
                    (2 . 3)
                    (2 . 4)
                    (3 . 1)
                    (3 . 2)
                    (3 . 3)
                    (3 . 4))))
  :rule-classes nil)

; It might be less confusing if the inner loop$ were

; (loop$ with ans1 = ans
;        with j = 4
;        do
;        (cond ((zp j) (return ans1))
;              (t (progn (setq ans1 (cons (cons i j) ans1))
;                        (setq j (- j 1))))))

; But they are logically identical.


; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(loop$ for i in '(1 2 3 4) sum (* i i))

;;;;;

(loop$ with sum = 0 with lst = '(1 2 3 4) do
       (if (consp lst)
           (let ((sq (* (car lst) (car lst))))
             (progn (setq sum (+ sq sum))  ; sum := (+ sq sum)
                    (setq lst (cdr lst)))) ; lst := (cdr lst)
         (return sum)))

;;;;;

(include-book "projects/apply/top" :dir :system)
(defstobj st fld) (defwarrant fld) (defwarrant update-fld)
(loop$ with sum = 0 with lst = '(1 2 3 4) do
       :values (nil st)
       (if (consp lst)
           (let ((sq (* (car lst) (car lst))))
             (progn (mv-setq (sum st)
                             (let ((st (update-fld (cons sq (fld st)) st)))
                               (mv (+ sq sum) st)))
                    (setq lst (cdr lst))))
         (return (mv sum st))))
(fld st)

;;;;;

(loop$ with sum = 0 with i = 1 do
       :measure (nfix (- 5 i))
       (if (<= i 4)
           (let ((sq (* i i)))
             (progn (setq sum (+ sq sum)) (setq i (1+ i))))
         (loop-finish))
       finally (return sum)) ; returns 30

;;;;;

(defun f (n) ; (f 4) evaluates to 30
  (declare (xargs :guard (natp n)))
  (loop$ with sum of-type integer = 0 with i = n do
         :guard (natp i)
         (if (zp i)
             (return sum)
           (let ((sq (* i i)))
             (progn (setq sum (+ sq sum)) (setq i (1- i)))))))
(f 4) ; 30

(in-package "ACL2")

(include-book "lemgen")


(defun ilen (x a)
  (if (endp x)
      a
    (ilen (cdr x) (1+ a))))

(defun rot2 (i x)
  (if (endp i)
      x
    (rot2 (cdr i) (append (cdr x) (list (car x))))))

(defun rv1 (x a)
  (if (endp x)
      a
    (rv1 (cdr x) (cons (car x) a))))


(make-event

; Added by Matt K. after v5-0.  Apparently bprove doesn't call
; initialize-summary-accumulators, which is what invokes (time-tracker :tau
; :init ...).  So we take the easy way out here and turn off time-tracker
; during certification.  If someone decides to use bprove outside this
; directory, that person can figure out how to initialize the time-tracker for
; tag :tau as it's done in initialize-summary-accumulators.

 (prog2$ (time-tracker nil)
         (value '(value-triple nil))))

(bprove (equal (rv1 x 'nil) (rv x)))

(bprove (equal (ilen x '0) (len x)))

(bprove (implies (and (true-listp x)) (equal (rot2 x x) x)))

(bprove (implies (and (true-listp x) (true-listp y)) (equal (rot2 x (append x y)) (append y x))))


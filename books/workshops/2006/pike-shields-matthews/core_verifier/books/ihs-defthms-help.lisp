#|
  Book:    ihs-defthms-help
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#


(in-package "ACL2")

(include-book "source_shallow")

; Edited by Matt K.:
; (include-book "super-ihs" :dir :super-ihs)
(include-book "coi/super-ihs/super-ihs" :dir :system)


(defun log-rep-hlp (x i)
  (let ((val (if (logbitp i x) T NIL)))
  (if (zp i) (list val)
    (cons val (log-rep-hlp x (- i 1))))))

;; Lil' endian representation of x.
(defun log-rep (x)
  (let ((size (nbits x)))
    (if (zp size) (list NIL)
      (reverse (log-rep-hlp x (- size 1))))))

(defun nat-rep-hlp (bin-list i)
  (if (endp bin-list) 0
    (let ((val (if (nth i bin-list) 1 0)))
      (if (zp i) val
	(+ (* val
	      (expt2 i))
	   (nat-rep-hlp bin-list (- i 1)))))))

(defun nat-rep (bin-lst)
  (nat-rep-hlp bin-lst (- (len bin-lst) 1)))

;; Helper needed by iterators yielding bits
(defun c-update-bit (i b w)
  (let ((hi-bits (logtail (+ i 1) w)))
    (logapp i w (logapp 1 b hi-bits))))


  (defthmd loghead-0 (equal (loghead 0 i) 0))

  (defthm c-word--thm
    (implies (and (natp i)
                  (natp k)
                  (natp n)
                  (natp m)
                  (<= n m))
             (equal (loghead n (c-word-- m i k))
                    (loghead n (- i k))))
    :hints (("Goal" :in-theory (enable c-word--))))

  (defthm nat-rep-loghead-1
    (implies (natp i)
             (equal (nat-rep
                     (reverse
                      (list
                       (equal (loghead 1 i) 1))))
                    (loghead 1 i))))

(defthm less-loghead-expt
  (< (loghead j i) (expt2 j))
  :hints (("Goal" :in-theory (enable loghead-when-i-is-not-an-integerp))))


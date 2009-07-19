;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; mod-expt-fast.lisp
;;;
;;; This book is a modification of one submitted by Warren Hunt.  It
;;; contains an optimized version of mod-expt --- mod-expt-fast.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../basic-ops/top"))

(local
 (include-book "floor-mod-basic"))

(local
 (include-book "floor-mod"))

(local
 (include-book "more-floor-mod"))

(local
 (include-book "truncate-rem"))

(local
 (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
					       HIST PSPV))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Here is a recursive definition (* acc (mod (expt a i) n)):

(defun mod-expt-fast-1 (a i n acc)
  (declare (xargs :guard (and (integerp a)
                              (natp i)
                              (integerp n)
                              (< 0 n)
                              (integerp acc)
                              )))
  (if (zp i)
      acc
    ;; Divide by 2 using right shift
    (let ((floor-i-by-2 (ash i -1)))
      (if (oddp i)
	  (mod-expt-fast-1 (mod (* a a) n)
			     floor-i-by-2
			     n
			     (mod (* a acc) n))
	(mod-expt-fast-1 (mod (* a a) n)
			   floor-i-by-2
			   n
			   acc)))))

(defun mod-expt-fast (a i n)
  (declare (xargs :guard (and (rationalp a)
                              (integerp i)
                              (not (and (eql a 0) (< i 0)))
                              (<= 0 i)
                              (rationalp n)
                              (not (eql n 0)))))
  (if (and (integerp a) (integerp n) (< 0 n))
      (mod-expt-fast-1 a i n 1)
    (mod (expt a i) n)))

(local
 (defthm mod-expt-fast-is-mod-expt-helper
   (implies (and (integerp a)
		 (natp i)
		 (integerp n)
		 (< 0 n)
		 (natp acc)
		 (< acc n))
	    (equal (mod-expt-fast-1 a i n acc)
		   (mod (* acc (expt a i)) n)))))

(defthm mod-expt-fast-is-mod-expt
  (implies (and (rationalp a)
                (natp i)
                (integerp n)
                (< 1 n))
           (equal (mod-expt-fast a i n)
                  (mod-expt a i n))))

(in-theory (disable mod-expt-fast))

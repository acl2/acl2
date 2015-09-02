; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;
;; inequalities.lisp
;;

(in-package "ACL2")


(local (include-book "basic-arithmetic"))

(set-default-hints
 '((nonlinearp-default-hint-pass1 stable-under-simplificationp
                                  hist pspv)))


; ??? I'm not convinced we should be apply FC to RATIONALP hypotheses,
; but for now I'll go ahead and do so at times.

(defmacro fc (x)
  x)

;; I need iff-equal for the next batch of theorems up till
;; <-*-right-cancel (which is in fact proved in
;; inequalities-helper.lisp).

(local
 (defthm iff-equal
   (equal (equal (< w x) (< y z))
	  (iff (< w x) (< y z)))))

(defthm /-preserves-positive
  (implies (rationalp x)
	   (equal (< 0 (/ x))
		  (< 0 x))))

(defthm /-preserves-negative
  (implies (rationalp x)
	   (equal (< (/ x) 0)
		  (< x 0))))

(defthm <-0-minus
  (equal (< 0 (- x))
         (< x 0)))

(defthm <-minus-zero
  (equal (< (- x) 0)
         (< 0 x)))

(defthm <-minus-minus
  (equal (< (- x) (- y))
	 (< y x)))

(defthm <-0-+-negative-1
  (equal (< 0 (+ (- y) x))
         (< y x)))

(defthm <-0-+-negative-2
  (equal (< 0 (+ x (- y)))
         (< y x)))

(defthm <-+-negative-0-1
  (equal (< (+ (- y) x) 0)
         (< x y)))

(defthm <-+-negative-0-2
  (equal (< (+ x (- y)) 0)
         (< x y)))

(defthm <-*-0
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))

(defthm 0-<-*
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< 0 (* x y))
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< 0 x)
                          (< 0 y))))))

; The following two lemmas could be extended by adding two more such
; lemmas, i.e. for (< (* x z) (* z y)) and (< (* z x) (* y z)), but
; rather than incur that overhead here and in any other such cases
; (and besides, how about for example (< (* x z a) (* z a y))?), I'll
; wait for metalemmas to handle such things.

(local
 (in-arithmetic-theory '((:rewrite COMMUTATIVITY-OF-*))))

(defthm <-*-right-cancel
  (implies (and (fc (rationalp x))
		(fc (rationalp y))
                (fc (rationalp z)))
           (equal (< (* x z) (* y z))
		  (cond ((< 0 z) (< x y))
			((< z 0) (< y x))
			((equal z 0) nil)
			(t nil)))))

(defthm <-*-left-cancel
  (implies (and (fc (rationalp x))
		(fc (rationalp y))
                (fc (rationalp z)))
           (equal (< (* z x) (* z y))
		  (cond ((< 0 z) (< x y))
			((< z 0) (< y x))
			((equal z 0) nil)
			(t nil)))))

(defthm <-*-x-y-y
  (implies (and (fc (rationalp x))
		(fc (rationalp y)))
	   (equal (< (* x y) y)
		  (cond
                   ((< 0 y) (< x 1))
                   ((< y 0) (< 1 x))
                   ((equal y 0) nil)
		   (t nil)))))

(defthm <-*-y-x-y
  (implies (and (fc (rationalp x))
		(fc (rationalp y)))
	   (equal (< (* y x) y)
		  (cond
                   ((< 0 y) (< x 1))
                   ((< y 0) (< 1 x))
                   ((equal y 0) nil)
                   (t nil)))))

(defthm <-y-*-x-y
  (implies (and (fc (rationalp x))
		(fc (rationalp y)))
	   (equal (< y (* x y))
		  (cond
                   ((< 0 y) (< 1 x))
                   ((< y 0) (< x 1))
                   ((equal y 0) nil)
                   (t nil)))))

(defthm <-y-*-y-x
  (implies (and (fc (rationalp x))
		(fc (rationalp y)))
	   (equal (< y (* y x))
		  (cond
                   ((< 0 y) (< 1 x))
                   ((< y 0) (< x 1))
                   ((equal y 0) nil)
                   (t nil)))))

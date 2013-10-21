; pcode semantics (sort of)
;; semantics for relevant subset of pcode ops -- probably not correct

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun copy (x) x)

(defun int_xor (x y z)
  (mod (logxor x y) (expt 2 z)))

(defun int_equal (x y z)
  (if (= (mod x (expt 2 z))
	 (mod y (expt 2 z)))
      1 0))

(defun int_sless (x y z)
  (declare (ignore z))
  (if (< x y) 1 0))

(defun int_add (x y z)
  (mod (+ x y) (expt 2 z)))

(defun int_or (x y z)
  (mod (logior x y) (expt 2 z)))

(defun int_carry (x y z)
  (if (>= (+ x y) (expt 2 z))
      1 0))

(defun int_sub (x y z)
  (mod (- x y) (expt 2 z)))

(defun int_mult (x y z)
  (mod (* x y) (expt 2 z)))
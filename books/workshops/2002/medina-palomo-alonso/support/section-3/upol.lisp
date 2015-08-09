;;; ------------------------
;;; Unnormalized polynomials
;;; ------------------------

(in-package "UPOL")

(include-book "monomial")

;;; Recognizer.

(defun polynomialp (p)
  (declare (xargs :guard t))
  (if (atom p)
      (equal p nil)
    (and (monomialp (first p))
	 (polynomialp (rest p)))))

;;; Recognizer for objects in normal form.

(defun nfp (p)
  (declare (xargs :guard t))
  (if (atom p)
      (equal p nil)
    (and (consp (first p))
	 (not (MON::nullp (first p)))
	 (or (atom (rest p))
	     (and (consp (second p))
		  (MON::< (second p) (first p))))
	 (nfp (rest p)))))

;;; ...

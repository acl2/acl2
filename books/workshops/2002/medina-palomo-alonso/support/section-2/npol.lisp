;;; ----------------------
;;; Normalized polynomials
;;; ----------------------

(in-package "NPOL")

(include-book "upol-2")

;;; -----------
;;; Definitions
;;; -----------

(defun polynomialp (p)
  (and (UPOL::polynomialp p) (UPOL::nfp p)))

(defun + (p q)
  (UPOL::nf (UPOL::+ p q)))

(defun * (p q)
  (UPOL::nf (UPOL::* p q)))

(defun - (p)
  (UPOL::nf (UPOL::- p)))

(defun null ()
  (UPOL::null))

(defun identity ()
  (UPOL::identity))

;;; ----------
;;; Properties
;;; ----------

(defthm |p + q = q + p|
  (equal (+ p q) (+ q p)))

(defthm |(p + q) + r = p + (q + r)|
  (equal (+ (+ p q) r) (+ p (+ q r))))

(defthm |p * q = q * p|
  (equal (* p q) (* q p)))

(defthm |(p * q) * r = p * (q * r)|
  (equal (* (* p q) r) (* p (* q r))))

(defthm |p * (q + r) = (p * q) + (p * r)|
  (equal (* p (+ q r)) (+ (* p q) (* p r))))

(defthm |p + (- p) = 0|
  (equal (+ p (- p)) (null))
  :hints (("Goal" :in-theory (disable (null)))))

(defthm |0 + p = p|
  (implies (polynomialp p)
           (equal (+ (null) p) p))
  :hints (("Goal" :in-theory (disable (null)))))

(defthm |1 * p = p|
  (implies (polynomialp p)
           (equal (* (identity) p) p))
  :hints (("Goal" :in-theory (disable (identity)))))

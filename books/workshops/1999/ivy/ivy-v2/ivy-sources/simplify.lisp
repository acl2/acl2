(in-package "ACL2")

;; Function (simp-tf f) simplifies formulas by removing all
;; occurrences of 'true and 'false (except if the formula
;; becomes 'true or 'false).
;;
;; We prove a syntactic correctness theorem, a soundness theorem,
;; and some preservation-of-property theorems.

(include-book "stage")

;; ===========================================

(defun simp-tf (f)
  (declare (xargs :guard (wff f)))
  (cond
	((wfnot f)
         (let ((g (simp-tf (a1 f))))
           (cond ((equal g 'false) 'true)
                 ((equal g 'true) 'false)
                 (t (list 'not g)))))
	((wfand f)
         (let ((g1 (simp-tf (a1 f))) (g2 (simp-tf (a2 f))))
           (cond ((equal g1 'true) g2)
                 ((equal g2 'true) g1)
                 ((equal g1 'false) 'false)
                 ((equal g2 'false) 'false)
                 (t (list 'and g1 g2)))))
	((wfor f)
         (let ((g1 (simp-tf (a1 f))) (g2 (simp-tf (a2 f))))
           (cond ((equal g1 'false) g2)
                 ((equal g2 'false) g1)
                 ((equal g1 'true) 'true)
                 ((equal g2 'true) 'true)
                 (t (list 'or g1 g2)))))
	((wfimp f)
         (let ((g1 (simp-tf (a1 f))) (g2 (simp-tf (a2 f))))
           (cond ((equal g1 'false) 'true)
                 ((equal g1 'true) g2)
                 ((equal g2 'false) (list 'not g1))
                 ((equal g2 'true) 'true)
                 (t (list 'imp g1 g2)))))
	((wfiff f)
         (let ((g1 (simp-tf (a1 f))) (g2 (simp-tf (a2 f))))
           (cond ((equal g1 'true) g2)
                 ((equal g2 'true) g1)
		 ((and (equal g1 'false) (equal g2 'false)) 'true)
                 ((equal g1 'false) (list 'not g2))
                 ((equal g2 'false) (list 'not g1))
                 (t (list 'iff g1 g2)))))
	((wfquant f)
         (let ((g (simp-tf (a2 f))))
	   (if (or (equal g 'true) (equal g 'false))
	       g
	       (list (car f) (a1 f) g))))
	(t f)))

;; Prove that simp-tf preserves well-formedness.

(defthm simp-tf-wff
  (implies (wff f)
	   (wff (simp-tf f))))

;;------------------------------------------------------------
;; Function tf-free checks for occurrences of 'true and 'false.
;; (Move these 2 functions to wfftype.)

(defun tf-free (f)
  (declare (xargs :guard (wff f)))
  (cond ((or (equal f 'true) (equal f 'false)) nil)
	((wfnot f) (tf-free (a1 f)))
	((wfbinary f) (and (tf-free (a1 f)) (tf-free (a2 f))))
	((wfquant f) (tf-free (a2 f)))
	(t t)))

(defun tf-free-except-top (f)
  (declare (xargs :guard (wff f)))
  (or (equal f 'true)
      (equal f 'false)
      (tf-free f)))

;;------------------------------------------------------------
;; Prove the simp-tf gets rid of all occurrences of 'true and 'false.

(defthm simp-complete-1
  (implies (and (not (equal (simp-tf f) 'true))
		(not (equal (simp-tf f) 'false)))
	   (tf-free (simp-tf f))))

(defthm simp-complete-2
  (tf-free-except-top (simp-tf f)))

;;-----------------------
;; Soundness

(defthm not-equal-subst-true
  (implies (not (equal f 'true))
	   (not (equal (subst-free f x tm) 'true))))

(defthm not-equal-subst-false
  (implies (not (equal f 'false))
	   (not (equal (subst-free f x tm) 'false))))

(defthm subst-simp-tf-commute
  (equal (simp-tf (subst-free f x tm))
	 (subst-free (simp-tf f) x tm)))

(defthm simp-tf-xsound
  (equal (xeval (simp-tf f) dom i)
	 (xeval f dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

(defthm simp-tf-fsound
  (equal (feval (simp-tf f) i)
	 (feval f i))
  :hints (("Goal"
	   :in-theory (enable xeval-feval))))

;;------------------------------------
;; Some other properties of simp-tf

;; Note that simp-ft can eliminate free-vars.

(defthm simp-tf-doesnt-introduce-free-vars
  (subsetp-equal (free-vars (simp-tf f))
		 (free-vars f))
  :rule-classes nil)

(defthm simp-tf-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (simp-tf f))))
  :hints (("Goal"
	   :do-not-induct t
	   :use simp-tf-doesnt-introduce-free-vars)))

(defthm simp-tf-preserves-nnfp
  (implies (nnfp f)
           (nnfp (simp-tf f)))
  :hints (("Goal"
           :induct (nnfp f))))

(in-package "ACL2")

;; This book is a little add-on to Ivy.  I imagine there will
;; times when we wish to simply check a proof object, without
;; using Ivy's preprocessing.  For example, if a prover
;; can build proof objects, but it is inconvenient to use
;; Ivy's preprocessing.
;;
;; Function (bcheck proof) below checks if its input is a proof
;; object, fixes the substitutions (just like refute-n-check),
;; and checks it.  Ths soundness theorems says that if the
;; input steps are true, then all the steps are true.
;;
;; Bcheck is similar to the checker of our 1994 Nqthm project.
;; (But we didn't have any soundness proofs back then.)

(include-book "derive")

;; Here is the checker function.  Compare it to refute-n-check
;; in book "derive".

(defun bcheck (prf)
  (declare (xargs :guard t))
  (if (not (wfproof prf))
      nil
    (let ((fixed-prf (fix-substs-in-prf
		      prf
		      (free-vars (extract-all-steps prf)))))
      (check-proof nil fixed-prf))))

;; Question to us: why weren't the following two lemmas needed
;; for soundness of refute-n-check?

(defthm extract-all-fixed
  (equal (extract-all-steps (fix-substs-in-prf prf vars))
	 (extract-all-steps prf)))

(defthm extract-input-fixed
  (equal (extract-input-steps (fix-substs-in-prf prf vars))
	 (extract-input-steps prf)))

;; Luckily, we can use theorem check-proof-xsound which we
;; used for soundness of refute-n-check.

(defthm bcheck-xsound
  (implies
   (and (bcheck prf)
	(xeval (universal-closure (extract-input-steps prf)) (domain i) i))
   (xeval (universal-closure (extract-all-steps prf)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance check-proof-xsound
			    (prf (fix-substs-in-prf
				  prf
				  (free-vars (extract-all-steps prf))
				  )))))))

;; Now state it in terms of the official evaluation function feval.

(defthm bcheck-fsound
  (implies (and (bcheck prf)
		(feval (universal-closure (extract-input-steps prf)) i))
	   (feval (universal-closure (extract-all-steps prf)) i))
  :hints (("Goal"
	   :in-theory (enable xeval-feval)
	   :do-not-induct t)))


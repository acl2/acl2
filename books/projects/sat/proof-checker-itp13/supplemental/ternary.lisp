(in-package "PROOF-CHECKER-ITP13")


;; ===================================================================
;; ========================== TERNARY LOGIC ==========================


(defun truep (x) 
  (declare (xargs :guard t))
  (equal x 't))

(defun falsep (x) 
  (declare (xargs :guard t))
  (equal x 'f))

(defun undefp (x) 
  (declare (xargs :guard t))
  (equal x 'undef))

(defun true ()
  (declare (xargs :guard t))
  't)

(defun false ()
  (declare (xargs :guard t))
  'f)

(defun undef ()
  (declare (xargs :guard t))
  'undef)


(defthm truep-true
  (truep (true)))

(defthm falsep-false
  (falsep (false)))

(defthm undefp-undef
  (undefp (undef)))

(defthm truep-implies-not-falsep
 (implies (truep x)
          (not (falsep x))))

(defthm truep-implies-not-undefp
 (implies (truep x)
          (not (undefp x))))

(defthm falsep-implies-not-truep
 (implies (falsep x)
          (not (truep x))))

(defthm falsep-implies-not-undefp
 (implies (falsep x)
          (not (undefp x))))

(defthm undefp-implies-not-falsep
 (implies (undefp x)
          (not (falsep x))))

(defthm undefp-implies-not-truep
 (implies (undefp x)
          (not (truep x))))


(in-theory (disable truep
                    falsep
                    undefp
                    true
                    false
                    undef
                    (:executable-counterpart truep)
                    (:executable-counterpart falsep)
                    (:executable-counterpart undefp)
                    (:executable-counterpart true)
                    (:executable-counterpart false)
                    (:executable-counterpart undef)
                    (:type-prescription truep)
                    (:type-prescription falsep)
                    (:type-prescription undefp)
                    (:type-prescription true)
                    (:type-prescription false)
                    (:type-prescription undef)))


;; ===================================================================
;; ============================= TERNARY =============================

(defun ternaryp (x)
  (declare (xargs :guard t))
  (or (truep x)
      (falsep x)
      (undefp x)))


(defthm ternaryp-true
  (ternaryp (true)))

(defthm ternaryp-false
  (ternaryp (false)))

(defthm ternaryp-undef
  (ternaryp (undef)))


; These rules may cause problems.  Comment them out if there are problems.
(defthm ternaryp-not-true-not-undef
  (implies (and (ternaryp x)
                (not (truep x))
                (not (undefp x)))
           (falsep x)))

(defthm ternaryp-not-true-not-false
  (implies (and (ternaryp x)
                (not (truep x))
                (not (falsep x)))
           (undefp x)))

(defthm ternaryp-not-false-not-undef
  (implies (and (ternaryp x)
                (not (falsep x))
                (not (undefp x)))
           (truep x)))


(in-theory (disable ternaryp))



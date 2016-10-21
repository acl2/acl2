(in-package "PROOF-CHECKER-ARRAY")

(include-book "literal")
(include-book "sets")

;; ===================================================================
;; ============================= UNIQUEP =============================

; Not used.

;; (defun uniquep (x)
;;   (declare (xargs :guard (eqlable-listp x)))
;;   (if (atom x)
;;       t
;;     (and (not (member (car x) (cdr x)))
;;          (uniquep (cdr x)))))


;; ===================================================================
;; =========================== PREDICATES ============================

(defun unique-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      t
    (and (not (member (car x) (cdr x)))
         (unique-literalsp (cdr x)))))

(defun no-conflicting-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      t
    (and ;(not (member (car x) (cdr x))) ; only check for conflicting
         (not (member (negate (car x)) (cdr x)))
         (no-conflicting-literalsp (cdr x)))))



;; ===================================================================
;; =========================== OPERATIONS ============================

(defun remove-duplicate-literals (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      nil
    (if (member (car x) (cdr x))
        (remove-duplicate-literals (cdr x))
      (cons (car x)
            (remove-duplicate-literals (cdr x))))))


(defthm member-remove-duplicate-literals
  (iff (member e (remove-duplicate-literals x))
       (member e x)))

(defthm unique-literalsp-remove-duplicate-literals
  (unique-literalsp (remove-duplicate-literals x)))

(defthm literal-listp-remove-duplicate-literals
  (implies (literal-listp x)
           (literal-listp (remove-duplicate-literals x))))

(defthm no-conflicting-literalsp-remove-duplicate-literals
  (implies (no-conflicting-literalsp x)
           (no-conflicting-literalsp (remove-duplicate-literals x))))


;; ===================================================================

(defun remove-conflicting-literals (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      nil
    (if (member (negate (car x)) (cdr x))
        (remove-conflicting-literals (cdr x))
      (cons (car x)
            (remove-conflicting-literals (cdr x))))))



; it would be nice to combine this into a iff lemma

(defthm not-member-remove-conflicting-literals
  (implies (not (member e x))
           (not (member e (remove-conflicting-literals x)))))


(defthm member-remove-conflicting-literals2
  (implies (and (member e x)
                (not (member (negate e) x)))
           (member e (remove-conflicting-literals x))))

(defthm member-remove-conflicting-literals3
  (implies (and (literalp e)
                (member e x)
                (not (member (negate e) (remove-conflicting-literals x))))
           (member e (remove-conflicting-literals x))))



(defthm no-conflicting-literalsp-remove-conflicting-literals
  (no-conflicting-literalsp (remove-conflicting-literals x)))

(defthm literal-listp-remove-conflicting-literals
  (implies (literal-listp x)
           (literal-listp (remove-conflicting-literals x))))

(defthm unique-literalsp-remove-conflicting-literals
  (implies (unique-literalsp x)
           (unique-literalsp (remove-conflicting-literals x))))



;; ===================================================================
;; ===================================================================

(defthm unique-literalsp-union-variables
  (implies (unique-literalsp x)
           (unique-literalsp (union-variables x y))))

(defthm no-conflicting-literalsp-union-variables
  (implies (no-conflicting-literalsp x)
           (no-conflicting-literalsp (union-variables x y))))

(defthm subsetp-remove-duplicate-literals
  (equal (subsetp x (remove-duplicate-literals y))
         (subsetp x y)))

(defthm subsetp-list-remove-duplicate-literals
  (equal (subsetp-list x (remove-duplicate-literals y))
         (subsetp-list x y)))


;; ===================================================================
;; ===================================================================

(defthm not-no-conflicting-literalsp
  (implies (and (member e x)
                (member (negate e) x)
                (literalp e))
           (not (no-conflicting-literalsp x))))


(encapsulate
 ()
 (local 
  (defun find-negated-literal (x y)
    (declare (xargs :guard (and (literal-listp x)
                                (literal-listp y))))
    (if (atom x)
        nil
      (if (member (negate (car x)) y)
          (car x)
        (find-negated-literal (cdr x) y)))))

 (local
  (defthm subset-variablesp-not-subsetp-implies-find-negated-literal
    (implies (and (subset-variablesp x y)
                  (not (subsetp x y))
                  (literal-listp x))
             (find-negated-literal x y))))
 (local
  (defthm find-negated-literal-implies-member
    (implies (find-negated-literal x y)
             (member (find-negated-literal x y) x))))
 (local
  (defthm find-negated-literal-implies-member-negate
    (implies (find-negated-literal x y)
             (member (negate (find-negated-literal x y)) y))))
 (local
  (defthm subset-variablesp-not-subsetp-implies-member-find-negated-literal
    (implies (and (subset-variablesp x y)
                  (not (subsetp x y))
                  (literal-listp x)
                  )
             (and (member (find-negated-literal x y) x)
                  (member (negate (find-negated-literal x y)) y)))))

 (defthm subset-variablesp-not-subsetp-implies-not-no-conflicting-literalsp
   (implies (and (subset-variablesp x y)
                 (not (subsetp x y))
                 (literal-listp x)
                 (subsetp y x))
            (not (no-conflicting-literalsp x)))
   :hints (("Goal"
            :use ((:instance
                   subset-variablesp-not-subsetp-implies-member-find-negated-literal)
                  (:instance subsetp-member-implies-member
                             (x y) (y x) (e (find-negated-literal x y)))
                  (:instance not-no-conflicting-literalsp
                             (e (find-negated-literal x y)))))))
 )



(defthm subset-variablesp-remove-conflicting-literals1
  (implies (literal-listp x)
           (subset-variablesp x (remove-conflicting-literals x))))

(defthm subset-variablesp-remove-conflicting-literals2
  (subset-variablesp (remove-conflicting-literals x) x))


(defthm subset-variablesp-and-subsetp-implies-subsetp
  (implies (and (subset-variablesp x y)
                (subsetp y x)
                (literal-listp x)
                ;(literal-listp y)
                (no-conflicting-literalsp x)
                ;(no-conflicting-literalsp y)
                )
           (subsetp x y)))

(defthm subsetp-and-set-equal-variablesp-implies-subsetp
  (implies (and (set-equal-variablesp x y) ;necessary?
                (subsetp y x)
                (literal-listp x)
                ;(literal-listp y)
                (no-conflicting-literalsp x)
                ;(no-conflicting-literalsp y)
                )
           (subsetp x y)))

(defthm subsetp-and-set-equal-variablesp-implies-set-equalp
  (implies (and (set-equal-variablesp x y)
                (literal-listp x)
                (no-conflicting-literalsp x)
                (no-conflicting-literalsp y)
                (literal-listp y)
                (subsetp x y))
           (set-equalp x y)))

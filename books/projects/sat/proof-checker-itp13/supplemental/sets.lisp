(in-package "PROOF-CHECKER-ITP13")

(include-book "literal")

;; ===================================================================
;; ============================= SUBSETP =============================

(defun subsetp (x y)
  (declare (xargs :guard (and (eqlable-listp y)
                              (eqlable-listp x))))
  (cond
   ((endp x) t)
   ((member (car x) y)
    (subsetp (cdr x) y))
   (t nil)))


(defthm subsetp-cdr
  (implies (subsetp x (cdr y))
           (subsetp x y)))


(defthm subsetp-member-implies-member
  (implies (and (subsetp x y)
                (member e x))
           (member e y))
  );:rule-classes :forward-chaining)

(defthm subsetp-append
  (and (subsetp x (append x y))
       (subsetp y (append x y))))

(defthm subsetp-implies-subsetp-append
  (implies (subsetp x y)
           (subsetp x (append z y))))


; is it better to eliminate this?
(defun set-equalp (x y)
  (declare (xargs :guard (and (eqlable-listp x)
                              (eqlable-listp y))))
  (and (subsetp x y)
       (subsetp y x)))


(defun union (x y)
  (declare (xargs :guard (and (eqlable-listp x)
                              (eqlable-listp y))))
  (if (atom x)
      y
    (if (member (car x) y)
        (union (cdr x) y)
      (cons (car x) (union (cdr x) y)))))


;; ===================================================================
;; ======================== SUBSET-VARIABLESP ========================

(defun subset-variablesp (x y)
  (declare (xargs :guard (and (literal-listp x)
                              (literal-listp y))))
  (if (atom x)
      t
    (if (and (not (member (car x) y))
             (not (member (negate (car x)) y)))
        nil
      (subset-variablesp (cdr x) y))))

        
(defthm subset-variablesp-implies-member-or-member-negate
 (implies (and (subset-variablesp x y)
               (member e x)
               (not (member e y)))
          (member (negate e) y)))

(defthm subset-variablesp-cons
  (implies (subset-variablesp x y)
           (subset-variablesp x (cons e y))))

(defthm subset-variablesp-append
  (iff (subset-variablesp (append x y) z)
       (and (subset-variablesp x z)
            (subset-variablesp y z))))


(defun set-equal-variablesp (x y)
  (declare (xargs :guard (and (literal-listp x)
                              (literal-listp y))))
  (and (subset-variablesp x y)
       (subset-variablesp y x)))


;; ===================================================================
;; ==================== SET-DIFFERENCE-VARIABLES =====================

(defun set-difference-variables (x y)
  (declare (xargs :guard (and (literal-listp x)
                              (literal-listp y))))
  (if (atom x)
      nil
    (if (and (not (member (car x) y))
             (not (member (negate (car x)) y)))
        (cons (car x)
              (set-difference-variables (cdr x) y))
      (set-difference-variables (cdr x) y))))


(defthm equal-set-difference-variables-cons
  (implies (and (literalp e)
                (not (member e x))
                (not (member (negate e) x)))
           (equal (set-difference-variables x (cons e y))
                  (set-difference-variables x y))))

(defthm not-set-difference-variables-implies-subset-variablesp
  (implies (not (set-difference-variables x y))
           (subset-variablesp x y)))

(defthm member-set-difference-variables
  (iff (member e (set-difference-variables x y))
       (and (member e x)
            (not (member e y))
            (not (member (negate e) y)))))

(defthm subsetp-set-difference-variables
  (subsetp (set-difference-variables x y) x))

(defthm subset-variablesp-set-difference-variables
  (implies (subset-variablesp x z)
           (subset-variablesp (set-difference-variables x y) z)))


;; ===================================================================
;; ========================= UNION-VARIABLES =========================

; this is intersect, change it
(defun union-variables (x y)
  (declare (xargs :guard (and (literal-listp x)
                              (literal-listp y))))
  (if (atom x)
      nil
    (if (or (member (car x) y)
            (member (negate (car x)) y))
        (cons (car x)
              (union-variables (cdr x) y))
      (union-variables (cdr x) y))))


; forward chaining?
(defthm member-union-variables1
  (implies (member e (union-variables x y))
           (member e x)))

(defthm member-union-variables2
  (implies (and (member e x)
                (member e y))
           (member e (union-variables x y))))

(defthm member-union-variables3
  (implies (and (member e x)
                (member (negate e) y))
           (member e (union-variables x y))))

(defthm subsetp-union-variables
  (subsetp (union-variables x y) x))

(defthm subset-variablesp-union-variables
  (subset-variablesp (union-variables x y) y))

(defthm literal-listp-union-variables
  (implies (literal-listp x)
           (literal-listp (union-variables x y))))


;; ===================================================================
;; ========================== SUBSETP-LIST ===========================

(defun eqlable-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (eqlable-listp (car x))
         (eqlable-list-listp (cdr x)))))

(defun subsetp-list (x y)
  (declare (xargs :guard (and (eqlable-list-listp x)
                              (eqlable-listp y))))
  (if (atom x)
      t
    (and (subsetp (car x) y)
         (subsetp-list (cdr x) y))))


(defthm subsetp-list-append
  (implies (subsetp-list x y)
           (subsetp-list x (append z y))))


;; ===================================================================
;; ===================================================================


(defthm member-and-not-member-implies-not-subset-variablesp
  (implies (and (member e x)
                (not (member e y))
                (not (member (negate e) y)))
           (not (subset-variablesp x y))))

(defthm subset-variablesp-transitive
  (implies (and (subset-variablesp x y)
                (subset-variablesp y z)
                (literal-listp x))
           (subset-variablesp x z)))

(defthm set-equal-variablesp-transitive
  (implies (and (set-equal-variablesp x y)
                (set-equal-variablesp y z)
                (literal-listp x)
                (literal-listp z))
           (set-equal-variablesp x z)))













;; ===================================================================
;; ===================================================================


; set-equal disabled with forward chaining for subset

;; (defthm set-equalp-implies-subsetp-and-subsetp
;;   (implies (set-equalp x y)
;;            (and (subsetp x y)
;;                 (subsetp y x)))
;;   :rule-classes :forward-chaining)

;; (in-theory (disable set-equalp))

;; (defthm set-equal-variablesp-implies-subset-variablesp-and-subset-variablesp
;;   (implies (set-equal-variablesp x y)
;;            (and (subset-variablesp x y)
;;                 (subset-variablesp y x)))
;;   :rule-classes :forward-chaining)

;; (in-theory (disable set-equal-variablesp))

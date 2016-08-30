(in-package "PROOF-CHECKER-ITP13")

;; ===================================================================
;; ============================ VARIABLES ============================

; Consider posp
(defun variablep (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (< 0 x)))


;; ===================================================================
;; ============================ LITERALS =============================

(defun literalp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (equal x 0))))


(defthm literalp-implies-eqlablep
  (implies (literalp x)
           (eqlablep x)))


;; ===================================================================
;; ========================== LITERAL-LIST ===========================

(defun literal-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (literalp (car x))
         (literal-listp (cdr x)))))


(defthm literal-listp-implies-eqlable-listp
  (implies (literal-listp x)
           (eqlable-listp x)))

(defthm literal-listp-implies-literalp-member
  (implies (and (literal-listp x)
                (member e x))
           (literalp e)))

(defthm literal-listp-append
  (implies (and (literal-listp x)
                (literal-listp y))
           (literal-listp (append x y))))


;; ===================================================================
;; ============================ NEGATION =============================

(defun negatedp (x)
  (declare (xargs :guard (literalp x)))
  (< x 0))

(defun negate (x)
  (declare (xargs :guard (literalp x)))
  (- x))


(defthm literalp-negate
  (equal (literalp (negate x))
         (literalp x)))

(defthm literalp-implies-not-equal-negate
  (implies (literalp x)
           (not (equal (negate x) x))))

(defthm negate-negate
  (implies (literalp x)
           (equal (negate (negate x))
                  x)))


;; ===================================================================
;; ============================ DISABLES =============================

(in-theory (disable variablep
                    literalp
                    ;literal-listp
                    negatedp
                    negate
                    ;literal-to-variable
                    ;variable-to-natural
                    ;natp ; needed to prevent acl2 from going crazy
                    ))

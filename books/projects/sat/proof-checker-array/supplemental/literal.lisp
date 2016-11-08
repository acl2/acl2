(in-package "PROOF-CHECKER-ARRAY")

(include-book "sb60")

;; ===================================================================
;; ============================ VARIABLES ============================

(defconst *2^58* (expt 2 58))
(defconst *2^59* (expt 2 59))
(defconst *2^60* (expt 2 60))

;; (signed-byte-p 60 x) --> (- *2^59*) <= x < *2^59*
;; *2^59* even, last literal should be odd because of pairing 0 0 1 -1 2 -2
;; (literalp x) --> 2 <= x <= (1- *2^59*) <--> < *2^59*
;; (encode x) = (if (< x 0) (1+ (* 2 (abs x))) (* 2 x))
;; (variablep x) --> 1 <= x <= (- *2^58* 2) <--> < (1- *2^58*)

(defun variablep (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (< 0 x)
       (< x (1- *2^58*))))


;; ===================================================================
;; ============================ LITERALS =============================

(defun literalp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (< 1 x)
       (< x *2^59*)))


(defthm literalp-implies-eqlablep
  (implies (literalp x)
           (eqlablep x)))

(defthm literalp-implies-sb60p
  (implies (literalp lit)
           (sb60p lit))
  :rule-classes :forward-chaining)


(defthm literalp-implies-<-2
  (implies (literalp lit)
           (< 1 lit))
  :rule-classes :forward-chaining)


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
  (logand x 1))

(defun negate (x)
  (declare (xargs :guard (literalp x)))
  (logxor x 1))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm literalp-negate
   (equal (literalp (negate x))
          (literalp x)))

 (defthm literalp-implies-not-equal-negate
   (implies (literalp x)
            (not (equal (negate x) x))))

 (defthm negate-negate
   (implies (literalp x)
            (equal (negate (negate x))
                   x))))



(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm literalp-implies-sb60p-negate
   (implies (literalp lit)
            (sb60p (negate lit)))))


;; ===================================================================

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm equal-negate-1+
   (implies (and (literalp lit)
                 (evenp lit))
            (equal (negate lit)
                   (1+ lit))))
 (in-theory (disable equal-negate-1+))

 (defthm equal-1+-negate
   (implies (and (literalp lit)
                 (evenp lit))
            (equal (1+ lit)
                   (negate lit))))
 (in-theory (disable equal-1+-negate))

 (defthm equal-negate-1-
   (implies (and (literalp lit)
                 (oddp lit))
            (equal (negate lit)
                   (1- lit))))
 (in-theory (disable equal-negate-1-))
 
 (defthm evenp-implies-<-negate
   (implies (and (literalp lit)
                 (integerp x)
                 (evenp x)
                 (< lit x))
            (< (negate lit) x))
   :hints (("Goal"
            :cases ((evenp lit)))))

 (defthm <=-0-negate
   (implies (literalp lit)
            (<= 0 (negate lit)))))


;; ===================================================================
;; ============================ DISABLES =============================

(in-theory (disable variablep
                    literalp
                    negatedp
                    negate
                    ))

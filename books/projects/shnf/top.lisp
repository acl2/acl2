;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")

(include-book "rtl/rel11/lib/basic" :dir :system)

(set-enforce-redundancy t)

(local (include-book "support"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; This book is a formalization of the theory of sparse Horner normal form for
;; integer polynomials.  For documentation see www.russinoff.com/papers/shnf.pdf.

;;*********************************************************************************
;;                              Polynomial Terms
;;*********************************************************************************

;; A polynomial term over a list of variables:

(defn distinct-symbols (vars)
  (if (consp vars)
      (and (distinct-symbols (cdr vars))
           (symbolp (car vars))
           (not (member (car vars) (cdr vars))))
    (null vars)))

(defun polyp (x vars)
  (declare (xargs :guard (distinct-symbols vars)))
  (if (atom x)
      (or (integerp x) (member x vars))
    (and (true-listp x)
         (case (len x)
           (2 (let ((y (cadr x)))
                (case (car x)
                  (- (polyp y vars)))))
           (3 (let ((y (cadr x)) (z (caddr x)))
                (case (car x)
                  (+ (and (polyp y vars) (polyp z vars)))
                  (- (and (polyp y vars) (polyp z vars)))
                  (* (and (polyp y vars) (polyp z vars)))
                  (expt (and (polyp y vars) (natp z))))))))))

;; Evaluation of a polynomial term:

(defun evalp (x alist)
  (if (integerp x)
      x
    (if (atom x)
        (cdr (assoc x alist))
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (+ (evalp y alist) (evalp z alist)))
          (- (if (cddr x) (- (evalp y alist) (evalp z alist)) (- (evalp y alist))))
          (* (* (evalp y alist) (evalp z alist)))
          (expt (expt (evalp y alist) (evalp z alist))))))))

(defn all-integers (vals)
  (if (consp vals)
      (and (all-integers (cdr vals))
           (integerp (car vals)))
    (null vals)))

(defthm integerp-evalp
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (polyp x vars))
           (integerp (evalp x (pairlis$ vars vals))))
  :rule-classes ())

;; As a matter of curiosity, it will be interesting to count the monomials
;; that would result from the expansion of a term:

(defun mono-count (x)
  (if (atom x)
      1
    (let ((y (cadr x)) (z (caddr x)))
      (case (car x)
        (+ (+ (mono-count y) (mono-count z)))
        (- (if (cddr x) (+ (mono-count y) (mono-count z)) (mono-count y)))
        (* (* (mono-count y) (mono-count z)))
        (expt (expt (mono-count y) z))))))

;;*********************************************************************************
;;                            Sparse Horner Form
;;*********************************************************************************

;; A sparse Horner form (SHF) is any of the following:
;;    (1) An integer
;;    (2) A list (POP i p), where i is a nat and p is a SHF
;;    (3) A list (POW i p q), where i is a nat and p and q are SHFs

(defn shfp (x)
  (if (atom x)
      (integerp x)
    (case (car x)
      (pop (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (shfp (caddr x))
                (null (cdddr x))))
      (pow (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (shfp (caddr x))
                (consp (cdddr x)) (shfp (cadddr x))
                (null (cddddr x)))))))

;; Thus, a SHF is a tree.  This function counts its nodes:

(defun shf-count (x)
  (if (atom x)
      1
    (case (car x)
      (pop (+ 2 (shf-count (caddr x))))
      (pow (+ 2 (shf-count (caddr x)) (shf-count (cadddr x))))
      (t 0))))

;; A SHF represents a polynomial term relative to an ordering of variables.
;; We shall define a procedure that derives a SHF x from a term z and show
;; that the value of z may be computed by the function evalh as defined
;; below.  That is, if vars is the ordered list of variables and vals is a
;; list of corresponding values, then

;;      (evalh x vals) = (evalp z (pairlis vars vals)).

(defun evalh (x vals)
  (declare (xargs :guard (and (shfp x)
                              (all-integers vals))))
  (if (atom x)
      x
    (case (car x)
      (pop (evalh (caddr x) (nthcdr (cadr x) vals)))
      (pow (+ (* (expt (if (consp vals) (car vals) 0) (cadr x))
                 (evalh (caddr x) vals))
             (evalh (cadddr x) (cdr vals)))))))

(defthm integerp-evalh
  (implies (and (shfp x)
                (all-integers vals))
           (integerp (evalh x vals)))
  ;; [Jared] removed the :type-prescription rule because accumulated persistence
  ;; says it's expensive and the hyps don't look type-prescription like.
  ;;:rule-classes (:type-prescription :rewrite)
  )

;; A SHF x is normal if the following conditions hold:
;;    (1) x = (POP i p) => p is a POW
;;    (2) x = (POW i p q) => p neither 0 nor (POW j r 0)

(defund shf-normp (x)
  (declare (xargs :guard (shfp x)))
  (if (atom x)
      t
    (let ((i (cadr x)) (p (caddr x)) (q (cadddr x)))
      (case (car x)
        (pop (and (not (= i 0))
                  (consp p)
                  (eql (car p) 'pow)
                  (shf-normp p)))
        (pow (and (not (= i 0))
                  (shf-normp p)
                  (shf-normp q)
                  (if (atom p)
                      (not (= p 0))
                    (not (and (eql (car p) 'pow)
                              (equal (cadddr p) 0))))))))))

(defnd shnfp (x)
  (and (shfp x) (shf-normp x)))

(defthm shnfp-shfp
  (implies (shnfp x)
           (shfp x))
  ;; [Jared] trying to cheapen this very expensive rule.
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm shnfp-pow-q
  (implies (and (shnfp x) (eql (car x) 'pow))
           (shnfp (cadddr x))))

(defthm shnfp-pow-p
  (implies (and (shnfp x) (eql (car x) 'pow))
           (shnfp (caddr x))))

(defthm shfp-pop-pow-atom
  (implies (and (shfp x) (not (eql (car x) 'pow)) (not (eql (car x) 'pop)))
           (atom x)))

(defthm shnfp-int
  (implies (integerp x)
           (shnfp x)))

;;*********************************************************************************
;;                        Converting a Polynomial to SHNF
;;*********************************************************************************

;; We shall define a function norm that computes a SHNF
;; representing a polynomial with respect to a given variable ordering.

;; norm-pop normalizes (POP i p), where p is normal:

(defund norm-pop (i p)
  (declare (xargs :guard (and (natp i)
                              (shnfp p))))
  (if (or (= i 0) (atom p))
      p
    (if (eql (car p) 'pop)
        (list 'pop (+ i (cadr p)) (caddr p))
      (list 'pop i p))))

(defthm norm-pop-shnfp
  (implies (and (shnfp p) (natp i))
           (shnfp (norm-pop i p))))

(defthm norm-pop-normp
  (implies (and (shnfp p) (natp i))
           (shf-normp (norm-pop i p))))

(defthm norm-pop-shfp
  (implies (and (shnfp p) (natp i))
           (shfp (norm-pop i p))))

(defthm norm-pop-evalh
  (implies (and (shnfp p) (natp i))
           (equal (evalh (norm-pop i p) n)
                  (evalh `(pop ,i ,p) n))))

;; norm-pow normalizes (POW i p q), where p and p are normal:

(defund norm-pow (i p q)
  (declare (xargs :guard (and (natp i)
                              (shnfp p)
                              (shnfp q))))
  (if (equal p 0)
      (norm-pop 1 q)
    (if (and (consp p) (eql (car p) 'pow) (equal (cadddr p) 0))
        (list 'pow (+ i (cadr p)) (caddr p) q)
      (list 'pow i p q))))

(defthm norm-pow-shnfp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shnfp (norm-pow i p q))))

(defthm norm-pow-normp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shf-normp (norm-pow i p q))))

(defthm norm-pow-shfp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shfp (norm-pow i p q))))

(defthm norm-pow-evalh
  (implies (and (shnfp p) (shnfp q) (not (zp i)) (all-integers vals))
           (equal (evalh (norm-pow i p q) vals)
                  (evalh `(pow ,i ,p ,q) vals))))

;; norm-var handles the case where the polynomial is a simple variable:

(defun var-index (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
  (if (consp vars)
      (if (eql x (car vars))
          0
        (1+ (var-index x (cdr vars))))
    ()))

(defund norm-var (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
  (norm-pop (var-index x vars) '(pow 1 1 0)))

(defthm shnfp-norm-var
  (implies (member x vars)
           (shnfp (norm-var x vars))))

(defthm evalh-norm-var
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (evalh (norm-var x vars) vals)
                  (evalp x (pairlis$ vars vals)))))

;; norm-add computes a normal representation of (+ a b),
;; given normal representations x and y of a and b.

;; add-int handles the case where x is an integer:

(defund add-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (shnfp y))))
  (if (atom y)
      (+ x y)
    (case (car y)
      (pow (list 'pow (cadr y) (caddr y) (add-int x (cadddr y))))
      (pop (list 'pop (cadr y) (add-int x (caddr y)))))))

(defthm normp-add-int
  (implies (and (shf-normp x)
                (shf-normp y)
                (atom x))
           (shf-normp (add-int x y))))

(defthm shnfp-add-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (shnfp (add-int x y))))

(defthm evalh-add-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (equal (evalh (add-int x y) vals)
                  (+ (evalh x vals) (evalh y vals)))))

(defmacro add-pop-pop (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (norm-pop i (norm-add p q))
       (if (> i j)
           (norm-pop j (norm-add (list 'pop (- i j) p) q))
         (norm-pop i (norm-add (list 'pop (- j i) q) p))))))

(defmacro add-pop-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (list 'pow j q (norm-add r p))
       (list 'pow j q (norm-add r (list 'pop (1- i) p))))))

(defmacro add-pow-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))
     (if (= i j)
         (norm-pow i (norm-add p r) (norm-add q s))
       (if (> i j)
           (norm-pow j (norm-add (list 'pow (- i j) p 0) r) (norm-add q s))
        (norm-pow i (norm-add (list 'pow (- j i) r 0) p) (norm-add s q))))))

(defun norm-add (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp x)
                              (shnfp y))))
  (if (atom x)
      (add-int x y)
    (if (atom y)
        (add-int y x)
      (case (car x)
        (pop (case (car y)
               (pop (add-pop-pop x y))
               (pow (add-pop-pow x y))))
        (pow (case (car y)
               (pop (add-pop-pow y x))
               (pow (add-pow-pow x y))))))))

(defthm evalh-norm-add-int
  (implies (and (shnfp x)
                (shnfp y)
                (or (atom x) (atom y)))
           (equal (evalh (norm-add x y) vals)
                  (+ (evalh x vals) (evalh y vals)))))

(defthm shnfp-norm-add
  (implies (and (shnfp x)
                (shnfp y))
           (shnfp (norm-add x y))))

(defthm normp-norm-add
  (implies (and (shnfp x)
                (shnfp y))
           (shf-normp (norm-add x y))))

(defthm evalh-norm-add
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-add x y) vals)
                  (+ (evalh x vals)
                     (evalh y vals)))))

;; The remaining cases are handled by norm-neg, norm-mul, and norm-expt:

(defun norm-neg (x)
  (declare (xargs :guard (shnfp x)))
  (if (atom x)
      (- x)
    (case (car x)
      (pop (list 'pop (cadr x) (norm-neg (caddr x))))
      (pow (list 'pow (cadr x) (norm-neg (caddr x)) (norm-neg (cadddr x)))))))

(defthm shnfp-norm-neg
  (implies (shnfp x)
           (shnfp (norm-neg x))))

(defthm evalh-norm-neg
  (implies (and (shnfp x)
                (all-integers vals))
           (equal (evalh (norm-neg x) vals)
                  (- (evalh x vals)))))

(defthmd norm-neg-norm-neg
  (implies (shfp x)
           (equal (norm-neg (norm-neg x)) x)))

(defund mul-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (shnfp y))))
  (if (= x 0)
      0
    (if (atom y)
        (* x y)
      (case (car y)
        (pop (norm-pop (cadr y) (mul-int x (caddr y))))
        (pow (norm-pow (cadr y) (mul-int x (caddr y)) (mul-int x (cadddr y))))))))

(defthm shnfp-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (shnfp (mul-int x y))))

(defthm evalh-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x)
                (all-integers vals))
           (equal (evalh (mul-int x y) vals)
                  (* (evalh x vals) (evalh y vals)))))

(defmacro mul-pop-pop (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (norm-pop i (norm-mul p q))
       (if (> i j)
           (norm-pop j (norm-mul (list 'pop (- i j) p) q))
         (norm-pop i (norm-mul (list 'pop (- j i) q) p))))))

(defmacro mul-pop-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (norm-pow j (norm-mul ,x q) (norm-mul p r))
       (norm-pow j (norm-mul ,x q) (norm-mul (list 'pop (1- i) p) r)))))

(defmacro mul-pow-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))   ;x = p * z^i + q
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))  ;y = r * z^j + s
     (norm-add (norm-add (norm-pow (+ i j) (norm-mul p r) (norm-mul q s))  ;p * r * z^(i+j) + q * s
                         (norm-pow i (norm-mul p (norm-pop 1 s)) 0))       ;p * s * z^i
               (norm-pow j (norm-mul r (norm-pop 1 q)) 0))))               ;r * q * z^j

(defund norm-mul (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp x)
                              (shnfp y))))
  (if (atom x)
      (mul-int x y)
    (if (atom y)
        (mul-int y x)
      (case (car x)
        (pop (case (car y)
               (pop (mul-pop-pop x y))
               (pow (mul-pop-pow x y))))
        (pow (case (car y)
               (pop (mul-pop-pow y x))
               (pow (mul-pow-pow x y))))))))

(defthm shnfp-norm-mul
  (implies (and (shnfp x)
                (shnfp y))
           (shnfp (norm-mul x y))))

(defthm evalh-norm-mul
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-mul x y) vals)
                  (* (evalh x vals)
                     (evalh y vals)))))

(defun norm-expt (x k)
  (declare (xargs :guard (and (shnfp x)
                              (natp k))))
  (if (zp k)
      1
    (norm-mul x (norm-expt x (1- k)))))

(defthm shnfp-norm-expt
  (implies (shnfp x)
           (shnfp (norm-expt x k))))

(defthm evalh-norm-expt
  (implies (and (shnfp x)
                (natp k)
                (all-integers vals))
           (equal (evalh (norm-expt x k) vals)
                 (expt (evalh x vals) k))))

(defun norm (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (polyp x vars))))
  (if (integerp x)
      x
    (if (atom x)
        (norm-var x vars)
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (norm-add (norm y vars) (norm z vars)))
          (- (if (cddr x) (norm-add (norm y vars) (norm-neg (norm z vars))) (norm-neg (norm y vars))))
          (* (norm-mul (norm y vars) (norm z vars)))
          (expt (norm-expt (norm y vars) (norm z vars))))))))

(defthm shnfp-norm
  (implies (and (distinct-symbols vars)
                (polyp x vars))
           (shnfp (norm x vars))))

(defthm evalh-norm
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (polyp x vars))
           (and (shnfp (norm x vars))
                (equal (evalh (norm x vars) vals)
                       (evalp x (pairlis$ vars vals))))))

;;*********************************************************************************
;;                                   Completeness
;;*********************************************************************************

;; We shall show that if two polynomials have the same values for all variable
;; assignments, then they produce the same SHNF.

(defun pad0 (i n)
  (if (zp i)
      n
    (cons 0 (pad0 (1- i) n))))

(defun ew (x y)
  (if (atom x)
      ()
    (if (eq (car x) 'pop)
        (let ((i (cadr x))
              (p (caddr x)))
          (pad0 i (ew p y)))
      (let ((p (caddr x))
            (q (cadddr x)))
        (if (or (atom p) (eq (car p) 'pop))
            (let ((n (ew p y)))
              (cons (ifix (+ (abs (evalh q (cdr n)))
                             (abs (evalh y (cdr n)))
                             1))
                    (cdr n)))
          (ew p
              (norm-add (norm-mul q q)
                        (norm-mul y y))))))))

(defund evalh-witness (x)
  (ew x 1))

(defthmd evalh-not-zero
  (implies (and (shnfp x)
                (not (= x 0)))
	   (let ((n (evalh-witness x)))
	     (and (all-integers n)
                  (not (equal (evalh x n) 0))))))

(defthmd evalh-not-equal
  (let ((n (evalh-witness (norm-add (norm-neg y) x))))
    (implies (and (shnfp x)
                  (shnfp y)
		  (not (equal x y)))
	     (not (equal (evalh x n) (evalh y n))))))

(defun list0 (k)
  (if (zp k)
      ()
    (cons 0 (list0 (1- k)))))

(defund evalp-witness (x y vars)
   (let ((n (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars)))))
     (append n (list0 (- (len vars) (len n))))))

(defthmd all-ints-evalp-witness
  (all-integers (evalp-witness x y vars)))

(defthm evalp-not-equal
  (let ((a (pairlis$ vars (evalp-witness x y vars))))
    (implies (and (distinct-symbols vars)
                  (polyp x vars)
  		  (polyp y vars)
		  (equal (evalp x a) (evalp y a)))
	     (equal (norm x vars)
	            (norm y vars))))
  :rule-classes ())

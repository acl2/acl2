(in-package "RTL")

(include-book "rtl/rel11/lib/basic" :dir :system)

(include-book "rtl/rel11/lib/util" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

;;*********************************************************************************
;;                              Polynomial Terms
;;*********************************************************************************

(defun polyp (x vars)
  (if (atom x)
      (or (integerp x) (member x vars))
    (let ((y (cadr x)) (z (caddr x)))
      (case (car x)
        (+ (and (polyp y vars) (polyp z vars)))
        (- (and (polyp y vars) (or (not (cddr x)) (polyp z vars))))
        (* (and (polyp y vars) (polyp z vars)))
        (expt (and (polyp y vars) (natp z)))))))

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

(defun shfp (x)
  (if (atom x)
      (integerp x)
    (let ((i (cadr x)) (p (caddr x)) (q (cadddr x)))
      (case (car x)
        (pop (and (natp i) (shfp p)))
        (pow (and (natp i) (shfp p) (shfp q)))))))

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
  (if (atom x)
      x
    (case (car x)
      (pop (evalh (caddr x) (nthcdr (cadr x) vals)))
      (pow (+ (* (expt (if (consp vals) (car vals) 0) (cadr x))
                 (evalh (caddr x) vals))
             (evalh (cadddr x) (cdr vals)))))))

(defthm evalh-int
  (implies (atom x)
           (equal (evalh x vals)
                  x)))

;; A SHF x is normal if the following conditions hold:
;;    (1) x = (POP i p) => p is a POW
;;    (2) x = (POW i p q) => p neither 0 nor (POW j r 0)

(defun normp (x)
  (if (atom x)
      t
    (let ((i (cadr x)) (p (caddr x)) (q (cadddr x)))
      (case (car x)
        (pop (and (not (= i 0))
                  (normp p)
                  (consp p)
                  (eql (car p) 'pow)
                  (normp p)))
        (pow (and (not (= i 0))
                  (normp p)
                  (normp q)
                  (if (atom p)
                      (not (= p 0))
                    (not (and (eql (car p) 'pow)
                              (equal (cadddr p) 0))))))))))

(defun shnfp (x)
  (and (shfp x) (normp x)))

(defthm shnfp-shfp
  (implies (shnfp x)
           (shfp x)))

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

(defun all-integers (vals)
  (if (consp vals)
      (and (all-integers (cdr vals))
           (integerp (car vals)))
    t))

(defthm all-integers-nthcdr
  (implies (all-integers vals)
           (all-integers (nthcdr n vals))))

(defthm integerp-evalh
  (implies (and (shfp x)
                (all-integers vals))
           (integerp (evalh x vals)))
  :rule-classes (:type-prescription :rewrite))

;; We shall define a function norm that computes a SHNF
;; representing a polynomial with respect to a given variable ordering.

;; norm-pop normalizes (POP i p), where p is normal:

(defun norm-pop (i p)
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
           (normp (norm-pop i p)))
  :hints (("Goal" :use norm-pop-shnfp)))

(defthm norm-pop-shfp
  (implies (and (shnfp p) (natp i))
           (shfp (norm-pop i p)))
  :hints (("Goal" :use norm-pop-shnfp)))

(defthm nthcdr+
  (implies (and (natp m) (natp n))
           (equal (nthcdr m (nthcdr n x))
                  (nthcdr (+ m n) x)))
  :hints (("Goal" :induct (nthcdr n x))))

(defthm norm-pop-evalh
  (implies (and (shnfp p) (natp i))
           (equal (evalh (norm-pop i p) n)
                  (evalh `(pop ,i ,p) n)))
  :hints (("Goal" :expand ((evalh p (nthcdr i n)) (evalh (list 'pop i p) N)))))

(in-theory (disable norm-pop))

;; norm-pow normalizes (POW i p q), where p and p are normal:

(defun norm-pow (i p q)
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
           (normp (norm-pow i p q)))
  :hints (("Goal" :use norm-pow-shnfp)))

(defthm norm-pow-shfp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shfp (norm-pow i p q)))
  :hints (("Goal" :use norm-pow-shnfp)))

(defthm norm-pow-evalh
  (implies (and (shnfp p) (shnfp q) (not (zp i)) (all-integers vals))
           (equal (evalh (norm-pow i p q) vals)
                  (evalh `(pow ,i ,p ,q) vals))))

(in-theory (disable norm-pow))

;; norm-var handles the case where the polynomial is a simple variable:

(defun var-index (x vars)
  (if (consp vars)
      (if (eql x (car vars))
          0
        (1+ (var-index x (cdr vars))))
    ()))

(defthm natp-var-index
  (implies (member x vars)
           (natp (var-index x vars)))
  :rule-classes (:type-prescription :rewrite))

(defun norm-var (x vars)
  (norm-pop (var-index x vars) '(pow 1 1 0)))

(defthm shnfp-norm-var
  (implies (member x vars)
           (shnfp (norm-var x vars))))

(defun distinct-symbols (vars)
  (if (consp vars)
      (and (distinct-symbols (cdr vars))
           (symbolp (car vars))
           (not (member (car vars) (cdr vars))))
    t))

(defthm car-nthcdr
  (equal (car (nthcdr i l))
         (nth i l)))

(defthm consp-nthcdr
  (implies (and (natp i)
                (< i (len l)))
           (consp (nthcdr i l))))

(defthm member-len-pos
  (implies (= (len l) 0)
           (not (member x l))))

(local-defthm var-index-len
  (implies (member x vars)
           (< (var-index x vars) (len vars)))
  :rule-classes ())

(defthm all-integers-integer
  (implies (and (all-integers vals)
                (natp i)
                (< i (len vals)))
           (integerp (nth i vals)))
  :rule-classes (:type-prescription :rewrite))

(defthm evalh-norm-var-rewrite
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (= (len vars) (len vals))
                (member x vars))
           (equal (evalh (norm-var x vars) vals)
                  (nth (var-index x vars) vals)))
  :hints (("Goal" :use (var-index-len))))

(defthm distinct-symbols-atom
  (implies (and (distinct-symbols vars)
                (member x vars))
           (atom x)))

(defthm evalp-var
  (implies (and (distinct-symbols vars)
                (member x vars))
           (equal (evalp x a)
                  (cdr (assoc x a)))))

(defthm nth-var-index-vals
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (= (len vars) (len vals))
                (member x vars))
           (equal (nth (var-index x vars) vals)
                  (cdr (assoc x (pairlis$ vars vals))))))

(defthm evalh-norm-var
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (= (len vars) (len vals))
                (member x vars))
           (equal (evalh (norm-var x vars) vals)
                  (evalp x (pairlis$ vars vals)))))

;; norm-add computes a normal representation of (+ a b),
;; given normal representations x and y of a and b.

(in-theory (disable norm-var))

;; add-int handles the case where x is an integer:

(defun add-int (x y)
  (if (atom y)
      (+ x y)
    (case (car y)
      (pow (list 'pow (cadr y) (caddr y) (add-int x (cadddr y))))
      (pop (list 'pop (cadr y) (add-int x (caddr y)))))))

(defthm normp-add-int
  (implies (and (normp x)
                (normp y)
                (atom x))
           (normp (add-int x y)))
  :hints (("Subgoal *1/5" :expand ((add-int x (caddr y))))))

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

(in-theory (disable add-int))

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
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (and (shfp x)
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
                    (pow (add-pow-pow x y)))))))))

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
           (normp (norm-add x y)))
  :hints (("Goal" :use shnfp-norm-add)))

(defun norm-add-induct (x y vals)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (if (or (not (shnfp x))
          (not (shnfp y))
          (atom x)
          (atom y)
          (not (member (car x) '(pop pow)))
          (not (member (car y) '(pop pow))))
      (list x y vals)
    (if (and (eql (car x) 'pop) (eql (car y) 'pop))
        (let ((i (cadr x)) (p (caddr x))
              (j (cadr y)) (q (caddr y)))
          (if (= i j)
              (norm-add-induct p q (nthcdr i vals))
            (if (> i j)
                (norm-add-induct (list 'pop (- i j) p) q (nthcdr j vals))
              (norm-add-induct (list 'pop (- j i) q) p (nthcdr i vals)))))
      (if (and (eql (car x) 'pop) (eql (car y) 'pow))
          (let ((i (cadr x)) (p (caddr x)) (r (cadddr y)))
            (if (= i 1)
                (norm-add-induct r p (cdr vals))
              (norm-add-induct r (list 'pop (1- i) p) (cdr vals))))
        (if (and (eql (car x) 'pow) (eql (car y) 'pop))
            (let ((i (cadr y)) (p (caddr y)) (r (cadddr x)))
              (if (= i 1)
                  (norm-add-induct r p (cdr vals))
                (norm-add-induct r (list 'pop (1- i) p) (cdr vals))))
          (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
                (j (cadr y)) (r (caddr y)) (s (cadddr y)))
            (if (= i j)
                (list (norm-add-induct p r vals)
                      (norm-add-induct q s (cdr vals) ))
              (if (> i j)
                  (list (norm-add-induct (list 'pow (- i j) p 0) r vals)
                        (norm-add-induct q s (cdr vals)))
                (list (norm-add-induct (list 'pow (- j i) r 0) p vals)
                      (norm-add-induct s q (cdr vals)))))))))))

(local-defthm evalh-add-pop-pop
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (implies (and (= i j) (shnfp p) (shnfp q))
                           (= (evalh (norm-add p q) (nthcdr i vals))
                              (+ (evalh p (nthcdr i vals)) (evalh q (nthcdr i vals)))))
                  (implies (and (> i j) (shnfp (list 'pop (- i j) p)) (shnfp q))
                           (= (evalh (norm-add (list 'pop (- i j) p) q) (nthcdr j vals))
                              (+ (evalh (list 'pop (- i j) p) (nthcdr j vals))
                                 (evalh q (nthcdr j vals)))))
                  (implies (and (< i j) (shnfp (list 'pop (- j i) q)) (shnfp p))
                           (= (evalh (norm-add (list 'pop (- j i) q) p) (nthcdr i vals))
                              (+ (evalh (list 'pop (- j i) q) (nthcdr i vals))
                                 (evalh p (nthcdr i vals))))))
             (= (evalh (norm-add x y) vals)
                (+ (evalh x vals) (evalh y vals))))))

(local-defthm evalh-add-pop-pow
  (let ((i (cadr x)) (p (caddr x)) (r (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (implies (and (= i 1) (shnfp r) (shnfp p))
                           (= (evalh (norm-add r p) (cdr vals))
                              (+ (evalh r (cdr vals)) (evalh p (cdr vals)))))
                  (implies (and (not (= i 1)) (shnfp r) (shnfp (list 'pop (1- i) p)))
                           (= (evalh (norm-add r (list 'pop (1- i) p)) (cdr vals))
                              (+ (evalh r (cdr vals))
                                 (evalh (list 'pop (1- i) p) (cdr vals))))))
             (= (evalh (norm-add x y) vals)
                (+ (evalh x vals) (evalh y vals))))))

(local-defthm evalh-add-pow-pop
  (let ((i (cadr y)) (p (caddr y)) (r (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pop)
                  (implies (and (= i 1) (shnfp r) (shnfp p))
                           (= (evalh (norm-add r p) (cdr vals))
                              (+ (evalh r (cdr vals)) (evalh p (cdr vals)))))
                  (implies (and (not (= i 1)) (shnfp r) (shnfp (list 'pop (1- i) p)))
                           (= (evalh (norm-add r (list 'pop (1- i) p)) (cdr vals))
                              (+ (evalh r (cdr vals))
                                 (evalh (list 'pop (1- i) p) (cdr vals))))))
             (= (evalh (norm-add x y) vals)
                (+ (evalh x vals) (evalh y vals))))))

(defun car0 (vals)
  (if (consp vals) (car vals) 0))

(defthm evalh-pow-rewrite
  (implies (eql (car x) 'pow)
           (equal (evalh x vals)
                  (+ (* (expt (car0 vals) (cadr x))
                        (evalh (caddr x) vals))
                     (evalh (cadddr x) (cdr vals))))))

(local-defthm hack-1
  (implies (and (integerp i)
                (integerp p)
                (integerp q)
                (integerp r)
                (integerp s)
                (integerp pr)
                (integerp qs)
                (= pr (+ p r))
                (= qs (+ q s)))
           (= (+ (* i pr) qs)
              (+ (* i p) (* i r) q s)))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-1
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (= i j))
             (equal (evalh (norm-add x y) vals)
                    (+ (* (expt (car0 vals) i)
                          (evalh (norm-add p r) vals))
                       (evalh (norm-add q s) (cdr vals))))))
  :hints (("Goal" :expand ((norm-add x y)))))

(local-defthm evalh-add-pow-pow-2
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (r (caddr y)) (s (cadddr y)))
    (implies (and (integerp (car0 vals))
                  (integerp (evalh p vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals)))
                  (= (evalh (norm-add p r) vals)
                     (+ (evalh p vals) (evalh r vals)))
                  (= (evalh (norm-add q s) (cdr vals))
                     (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))
             (equal (+ (* (expt (car0 vals) i)
                          (evalh (norm-add p r) vals))
                       (evalh (norm-add q s) (cdr vals)))
                    (+ (* (expt (car0 vals) i)
                          (evalh p vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) i)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance hack-1 (i (expt (car0 vals) (cadr x)))
                                          (p (evalh (caddr x) vals))
                                          (q (evalh (cadddr x) (cdr vals)))
                                          (r (evalh (caddr y) vals))
                                          (s (evalh (cadddr y) (cdr vals)))
                                          (pr (evalh (norm-add (caddr x) (caddr y)) vals))
                                          (qs (evalh (norm-add (cadddr x) (cadddr y)) (cdr vals))))))))

(local-defthm evalh-add-pow-pow-3
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow))
             (equal (+ (evalh x vals) (evalh y vals))
                    (+ (* (expt (car0 vals) i)
                          (evalh p vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-4
  (let ((p (caddr x)) (q (cadddr x))
        (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow))
             (and (shnfp p)
                  (shnfp q) 
                  (shnfp r) 
                  (shnfp s) 
                  (integerp (car0 vals))
                  (integerp (evalh p vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals))))))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-5
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (= i j)
                  (implies (and (shnfp p) (shnfp r) (shnfp q) (shnfp s))
                           (and (= (evalh (norm-add p r) vals)
                                   (+ (evalh p vals) (evalh r vals)))
                                (= (evalh (norm-add q s) (cdr vals))
                                   (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))))
             (equal (evalh (norm-add x y) vals)
                    (+ (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :use (evalh-add-pow-pow-1 evalh-add-pow-pow-2 evalh-add-pow-pow-3 evalh-add-pow-pow-4)
                  :in-theory (theory 'minimal-theory))))

(local-defthm evalh-add-pow-pow-6
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (equal (evalh (norm-add x y) vals)
                    (+ (* (expt (car0 vals) j)
                          (evalh (norm-add (list 'pow (- i j) p 0) r) vals))
                       (evalh (norm-add q s) (cdr vals))))))
  :hints (("Goal" :in-theory (disable norm-add evalh)
                  :expand ((norm-add x y)))))

(local-defthm evalh-add-pow-pow-7
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (integerp (car0 vals))
                  (integerp (evalh (list 'pow (- i j) p 0) vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals)))
                  (= (evalh (norm-add (list 'pow (- i j) p 0) r) vals)
                     (+ (evalh (list 'pow (- i j) p 0) vals) (evalh r vals)))
                  (= (evalh (norm-add q s) (cdr vals))
                     (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))
             (equal (+ (* (expt (car0 vals) j)
                          (evalh (norm-add (list 'pow (- i j) p 0) r) vals))
                       (evalh (norm-add q s) (cdr vals)))
                    (+ (* (expt (car0 vals) j)
                          (evalh (list 'pow (- i j) p 0) vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable ACL2::|(* x (if a b c))|)
                  :use ((:instance hack-1 (i (expt (car0 vals) (cadr y)))
                                          (p (evalh (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) vals))
                                          (q (evalh (cadddr x) (cdr vals)))
                                          (r (evalh (caddr y) vals))
                                          (s (evalh (cadddr y) (cdr vals)))
                                          (pr (evalh (norm-add (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) (caddr y)) vals))
                                          (qs (evalh (norm-add (cadddr x) (cadddr y)) (cdr vals))))))))

(local-defthm evalh-add-pow-pow-8
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow))
             (equal (+ (* (expt (car0 vals) j)
                          (evalh (list 'pow (- i j) p 0) vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals)))
                    (+ (* (expt (car0 vals) i)
                          (evalh p vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-9
  (implies (and (shnfp x)
                (all-integers vals)
                (consp x)
                (eql (car x) 'pow))
           (integerp (evalh (caddr x) vals)))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-10
  (let ((i (cadr x)) (p (caddr x)) (j (cadr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (integerp (evalh (list 'pow (- i j) p 0) vals))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-evalh) :use (evalh-add-pow-pow-9))))

(local-defthm evalh-add-pow-pow-11
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (and (shnfp (list 'pow (- i j) p 0))
                  (shnfp q) 
                  (shnfp r) 
                  (shnfp s) 
                  (integerp (car0 vals))
                  (integerp (evalh (list 'pow (- i j) p 0) vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh p vals))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable evalh) :use (evalh-add-pow-pow-10))))

(local-defthm evalh-add-pow-pow-12
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j)
                  (implies (and (shnfp (list 'pow (- i j) p 0)) (shnfp r) (shnfp q) (shnfp s))
                           (and (= (evalh (norm-add (list 'pow (- i j) p 0) r) vals)
                                   (+ (evalh (list 'pow (- i j) p 0) vals) (evalh r vals)))
                                (= (evalh (norm-add q s) (cdr vals))
                                   (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))))
             (equal (evalh (norm-add x y) vals)
                    (+ (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :use (evalh-add-pow-pow-3 evalh-add-pow-pow-6 evalh-add-pow-pow-7 evalh-add-pow-pow-8 evalh-add-pow-pow-11)
                  :in-theory (theory 'minimal-theory))))

(local-defthm evalh-add-pow-pow-13
  (let ((i (cadr y)) (p (caddr y)) (q (cadddr y))
        (j (cadr x)) (r (caddr x)) (s (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (equal (evalh (norm-add x y) vals)
                    (+ (* (expt (car0 vals) j)
                          (evalh (norm-add (list 'pow (- i j) p 0) r) vals))
                       (evalh (norm-add q s) (cdr vals))))))
  :hints (("Goal" :in-theory (disable norm-add evalh)
                  :expand ((norm-add x y)))))

(local-defthm evalh-add-pow-pow-14
  (let ((i (cadr y)) (p (caddr y)) (q (cadddr y))
        (j (cadr x)) (r (caddr x)) (s (cadddr x)))
    (implies (and (integerp (car0 vals))
                  (integerp (evalh (list 'pow (- i j) p 0) vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals)))
                  (= (evalh (norm-add (list 'pow (- i j) p 0) r) vals)
                     (+ (evalh (list 'pow (- i j) p 0) vals) (evalh r vals)))
                  (= (evalh (norm-add q s) (cdr vals))
                     (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))
             (equal (+ (* (expt (car0 vals) j)
                          (evalh (norm-add (list 'pow (- i j) p 0) r) vals))
                       (evalh (norm-add q s) (cdr vals)))
                    (+ (* (expt (car0 vals) j)
                          (evalh (list 'pow (- i j) p 0) vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ()
  :hints (("Goal" :do-not '(eliminate-destructors generalize)
                  :in-theory (disable ACL2::|(equal x (if a b c))| ACL2::|(+ x (if a b c))| ACL2::|(equal (if a b c) x)| 
                                      ACL2::|(+ (if a b c) x)| ACL2::|(* (if a b c) x)| car0 evalh-pow-rewrite evalh norm-add 
                                      ACL2::|(* x (if a b c))|)
                  :use ((:instance hack-1 (i (expt (car0 vals) (cadr y)))
                                          (p (evalh (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) vals))
                                          (q (evalh (cadddr x) (cdr vals)))
                                          (r (evalh (caddr y) vals))
                                          (s (evalh (cadddr y) (cdr vals)))
                                          (pr (evalh (norm-add (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) (caddr y)) vals))
                                          (qs (evalh (norm-add (cadddr x) (cadddr y)) (cdr vals))))))))

(local-defthm evalh-add-pow-pow-15 
  (let ((i (cadr y)) (p (caddr y)) (q (cadddr y))
        (j (cadr x)) (r (caddr x)) (s (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow))
             (equal (+ (* (expt (car0 vals) j)
                          (evalh (list 'pow (- i j) p 0) vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals)))
                    (+ (* (expt (car0 vals) i)
                          (evalh p vals))
                       (evalh q (cdr vals))
                       (* (expt (car0 vals) j)
                          (evalh r vals))
                       (evalh s (cdr vals))))))
  :rule-classes ())

(local-defthm evalh-add-pow-pow-16
  (let ((i (cadr y)) (p (caddr y)) (j (cadr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (integerp (evalh (list 'pow (- i j) p 0) vals))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-evalh) :use (:instance evalh-add-pow-pow-9 (x y)))))

(local-defthm evalh-add-pow-pow-17
  (let ((i (cadr y)) (p (caddr y)) (q (cadddr y))
        (j (cadr x)) (r (caddr x)) (s (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j))
             (and (shnfp (list 'pow (- i j) p 0))
                  (shnfp q) 
                  (shnfp r) 
                  (shnfp s) 
                  (integerp (car0 vals))
                  (integerp (evalh (list 'pow (- i j) p 0) vals))
                  (integerp (evalh q (cdr vals)))
                  (integerp (evalh p vals))
                  (integerp (evalh r vals))
                  (integerp (evalh s (cdr vals))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable evalh) :use (evalh-add-pow-pow-16))))

(local-defthm evalh-add-pow-pow-18
  (let ((i (cadr y)) (p (caddr y)) (q (cadddr y))
        (j (cadr x)) (r (caddr x)) (s (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (> i j)
                  (implies (and (shnfp (list 'pow (- i j) p 0)) (shnfp r) (shnfp q) (shnfp s))
                           (and (= (evalh (norm-add (list 'pow (- i j) p 0) r) vals)
                                   (+ (evalh (list 'pow (- i j) p 0) vals) (evalh r vals)))
                                (= (evalh (norm-add q s) (cdr vals))
                                   (+ (evalh q (cdr vals)) (evalh s (cdr vals)))))))
             (equal (evalh (norm-add x y) vals)
                    (+ (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :use (evalh-add-pow-pow-3 evalh-add-pow-pow-13 evalh-add-pow-pow-14 evalh-add-pow-pow-15 evalh-add-pow-pow-17)
                  :in-theory (theory 'minimal-theory))))

(in-theory (disable normp norm-add evalh))

(defthm evalh-norm-add
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-add x y) vals)
                  (+ (evalh x vals)
                     (evalh y vals))))
  :hints (("Goal" :induct (norm-add-induct x y vals))))

(in-theory (enable normp evalh))

;; The remaining cases are handled by norm-neg, norm-mul, and norm-expt:

(defun norm-neg (x)
  (if (atom x)
      (- x)
    (case (car x)
      (pop (list 'pop (cadr x) (norm-neg (caddr x))))
      (pow (list 'pow (cadr x) (norm-neg (caddr x)) (norm-neg (cadddr x)))))))

(local-defthm norm-neg-0
  (implies (and (shfp x) (not (equal x 0)))
           (not (equal (norm-neg x) 0))))

(defthm shnfp-norm-neg
  (implies (shnfp x)
           (shnfp (norm-neg x)))
  :hints (("Subgoal *1/3" :expand ((norm-neg (caddr x))))
          ("subgoal *1/2" :expand ((norm-neg (caddr x))))))

(defthm evalh-norm-neg
  (implies (and (shnfp x)
                (all-integers vals))
           (equal (evalh (norm-neg x) vals)
                  (- (evalh x vals)))))

(defun mul-int (x y)
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

(local-defthm normp-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (normp (mul-int x y)))
  :hints (("Goal" :use shnfp-mul-int)))

(defthm evalh-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x)
                (all-integers vals))
           (equal (evalh (mul-int x y) vals)
                  (* (evalh x vals) (evalh y vals)))))

(in-theory (disable mul-int))

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

(in-theory (enable norm-pop norm-pow))

(defun norm-mul (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (and (shfp x)
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
                    (pow (mul-pow-pow x y)))))))))

(in-theory (disable norm-pop norm-pow))

(defthm evalh-norm-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (or (atom x) (atom y))
                (all-integers vals))
           (equal (evalh (norm-mul x y) vals)
                  (* (evalh x vals) (evalh y vals)))))

(defthm shnfp-norm-mul
  (implies (and (shnfp x)
                (shnfp y))
           (shnfp (norm-mul x y))))

(in-theory (enable norm-pop norm-pow))

(defun norm-mul-induct (x y vals)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (if (or (not (shnfp x))
          (not (shnfp y))
          (atom x)
          (atom y)
          (not (member (car x) '(pop pow)))
          (not (member (car y) '(pop pow)))
          (not (all-integers vals)))
      (list x y vals)
    (if (and (eql (car x) 'pop) (eql (car y) 'pop))
        (let ((i (cadr x)) (p (caddr x))
              (j (cadr y)) (q (caddr y)))
          (if (= i j)
              (norm-mul-induct p q (nthcdr i vals))
            (if (> i j)
                (norm-mul-induct (list 'pop (- i j) p) q (nthcdr j vals))
              (norm-mul-induct (list 'pop (- j i) q) p (nthcdr i vals)))))
      (if (and (eql (car x) 'pop) (eql (car y) 'pow))
          (let ((i (cadr x)) (p (caddr x)) (q (caddr y)) (r (cadddr y)))
            (if (= i 1)
                (list (norm-mul-induct x q vals)
                      (norm-mul-induct p r (cdr vals)))
              (list (norm-mul-induct x q vals)
                    (norm-mul-induct (list 'pop (1- i) p) r (cdr vals)))))
        (if (and (eql (car x) 'pow) (eql (car y) 'pop))
            (let ((i (cadr y)) (p (caddr y)) (q (caddr x)) (r (cadddr x)))
              (if (= i 1)
                  (list (norm-mul-induct y q vals)
                        (norm-mul-induct p r (cdr vals)))
                (list (norm-mul-induct y q vals)
                      (norm-mul-induct (list 'pop (1- i) p) r (cdr vals)))))
          (let ((p (caddr x)) (q (cadddr x))
                (r (caddr y)) (s (cadddr y)))
            (list (norm-mul-induct p r vals)
                  (norm-mul-induct q s (cdr vals))
                  (norm-mul-induct p (norm-pop 1 s) vals)
                  (norm-mul-induct r (norm-pop 1 q) vals))))))))

(in-theory (disable norm-pop norm-pow))

(local-defthm evalh-mul-pop-pop-1
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop))
             (and (shnfp p)
                  (shnfp q)
                  (not (zp i))
                  (not (zp j))
                  (implies (> i j) (shnfp (list 'pop (- i j) p)))
                  (implies (> j i) (shnfp (list 'pop (- j i) q))))))
  :rule-classes ())

(local-defthm evalh-mul-pop-pop
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (implies (and (= i j) (shnfp p) (shnfp q))
                           (= (evalh (norm-mul p q) (nthcdr i vals))
                              (* (evalh p (nthcdr i vals)) (evalh q (nthcdr i vals)))))
                  (implies (and (> i j) (shnfp (list 'pop (- i j) p)) (shnfp q))
                           (= (evalh (norm-mul (list 'pop (- i j) p) q) (nthcdr j vals))
                              (* (evalh (list 'pop (- i j) p) (nthcdr j vals))
                                 (evalh q (nthcdr j vals)))))
                  (implies (and (< i j) (shnfp (list 'pop (- j i) q)) (shnfp p))
                           (= (evalh (norm-mul (list 'pop (- j i) q) p) (nthcdr i vals))
                              (* (evalh (list 'pop (- j i) q) (nthcdr i vals))
                                 (evalh p (nthcdr i vals))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :in-theory (disable shnfp)
                  :use (evalh-mul-pop-pop-1))))

(local-defthm evalh-mul-pop-pow-1
  (let ((i (cadr x)) (p (caddr x)) (j (cadr y)) (q (caddr y)) (r (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow))
             (and (shnfp p)
                  (shnfp q)
                  (shnfp r)
                  (not (zp i))
                  (not (zp j))
                  (implies (not (= i 1)) (shnfp (list 'pop (1- i) p))))))
  :rule-classes ())

(local-defthm evalh-mul-pop-pow
  (let ((i (cadr x)) (p (caddr x)) (q (caddr y)) (r (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (implies (and (= i 1) (shnfp q)  (shnfp r) (shnfp p))
                           (and (= (evalh (norm-mul x q) vals)
                                   (* (evalh x vals) (evalh q vals)))
                                (= (evalh (norm-mul p r) (cdr vals))
                                   (* (evalh p (cdr vals)) (evalh r (cdr vals))))))
                  (implies (and (not (= i 1)) (shnfp q) (shnfp r) (shnfp (list 'pop (1- i) p)))
                           (and (= (evalh (norm-mul x q) vals)
                                   (* (evalh x vals) (evalh q vals)))
                                (= (evalh (norm-mul (list 'pop (1- i) p) r) (cdr vals))
                                   (* (evalh (list 'pop (1- i) p) (cdr vals))
                                      (evalh r (cdr vals)))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :in-theory (disable shnfp)
                  :use (evalh-mul-pop-pow-1))))

(local-defthm evalh-mul-pow-pop
  (let ((i (cadr y)) (p (caddr y)) (q (caddr x)) (r (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pop)
                  (implies (and (= i 1) (shnfp q)  (shnfp r) (shnfp p))
                           (and (= (evalh (norm-mul y q) vals)
                                   (* (evalh y vals) (evalh q vals)))
                                (= (evalh (norm-mul p r) (cdr vals))
                                   (* (evalh p (cdr vals)) (evalh r (cdr vals))))))
                  (implies (and (not (= i 1)) (shnfp q) (shnfp r) (shnfp (list 'pop (1- i) p)))
                           (and (= (evalh (norm-mul y q) vals)
                                   (* (evalh y vals) (evalh q vals)))
                                (= (evalh (norm-mul (list 'pop (1- i) p) r) (cdr vals))
                                   (* (evalh (list 'pop (1- i) p) (cdr vals))
                                      (evalh r (cdr vals)))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :in-theory (disable shnfp)
                  :use ((:instance evalh-mul-pop-pow-1 (x y) (y x))))))

(local-defthm evalh-mul-pow-pow-1
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow))
             (and (shnfp p)
                  (shnfp q)
                  (shnfp r)
                  (shnfp s)
                  (not (zp i))
                  (not (zp j)))))
  :rule-classes ())

(local-defthm evalh-mul-pow-pow
  (let ((p (caddr x)) (q (cadddr x))
        (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (consp x)
                  (consp y)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (implies (and (shnfp p) (shnfp r))
                           (= (evalh (norm-mul p r) vals)
                              (* (evalh p vals) (evalh r vals))))
                  (implies (and (shnfp q) (shnfp s))
                           (= (evalh (norm-mul q s) (cdr vals))
                              (* (evalh q (cdr vals)) (evalh s (cdr vals)))))
                  (implies (and (shnfp p) (shnfp (norm-pop 1 s)))
                           (= (evalh (norm-mul p (norm-pop 1 s)) vals)
                              (* (evalh p vals) (evalh (norm-pop 1 s) vals))))
                  (implies (and (shnfp r) (shnfp (norm-pop 1 q)))
                           (= (evalh (norm-mul r (norm-pop 1 q)) vals)
                              (* (evalh r vals) (evalh (norm-pop 1 q) vals)))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :hints (("Goal" :use (evalh-mul-pow-pow-1)
                  :in-theory (disable shnfp))))

(in-theory (disable shnfp normp norm-mul evalh))

(defthm evalh-norm-mul
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-mul x y) vals)
                  (* (evalh x vals)
                     (evalh y vals))))
  :hints (("Goal" :induct (norm-mul-induct x y vals))))

(defun norm-expt (x k)
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
                 (expt (evalh x vals) k)))
  :hints (("Goal" :induct (norm-expt x k))))

(defun norm (x vars)
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
                (= (len vars) (len vals))
                (polyp x vars))
           (and (shnfp (norm x vars))
                (equal (evalh (norm x vars) vals)
                       (evalp x (pairlis$ vars vals))))))

;; I should have proved this At the beginning of this file:

(defthm integerp-evalp
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (= (len vars) (len vals))
                (polyp x vars))
           (integerp (evalp x (pairlis$ vars vals))))
  :rule-classes ()
  :hints (("Goal" :use (evalh-norm)
                  :in-theory (disable evalh-norm))))

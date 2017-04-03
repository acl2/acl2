(in-package "RTL")

(include-book "std/util/defrule" :dir :system)

(include-book "rtl/rel11/lib/basic" :dir :system)

(include-book "rtl/rel11/lib/util" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))


;; [Jared] trying to speed up this book
;; [Dima] Most of them are disabled using with-arith5-help
(local (deftheory jared-disables
         '(;ACL2::ACL2-NUMBERP-X
           ;ACL2::RATIONALP-X
           ;ACL2::DEFAULT-PLUS-2
           ;ACL2::DEFAULT-TIMES-2
           default-car
           default-cdr

           ;acl2::default-plus-1
           ;acl2::default-times-1
           ;acl2::default-expt-1
           ;acl2::default-expt-2
           ;acl2::default-minus

           ;acl2::|(equal (/ x) (/ y))|
           ;acl2::|(equal c (/ x))|
           ;acl2::|(equal (- x) (- y))|
           ;acl2::|(equal c (- x))|
           ;acl2::|(equal (- x) c)|
           ;acl2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
           ;acl2::EQUAL-OF-PREDICATES-REWRITE

           )))

(local (in-theory (disable jared-disables)))


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
    (case (car x)
      (pop (and (natp (cadr x)) (shfp (caddr x)) (null (cdddr x))))
      (pow (and (natp (cadr x)) (shfp (caddr x)) (shfp (cadddr x)) (null (cddddr x)))))))

;; Thus, a SHF is a tree.  This function counts its nodes:

(defun shf-count (x)
  (if (atom x)
      1
    (case (car x)
      (pop (+ 2 (shf-count (caddr x))))
      (pow (+ 2 (shf-count (caddr x)) (shf-count (cadddr x))))
      (t 0))))

(local (defrule shf-count-atom
  (implies (atom x)
           (equal (shf-count x) 1))))

(local (defrule shf-count-pop
  (equal (shf-count (list 'pop i p))
         (+ 2 (shf-count p)))))

(local (defrule shf-count-pow
  (equal (shf-count (list 'pow i p q))
         (+ 2 (shf-count p) (shf-count q)))))

(local (defrule shf-count-pop-p
  (implies (eql (car x) 'pop)
           (equal (shf-count (caddr x))
                  (- (shf-count x) 2)))))

(local (defrule shf-count-pow-p
  (implies (eql (car x) 'pow)
           (equal (shf-count (caddr x))
                  (- (shf-count x) (+ 2 (shf-count (cadddr x))))))))

(local (defrule shf-count-shfp
  (implies (shfp x)
           (>= (shf-count x) 1))
  :rule-classes :linear))

(local (defrule shf-cound-pow-q
  (implies (eql (car x) 'pow)
           (<= (shf-count (cadddr x)) (- (shf-count x) 2)))
  :rule-classes :linear))

(local (defrule shf-cound-pow-q-shfp
  (implies (and (shfp x)
                (eql (car x) 'pow))
           (<= (shf-count (cadddr x)) (- (shf-count x) 3)))
  :rule-classes :linear))

(local (in-theory (disable shf-count)))

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

(defun all-integers (vals)
  (if (consp vals)
      (and (all-integers (cdr vals))
           (integerp (car vals)))
    t))

(defthm all-integers-nthcdr
  (implies (all-integers vals)
           (all-integers (nthcdr n vals))))

(defrule integerp-evalh
  (implies (and (shfp x)
                (all-integers vals))
           (integerp (evalh x vals)))
  ;; [Jared] dropping this rule-classes because the type-prescription rule
  ;; seems to be very expensive and the hyps don't look like type prescription
  ;; reasoning stuff anyway.
  ;; :rule-classes (:type-prescription :rewrite)
  :enable acl2::expt-type-prescription-integerp-base)

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

(defrule norm-pow-evalh
  (implies (and (shnfp p) (shnfp q) (not (zp i)) (all-integers vals))
           (equal (evalh (norm-pow i p q) vals)
                  (evalh `(pow ,i ,p ,q) vals)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (acl2-numberp x)
                    (natp i)
                    (natp j))
               (equal (* z (expt x (+ i j)))
                      (* (expt x i) z (expt x j))))))))

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

(defrule evalh-norm-var-rewrite
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (evalh (norm-var x vars) vals)
                  (nth (var-index x vars) vals)))
  :use var-index-len
  :enable ACL2::|arith (expt x 1)|)

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
                (<= (len vars) (len vals))
                (member x vars))
           (equal (nth (var-index x vars) vals)
                  (cdr (assoc x (pairlis$ vars vals))))))

(defrule evalh-norm-var
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (evalh (norm-var x vars) vals)
                  (evalp x (pairlis$ vars vals))))
  :enable acl2::|arith (expt x 1)|)

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

;; [Jared] disabling this because accumulated persistence says it's expensive and never
;; useful (but it gets explicitly :use'd later)o
(local-defthmd evalh-add-pow-pow-1
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

(local (defrule evalh-add-pow-pow-8
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
  :rule-classes ()
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (acl2-numberp x)
                    (posp i)
                    (posp j))
               (equal (* (expt x j) y (expt x (- i j)))
                      (* y (expt x i)))))))))

(local (defrule evalh-add-pow-pow-9
  (implies (and (shnfp x)
                (all-integers vals)
                (consp x)
                (eql (car x) 'pow))
           (integerp (evalh (caddr x) vals)))
  :rule-classes ()
  :enable default-car))

(local (defrule evalh-add-pow-pow-10
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
  :use evalh-add-pow-pow-9
  :enable acl2::expt-type-prescription-integerp-base
  :disable integerp-evalh))

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

;; [Jared] disabling this because accumulated persistence says it is expensive and never
;; useful.  it is, however, :use'd later on.
(local-defthmd evalh-add-pow-pow-13
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

(local (defrule evalh-add-pow-pow-15
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
  :rule-classes ()
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (acl2-numberp x)
                    (posp i)
                    (posp j))
               (equal (* (expt x j) y (expt x (+ (- j) i)))
                      (* y (expt x i)))))))))

(local (defrule evalh-add-pow-pow-16
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
  :use (:instance evalh-add-pow-pow-9 (x y))
  :enable acl2::expt-type-prescription-integerp-base
  :disable integerp-evalh))

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

(defrule evalh-norm-neg
  (implies (and (shnfp x)
                (all-integers vals))
           (equal (evalh (norm-neg x) vals)
                  (- (evalh x vals))))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (equal (evalh (norm-neg x) vals)
                      (- (evalh x vals)))
               (equal (* y (evalh (norm-neg x) vals))
                      (- (* (evalh x vals) y))))
      :disable (evalh norm-neg)))))

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

(defrule evalh-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x)
                (all-integers vals))
           (equal (evalh (mul-int x y) vals)
                  (* (evalh x vals) (evalh y vals))))
  :enable acl2::|arith (* y (* x z))|)

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

(local (defrule evalh-mul-pop-pop
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
  :use evalh-mul-pop-pop-1
  :enable default-car
  :disable shnfp))

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

(local (defrule evalh-mul-pop-pow
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
  :use evalh-mul-pop-pow-1
  :enable acl2::|arith (* y (* x z))|
  :disable shnfp))

(local (defrule evalh-mul-pow-pop
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
  :use (:instance evalh-mul-pop-pow-1 (x y) (y x))
  :enable acl2::|arith (* y (* x z))|
  :disable shnfp))

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

(local (defrule evalh-mul-pow-pow
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
  :use evalh-mul-pow-pow-1
  :enable (acl2::|arith (* y (* x z))| acl2::|arith (expt x (+ m n))|)
  :disable shnfp))

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
                (<= (len vars) (len vals))
                (polyp x vars))
           (and (shnfp (norm x vars))
                (equal (evalh (norm x vars) vals)
                       (evalp x (pairlis$ vars vals))))))

;; I should have proved this At the beginning of this file:

(defthm integerp-evalp
  (implies (and (distinct-symbols vars)
                (all-integers vals)
                (<= (len vars) (len vals))
                (polyp x vars))
           (integerp (evalp x (pairlis$ vars vals))))
  :rule-classes ()
  :hints (("Goal" :use (evalh-norm)
                  :in-theory (disable evalh-norm))))



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

(local-defthmd ew-1
  (implies (not (zp x))
           (not (equal (evalh x (ew x y)) 0))))

(local-defthm ew-2
  (equal (nthcdr i (pad0 i n))
         n))

(local-defthmd ew-3
  (let ((p (caddr x)))
    (implies (and (shnfp x)
                  (eq (car x) 'pop)
                  (not (= (evalh p (ew p y)) 0)))
             (not (= (evalh x (ew x y)) 0))))
  :hints (("Goal" :expand ((evalh x (pad0 (cadr x) (ew (caddr x) y)))))))

(local-defthmd ew-4
  (let ((i (cadr z))
        (p (caddr z)))
    (implies (and (eq (car z) 'pop)
                  (not (zp i)))
             (equal (evalh z n)
                    (evalh (list 'pop (1- i) p) (cdr n)))))
  :hints (("Goal" :expand ((evalh z n) (:free (i p n) (evalh (list 'pop i p) n))))))

(local-defthm ew-5
  (implies (and (shnfp z)
                (or (atom z) (eq (car z) 'pop))
                (equal (cdr n1) (cdr n2)))
           (= (evalh z n1) (evalh z n2)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp z) (normp z))
                  :use ((:instance ew-4 (n n1))
                        (:instance ew-4 (n n2))))))

(local-defthm ew-6
  (let* ((i (cadr x))
         (p (caddr x))
         (q (cadddr x))
         (np (cons k (cdr n))))
    (implies (and (shnfp x)
                  (eq (car x) 'pow)
                  (or (atom p) (eq (car p) 'pop)))
             (= (evalh x np)
                (+ (* (expt k i)
                      (evalh p n))
                   (evalh q (cdr n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance ew-5 (z (caddr x)) (n1 n) (n2 (cons k (cdr n)))))
                  :expand ((evalh x (cons k (cdr n))) (shnfp x) (shfp x) (normp x)))))

(local-defthm ew-7
  (implies (and (not (zp k))
                (not (zp i))
		(integerp p)
		(not (= p 0)))
           (>= (abs (* (expt k i) p)) k))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(local-defthm ew-8
  (let* ((i (cadr x))
         (p (caddr x))
         (q (cadddr x))
         (np (cons k (cdr n))))
    (implies (and (not (zp k))
                  (all-integers n)
                  (not (= (evalh p n) 0))
                  (shnfp x)
                  (eq (car x) 'pow)
                  (or (atom p) (eq (car p) 'pop)))
             (>= (abs (evalh x np))
                 (- (abs (* (expt k i) (evalh p n)))
		    (abs (evalh q (cdr n)))))))
  :rule-classes ()
  :hints (("Goal" :use (ew-6) :in-theory (disable evalh evalh-pow-rewrite)
                  :expand ((normp x) (normp (caddr x)) (shnfp x)))))

(local-defthm ew-9
  (let* ((i (cadr x))
         (p (caddr x))
         (q (cadddr x))
         (np (cons k (cdr n))))
    (implies (and (not (zp k))
                  (all-integers n)
                  (shnfp x)
                  (eq (car x) 'pow)
                  (or (atom p) (eq (car p) 'pop)))
             (and (not (zp i))
	          (integerp (evalh x np))
	          (integerp (evalh p n))
	          (integerp (evalh q (cdr n)))
	          (integerp (expt k i)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable evalh evalh-pow-rewrite)
                  :expand ((normp x) (normp (caddr x)) (shnfp x)))))

(local-defthm ew-10
  (let* ((p (caddr x))
         (q (cadddr x))
         (np (cons k (cdr n))))
    (implies (and (not (zp k))
                  (all-integers n)
                  (not (= (evalh p n) 0))
                  (shnfp x)
                  (eq (car x) 'pow)
                  (or (atom p) (eq (car p) 'pop)))
             (>= (abs (evalh x np))
                 (- k (abs (evalh q (cdr n)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable evalh evalh-pow-rewrite)
                  :use (ew-8 ew-9
                        (:instance ew-7 (i (cadr x)) (p (evalh (caddr x) n)))))))

(local-defthm ew-11
  (all-integers (ew x y)))

(local-defthmd ew-12
  (let ((p (caddr x)) (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers n)
                  (eq (car x) 'pow)
                  (not (= (evalh p (ew p y)) 0)))
             (and (integerp (evalh q (cdr n)))
                  (integerp (evalh y (cdr n)))))))

(local-defthmd ew-13
  (let ((p (caddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (or (atom p) (eq (car p) 'pop))
                  (not (= (evalh p (ew p y)) 0)))
             (and (> (car (ew x y)) 0)
	          (> (abs (evalh x (ew x y)))
		     (abs (evalh y (cdr (ew x y)))))
                  (not (= (evalh x (ew x y)) 0)))))
  :hints (("Goal" :expand ((evalh x (pad0 (cadr x) (ew (caddr x) y))))
                  :in-theory (disable integerp-evalh evalh-pow-rewrite)
                  :use ((:instance ew-12 (n (ew (caddr x) y)))
		        (:instance ew-10 (n (ew (caddr x) y))
		                         (k (ifix (+ (abs (evalh (cadddr x) (cdr (ew (caddr x) y))))
					             (abs (evalh y (cdr (ew (caddr x) y))))
						     1))))))))

(local-defthmd ew-14
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x)))
    (implies (and (shnfp x)
                  (eq (car x) 'pow))
             (and (not (zp i))
                  (shnfp p)
                  (shnfp q))))
  :hints (("Goal" :expand ((normp x) (shfp x) (shnfp x)))))

(local-defthmd ew-15
  (let ((p (caddr x))
        (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
             (and (integerp (evalh p n))
                  (integerp (evalh q (cdr n)))
                  (integerp (evalh y (cdr n))))))
  :hints (("Goal" :use (ew-14) :expand ((shnfp y)))))

(local (defruled ew-16
  (let ((i (cadr x))
        (p (caddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n)
                  (> (car n) 0))
             (and (integerp (expt (car n) i))
                  (>= (abs (* (expt (car n) i) (evalh p n)))
                      (abs (evalh p n))))))
  :disable abs
  :use (ew-14 ew-15)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
     (implies (and (integerp z)
                   (posp x)
                   (natp i))
              (<= (abs z) (abs (* z (expt x i))))))))))

(local-defthmd ew-17
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n)
                  (> (car n) 0))
             (>= (abs (evalh x n))
                 (- (abs (* (expt (car n) i) (evalh p n)))
                    (abs (evalh q (cdr n)))))))
  :hints (("Goal" :use (ew-14 ew-15 ew-16)
                  :in-theory (disable shnfp-pow-p shnfp-pow-q
                                      integerp-evalh))))

(local-defthm int-abs
  (implies (integerp x) (integerp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(local-defthmd ew-18
  (let ((p (caddr x))
        (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n)
                  (> (car n) 0))
             (>= (abs (evalh x n))
                 (- (abs (evalh p n)) (abs (evalh q (cdr n)))))))
  :hints (("Goal" :use (ew-15 ew-16 ew-17)
                  :in-theory (disable abs shnfp-pow-p shnfp-pow-q
                                      integerp-evalh))))

(local-defthm ew-19
  (implies (all-integers n)
           (all-integers (cdr n))))

(local-defthmd ew-20
  (let* ((q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
  		  (all-integers n))
      (equal (evalh yp (cdr n))
             (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
                (* (evalh y (cdr n)) (evalh y (cdr n)))))))
  :hints (("Goal" :use (ew-14)
           :in-theory (disable shnfp-pow-p shnfp-pow-q))))

(local-defthm hack-2
  (implies (integerp a)
           (>= (* a a) 0))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :cases ((>= a 0)))))

(local-defthmd ew-21
  (let* ((q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
  		  (all-integers n))
      (>= (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
             (* (evalh y (cdr n)) (evalh y (cdr n))))
          0)))
  :hints (("Goal" :use (ew-14 ew-15
                        (:instance hack-2 (a (evalh (cadddr x) (cdr n))))
                        (:instance hack-2 (a (evalh y (cdr n)))))
           :in-theory (disable acl2::normalize-factors-gather-exponents
                               integerp-evalh shnfp-pow-p shnfp-pow-q))))

(local-defthmd ew-22
  (let* ((q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
      (equal (abs (evalh yp (cdr n)))
             (evalh yp (cdr n)))))
  :hints (("Goal" :use (ew-14 ew-20 ew-21)
           :in-theory (disable integerp-evalh shnfp-pow-p shnfp-pow-q))))

(local-defthmd ew-23
  (let* ((q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
      (equal (abs (evalh yp (cdr n)))
             (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
                (* (evalh y (cdr n)) (evalh y (cdr n)))))))
  :hints (("Goal" :use (ew-20 ew-22))))

(local-defthmd ew-24
  (let* ((p (caddr x))
         (q (caddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (eq (car p) 'pow)
                  (all-integers n)
                  (> (car n) 0)
                  (> (abs (evalh p n))
                     (abs (evalh yp (cdr n)))))
             (> (abs (evalh p n))
                (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
                   (* (evalh y (cdr n)) (evalh y (cdr n)))))))
  :hints (("Goal" :use (ew-23))))

(local (acl2::with-arith5-help (defrule hack-3
  (implies (integerp a)
           (>= (* a a) (abs a)))
	   :rule-classes ())))

(local-defthmd ew-25
  (let ((q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
             (>= (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
                    (* (evalh y (cdr n)) (evalh y (cdr n))))
                 (+ (abs (evalh q (cdr n))) (abs (evalh y (cdr n)))))))
  :hints (("Goal" :use (ew-15
                        (:instance hack-3 (a (evalh (cadddr x) (cdr n))))
                        (:instance hack-3 (a (evalh y (cdr n)))))
		  :nonlinearp t
                  :in-theory (disable integerp-evalh))))

(local-defthmd ew-26
  (let* ((p (caddr x)))
    (implies (and (shnfp x)
                  (all-integers n)
		  (eq (car x) 'pow))
             (integerp (evalh p n)))))

(local-defthmd ew-27
  (let ((q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
             (and (integerp (+ (* (evalh q (cdr n)) (evalh q (cdr n)))
                               (* (evalh y (cdr n)) (evalh y (cdr n)))))
                  (integerp (+ (abs (evalh q (cdr n))) (abs (evalh y (cdr n))))))))
  :hints (("Goal" :use (ew-15) :in-theory (disable integerp-evalh))))

(local-defthm hack-4
  (implies (and (integerp a) (integerp b) (integerp c)
                (> a b) (>= b c))
	   (> a c))
  :rule-classes ())

(local-defthmd ew-28
  (let* ((p (caddr x))
         (q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (eq (car p) 'pow)
                  (all-integers n)
                  (> (car n) 0)
                  (> (abs (evalh p n))
                     (abs (evalh yp (cdr n)))))
             (> (abs (evalh p n))
                (+ (abs (evalh q (cdr n))) (abs (evalh y (cdr n)))))))
  :hints (("Goal" :use (ew-26 ew-27 ew-24 ew-25 ew-15 ew-23
                        (:instance hack-4 (a (abs (evalh (caddr x) n)))
			                  (b (+ (* (evalh (cadddr x) (cdr n)) (evalh (cadddr x) (cdr n)))
                                                (* (evalh y (cdr n)) (evalh y (cdr n)))))
					  (c (+ (abs (evalh (cadddr x) (cdr n))) (abs (evalh y (cdr n)))))))
		  :in-theory '(int-abs))))

(local-defthmd ew-29
  (implies (and (shnfp x) (all-integers n))
           (integerp (evalh x n))))

(local-defthm hack-5
 (implies (and (integerp x) (integerp p) (integerp q) (integerp y)
               (>= x (- p q)) (> p (+ q y)))
	  (> x y))
  :rule-classes ())

(local-defthmd ew-30
  (let* ((p (caddr x))
         (q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y))))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (eq (car p) 'pow)
		  (all-integers n)
                  (> (car n) 0)
                  (> (abs (evalh p n))
                     (abs (evalh yp (cdr n)))))
             (> (abs (evalh x n)) (abs (evalh y (cdr n))))))
  :hints (("Goal" :use (ew-29 ew-15 ew-18 ew-28
                        (:instance hack-5 (x (abs (evalh x n)))
			                  (p (abs (evalh (caddr x) n)))
					  (q (abs (evalh (cadDdr x) (cdr n))))
					  (y (abs (evalh y (cdr n))))))
		  :in-theory '(int-abs))))

(local-defthmd ew-31
  (let* ((p (caddr x))
         (q (cadddr x))
         (yp (norm-add (norm-mul q q) (norm-mul y y)))
         (n (ew p yp)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (eq (car p) 'pow)
                  (> (car n) 0)
                  (> (abs (evalh p n))
                     (abs (evalh yp (cdr n)))))
             (> (abs (evalh x n)) (abs (evalh y (cdr n))))))
  :hints (("Goal" :use ((:instance ew-30
                                   (n (ew (caddr x)
				          (norm-add (norm-mul (cadddr x) (cadddr x)) (norm-mul y y))))))
		  :in-theory '(ew-11))))

(local-defthmd ew-32
  (let* ((q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow))
      (shnfp (norm-add (norm-mul q q) (norm-mul y y)))))
  :hints (("Goal" :use (ew-14)
           :in-theory (disable shnfp-pow-p shnfp-pow-q))))

(local-defthm ew-33
  (implies (and (shnfp x) (eq (car x) 'pow))
           (not (= (caddr x) 0)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (shfp x) (normp x)))))

(local-defthm ew-34
  (implies (and (shnfp x) (eq (car x) 'pop))
           (and (not (zp (cadr x)))
	        (shnfp (caddr x))
		(eq (caaddr x) 'pow)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (shfp x) (normp x)))))

(local-in-theory (disable evalh-int shnfp-pow-p shnfp-pow-q shnfp-norm-add shnfp-norm-mul shfp-pop-pow-atom evalh-norm-add evalh-norm-mul evalh-pow-rewrite ew-11 ew-19))

(local-defthmd ew-lemma
  (implies (and (shnfp x)
                (not (= x 0))
		(shnfp y))
	   (let ((n (ew x y)))
	     (and (not (= (evalh x n) 0))
	          (implies (eq (car x) 'pow)
		           (and (> (car n) 0)
			        (> (abs (evalh x n)) (abs (evalh y (cdr n)))))))))
  :hints (("Subgoal *1/4" :expand ((ew x y))
                          :use (ew-31 ew-32 ew-14 shfp-pop-pow-atom
                                (:instance shfp-pop-pow-atom (x (caddr x)))))
          ("Subgoal *1/3" :expand ((ew x y))
                          :use (ew-13 ew-14 shfp-pop-pow-atom shnfp-pow-p ew-33
                                (:instance shfp-pop-pow-atom (x (caddr x)))))
          ("Subgoal *1/2" :expand ((ew x y))
                          :use (ew-3 ew-34))
          ("Subgoal *1/1" :expand ((ew x y) (:free (n) (evalh x n)))
                          :use (ew-1))))

(defthmd evalh-not-zero
  (implies (and (shnfp x)
                (not (= x 0)))
	   (let ((n (evalh-witness x)))
	     (and (all-integers n)
                  (not (equal (evalh x n) 0)))))
  :hints (("Goal" :in-theory (enable ew-11 evalh-witness) :use ((:instance ew-lemma (y 1))))))

(local-defthm na0-1
  (implies (equal (norm-pop i p) 0)
           (equal p 0))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-pop i p)))))

(local-defthm na0-2
  (implies (equal (norm-pow i p q) 0)
           (and (equal p 0) (equal q 0)))
  :rule-classes ()
  :hints (("Goal" :expand ((:free (p q) (norm-pow i p q))) :use ((:instance na0-1 (i 1) (p q))))))

(local-defthm na0-3
  (implies (and (shnfp x)
                (shnfp y)
		(or (atom x) (atom y))
		(equal (norm-add x y) 0))
           (equal y (norm-neg x)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (add-int x y) (add-int y x) (norm-add x y)))))

(defthmd norm-neg-norm-neg
  (implies (shfp x)
           (equal (norm-neg (norm-neg x)) x))
  :hints (("Goal" :expand ((shfp x)))))

(local-defthmd na0-4
  (implies (and (shnfp x)
                (shnfp y)
		(eq (car x) 'pop)
		(equal (norm-add x y) 0))
           (equal (car y) 'pop))
  :hints (("Goal" :expand ((add-int x y) (add-int y x) (shnfp y) (shfp y) (norm-add x y)))))

(local-defthm na0-5
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (= i j))
	     (equal (norm-add p q) 0)))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-4 (:instance na0-1 (i (cadr x)) (p (norm-add (caddr x) (caddr y))))))))

(local-defthm na0-6
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (= i j)
		  (implies (equal (norm-add p q) 0)
		           (equal q (norm-neg p))))
	     (equal (norm-neg x) y)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (norm-neg x))
                  :use (na0-4 na0-5))))

(local-defthm na0-7
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (> i j))
	     (equal (norm-add (list 'pop (- i j) p) q) 0)))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-4 (:instance na0-1 (i (cadr y))
		                               (p (norm-add (list 'pop (- (cadr x) (cadr y)) (caddr x)) (caddr y))))))))

(local-defthm na0-8
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (> i j)
		  (implies (equal (norm-add (list 'pop (- i j) p) q) 0)
		           (equal q (norm-neg (list 'pop (- i j) p)))))
	     (equal (caaddr y) 'pop)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (:free (i) (norm-neg (list 'pop i p))))
                  :use (na0-4 na0-7))))

(local-defthm na0-9
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (implies (equal (norm-add (list 'pop (- i j) p) q) 0)
		           (equal q (norm-neg (list 'pop (- i j) p)))))
	     (not (> i j))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (normp y))
                  :use (na0-4 na0-8))))

(local-defthm na0-10
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (< i j))
	     (equal (norm-add (list 'pop (- j i) q) p) 0)))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-4 (:instance na0-1 (i (cadr x))
		                               (p (norm-add (list 'pop (- (cadr y) (cadr x)) (caddr y)) (caddr x))))))))

(local-defthm na0-11
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (< i j)
		  (implies (equal (norm-add (list 'pop (- j i) q) p) 0)
		           (equal p (norm-neg (list 'pop (- j i) q)))))
	     (equal (caaddr x) 'pop)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (shfp x) (:free (i) (norm-neg (list 'pop i p))))
                  :use (na0-4 na0-10))))

(local-defthm na0-12
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (implies (equal (norm-add (list 'pop (- j i) q) p) 0)
		           (equal p (norm-neg (list 'pop (- j i) q)))))
	     (not (< i j))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (normp x))
                  :use (na0-4 na0-11))))

(local-defthmd na0-13
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (implies (and (= i j) (equal (norm-add p q) 0))
		           (equal q (norm-neg p)))
		  (implies (and (> i j) (equal (norm-add (list 'pop (- i j) p) q) 0))
		           (equal q (norm-neg (list 'pop (- i j) p))))
		  (implies (and (< i j) (equal (norm-add (list 'pop (- j i) q) p) 0))
		           (equal p (norm-neg (list 'pop (- j i) q)))))
	     (equal (norm-neg x) y)))
  :hints (("Goal" :expand ((shnfp x) (normp x))
                  :use (na0-6 na0-9 na0-12))))

(local-defthmd na0-14
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0))
	     (and (shnfp p)
	          (shnfp q)
		  (implies (> i j) (shnfp (list 'pop (- i j) p)))
		  (implies (< i j) (shnfp (list 'pop (- j i) q))))))
  :hints (("Goal" :use (na0-4)
                  :expand ((:free (x) (shnfp x)) (normp x) (normp y)
                           (:free (i p) (shnfp (list 'pop i p)))
                           (:free (i p) (normp (list 'pop i p)))))))

(local-defthmd na0-15
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pop)
		  (equal (norm-add x y) 0)
		  (implies (and (= i j)
		                (shnfp p)
                                (shnfp q)
		                (equal (norm-add p q) 0))
		           (equal q (norm-neg p)))
		  (implies (and (> i j)
		                (shnfp (list 'pop (- i j) p))
                                (shnfp q)
		                (equal (norm-add (list 'pop (- i j) p) q) 0))
		           (equal q (norm-neg (list 'pop (- i j) p))))
		  (implies (and (< i j)
		                (shnfp (list 'pop (- j i) q))
		                (shnfp p)
		                (equal (norm-add (list 'pop (- j i) q) p) 0))
		           (equal p (norm-neg (list 'pop (- j i) q)))))
	     (equal (norm-neg x) y)))
  :hints (("Goal" :use (na0-14 na0-13))))

(local-defthmd na0-16
  (implies (and (shnfp x)
                (shnfp y)
		(eq (car x) 'pow)
		(equal (norm-add x y) 0))
           (equal (car y) 'pow))
  :hints (("Goal" :expand ((add-int x y) (add-int y x) (shnfp y) (shfp y) (norm-add x y)))))

(local-defthm na0-17
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (= i j))
	     (and (equal (norm-add p r) 0)
	          (equal (norm-add q s) 0))))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-16
		        (:instance na0-2 (i (cadr x)) (p (norm-add (caddr x) (caddr y))) (q (norm-add (cadddr x) (cadddr y))))))))

(local-defthm na0-18
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (= i j)
		  (implies (equal (norm-add p r) 0)
		           (equal r (norm-neg p)))
		  (implies (equal (norm-add q s) 0)
		           (equal s (norm-neg q))))
	     (equal (norm-neg x) y)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (norm-neg x))
                  :use (na0-16 na0-17))))

(local-defthm na0-19
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (> i j))
	     (and (equal (norm-add (list 'pow (- i j) p 0) r) 0)
	          (equal (norm-add q s) 0))))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-16
		        (:instance na0-2 (i (cadr y))
		                         (p (norm-add (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) (caddr y)))
					 (q (norm-add (cadddr x) (cadddr y))))))))

(local-defthm na0-20
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (> i j)
		  (implies (equal (norm-add (list 'pow (- i j) p 0) r) 0)
		           (equal r (norm-neg (list 'pow (- i j) p 0)))))
	     (and (eq (car r) 'pow)
	          (= (cadddr r) 0))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (:free (i) (norm-neg (list 'pow i p 0))))
                  :use (na0-12 na0-19))))

(local-defthm na0-21
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (implies (equal (norm-add (list 'pow (- i j) p 0) r) 0)
		           (equal r (norm-neg (list 'pow (- i j) p 0)))))
	     (not (> i j))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (normp y))
                  :use (na0-16 na0-20))))

(local-defthm na0-22
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (< i j))
	     (and (equal (norm-add (list 'pow (- j i) r 0) p) 0)
	          (equal (norm-add s q) 0))))
  :rule-classes ()
  :hints (("Goal" :expand ((norm-add x y))
                  :use (na0-16
		        (:instance na0-2 (i (cadr x))
		                         (p (norm-add (list 'pow (- (cadr y) (cadr x)) (caddr y) 0) (caddr x)))
					 (q (norm-add (cadddr y) (cadddr x))))))))

(local-defthm na0-23
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (< i j)
		  (implies (equal (norm-add (list 'pow (- j i) r 0) p) 0)
		           (equal p (norm-neg (list 'pow (- j i) r 0)))))
	     (and (eq (car p) 'pow)
	          (= (cadddr p) 0))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp y) (shfp y) (:free (i) (norm-neg (list 'pow i p 0))))
                  :use (na0-12 na0-22))))

(local-defthm na0-24
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (implies (equal (norm-add (list 'pow (- j i) r 0) p) 0)
		           (equal p (norm-neg (list 'pow (- j i) r 0)))))
	     (not (< i j))))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (normp x))
                  :use (na0-16 na0-23))))

(local-defthm na0-25
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (implies (and (= i j) (equal (norm-add p r) 0))
		           (equal r (norm-neg p)))
		  (implies (and (= i j) (equal (norm-add q s) 0))
		           (equal s (norm-neg q)))
		  (implies (and (> i j) (equal (norm-add (list 'pow (- i j) p 0) r) 0))
		           (equal r (norm-neg (list 'pow (- i j) p 0))))
		  (implies (and (< i j) (equal (norm-add (list 'pow (- j i) r 0) p) 0))
		           (equal p (norm-neg (list 'pow (- j i) r 0)))))
	     (equal (norm-neg x) y)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (normp x))
                  :use (na0-18 na0-21 na0-24))))

(local-defthmd na0-26
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0))
	     (and (shnfp p)
	          (shnfp q)
	          (shnfp r)
	          (shnfp s)
		  (implies (> i j) (shnfp (list 'pow (- i j) p 0)))
		  (implies (< i j) (shnfp (list 'pow (- j i) r 0))))))
  :hints (("Goal" :use (na0-16)
                  :expand ((:free (x) (shnfp x)) (normp x) (normp y)
                           (:free (i p q) (shnfp (list 'pow i p q)))
                           (:free (i p q) (normp (list 'pow i p q)))))))

(local-defthmd na0-27
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
		  (equal (norm-add x y) 0)
		  (implies (and (= i j)
		                (shnfp p)
				(shnfp r)
				(equal (norm-add p r) 0))
		           (equal r (norm-neg p)))
		  (implies (and (= i j)
		                (shnfp q)
				(shnfp s)
				(equal (norm-add q s) 0))
		           (equal s (norm-neg q)))
		  (implies (and (> i j)
		                (shnfp (list 'pow (- i j) p 0))
				(shnfp r)
				(equal (norm-add (list 'pow (- i j) p 0) r) 0))
		           (equal r (norm-neg (list 'pow (- i j) p 0))))
		  (implies (and (< i j)
		                (shnfp (list 'pow (- j i) r 0))
				(shnfp p)
				(equal (norm-add (list 'pow (- j i) r 0) p) 0))
		           (equal p (norm-neg (list 'pow (- j i) r 0)))))
	     (equal (norm-neg x) y)))
  :hints (("Goal" :use (na0-26 na0-25))))

(in-theory (enable norm-add))

(local-defthm norm-add-0
  (implies (and (shnfp x)
                (shnfp y)
		(equal (norm-add x y) 0))
           (equal (norm-neg x) y))
  :rule-classes ()
  :hints (("Goal" :induct (norm-add x y) :expand ((shnfp x) (shfp x) (shnfp y) (shfp y) (norm-add x y)))
          ("Subgoal *1/13" :use (na0-27))
          ("Subgoal *1/12" :use (na0-27))
          ("Subgoal *1/11" :use (na0-27))
          ("Subgoal *1/10" :use (na0-16))
          ("Subgoal *1/9" :use (na0-16))
          ("Subgoal *1/5" :use (na0-15))
          ("Subgoal *1/4" :use (na0-15))
          ("Subgoal *1/3" :use (na0-15))
          ("Subgoal *1/2" :use (na0-4 na0-16))
          ("Subgoal *1/1" :use (na0-3))))

(defthmd evalh-not-equal
  (let ((n (evalh-witness (norm-add (norm-neg y) x))))
    (implies (and (shnfp x)
                  (shnfp y)
		  (not (equal x y)))
	     (not (equal (evalh x n) (evalh y n)))))
  :hints (("Goal" :in-theory (enable evalh-norm-add)
                  :use ((:instance norm-neg-norm-neg (x y))
                        (:instance norm-add-0 (x (norm-neg y)) (y x))
			(:instance evalh-not-zero (x (norm-add (norm-neg y) x)))))))

(local-defun all0p (n)
  (if (consp n)
      (and (= (car n) 0)
           (all0p (cdr n)))
    t))

(local-defun append0p (n n0)
  (if (consp n)
      (and (consp n0)
           (= (car n) (car n0))
           (append0p (cdr n) (cdr n0)))
    (all0p n0)))

(local-defthm append0p-cdr
  (implies (append0p n n0)
           (append0p (cdr n) (cdr n0))))

(local-defthm append0p-nthcdr
  (implies (append0p n n0)
           (append0p (nthcdr k n) (nthcdr k n0))))

(local-in-theory (enable evalh))

(local-in-theory (disable ACL2::REDUCE-ADDITIVE-CONSTANT-<))

(local-defun induct-evalh-2 (x n n0)
  (if (atom x)
      t
    (case (car x)
      (pop (induct-evalh-2 (caddr x) (nthcdr (cadr x) n) (nthcdr (cadr x) n0)))
      (pow (and (induct-evalh-2 (caddr x) n n0)
                (induct-evalh-2 (cadddr x) (cdr n) (cdr n0))))
      (t (list n n0)))))

(local-defthm induct-evalh-2-non-nil
  (induct-evalh-2 x n n0))

(local-defthm evalh-append0p
  (implies (and (shnfp x) (append0p n n0))
           (equal (evalh x n)
                  (evalh x n0)))
  :hints (("Goal" :induct (induct-evalh-2 x n n0))
          ("Subgoal *1/3" :expand ((evalh x n) (evalh x n0) (shnfp x) (shfp x) (normp x)))
          ("Subgoal *1/2" :expand ((evalh x n) (evalh x n0) (shnfp x) (shfp x) (normp x)))))

(defun list0 (k)
  (if (zp k)
      ()
    (cons 0 (list0 (1- k)))))

(local-defthm append0p-list0
  (append0p n (append n (list0 k))))

(local-defthmd evalh-append-0
  (implies (shnfp x)
           (equal (evalh x (append n (list0 k)))
	          (evalh x n)))
  :hints (("Goal" :use ((:instance evalh-append0p (n0 (append n (list0 k))))))))

(defund evalp-witness (x y vars)
   (let ((n (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars)))))
     (append n (list0 (- (len vars) (len n))))))

(local-defthm all-ints-list0
  (all-integers (list0 k)))

(local-defthm all-ints-append
  (implies (and (all-integers a)
                (all-integers b))
           (all-integers (append a b))))

(defthmd all-ints-evalp-witness
  (all-integers (evalp-witness x y vars))
  :hints (("Goal" :expand ((evalp-witness x y vars) (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars)))))))

(local-defthm len-list0
  (equal (len (list0 k))
         (nfix k)))

(local-defthm len-append
  (equal (len (append a b))
         (+ (len a) (len b))))

(local-defthmd len-evalp-witness
  (>= (len (evalp-witness x y vars))
      (len vars))
  :hints (("Goal" :expand ((evalp-witness x y vars)))))

(defthm evalp-not-equal
  (let ((a (pairlis$ vars (evalp-witness x y vars))))
    (implies (and (distinct-symbols vars)
                  (polyp x vars)
  		  (polyp y vars)
		  (equal (evalp x a) (evalp y a)))
	     (equal (norm x vars)
	            (norm y vars))))
  :rule-classes ()
  :hints (("Goal" :expand ((evalp-witness x y vars)) :in-theory (enable evalh-append-0)
                  :use (len-evalp-witness all-ints-evalp-witness
		        (:instance evalh-append-0 (x (norm x vars))
			                          (n (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars))))
						  (k (- (len vars)
						        (len (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars)))))))
		        (:instance evalh-append-0 (x (norm y vars))
			                          (n (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars))))
						  (k (- (len vars)
						        (len (evalh-witness (norm-add (norm-neg (norm y vars)) (norm x vars)))))))
		        (:instance evalh-not-equal (x (norm x vars)) (y (norm y vars)))
                        (:instance evalh-norm (vals (evalp-witness x y vars)))
                        (:instance evalh-norm (x y) (vals (evalp-witness x y vars)))))))

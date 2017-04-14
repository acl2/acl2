(in-package "RTL")

(include-book "std/util/defrule" :dir :system)

(include-book "rtl/rel11/lib/basic" :dir :system)

(include-book "rtl/rel11/lib/util" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))


;; [Jared] trying to speed up this book
;; [Dima] Remove those rules which are already disabled using with-arith5-help
(local (deftheory jared-disables
         '(default-car
           default-cdr)))

(local (in-theory (disable jared-disables)))


;;*********************************************************************************
;;                              Polynomial Terms
;;*********************************************************************************

(defn distinct-symbols (vars)
  (if (consp vars)
      (and (distinct-symbols (cdr vars))
           (symbolp (car vars))
           (not (member (car vars) (cdr vars))))
    (null vars)))

(defrule eqlable-listp-distinct-symbols
  (implies (distinct-symbols vars)
           (eqlable-listp vars)))

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

(defn all-integers (vals)
  (if (consp vals)
      (and (all-integers (cdr vals))
           (integerp (car vals)))
    (null vals)))

(defrule true-listp-all-integers
  (implies (all-integers vals)
           (true-listp vals)))

(defthm all-integers-nthcdr
  (implies (all-integers vals)
           (all-integers (nthcdr n vals))))

(defun evalh (x vals)
  (declare (xargs :guard (and (shfp x)
                              (all-integers vals))
                  :verify-guards nil))
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

(defun shf-normp (x)
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

(defn shnfp (x)
  (and (shfp x) (shf-normp x)))

(defthm shnfp-shfp
  (implies (shnfp x)
           (shfp x))
  ;; [Jared] trying to cheapen this very expensive rule.
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(local (defruled shnfp-pop-structure
  (implies (and (shnfp x)
                (eql (car x) 'pop))
           (and (consp (cdr x))
                (consp (cddr x))))
  :enable shnfp))

(local (defruled shnfp-pow-structure
  (implies (and (shnfp x)
                (eql (car x) 'pow))
           (and (consp (cdr x))
                (consp (cddr x))
                (consp (cdddr x))))
  :enable shnfp))

(local (defruled shnfp-atom
  (implies (and (shnfp x)
                (not (consp x)))
           (integerp x))))

(local (defruled shnfp-forward
  (implies (shnfp x)
           (or (integerp x)
               (and (consp x)
                    (or (eql (car x) 'pop)
                        (eql (car x) 'pow)))))
  :rule-classes :forward-chaining))

(local (defruled shnfp-label
  (implies (and (shnfp x)
                (consp x))
           (and (implies (not (equal (car x) 'pop))
                         (equal (equal (car x) 'pow) t))
                (implies (not (equal (car x) 'pow))
                         (equal (equal (car x) 'pop) t))))))

(local (defrule shnfp-split
  (implies (shnfp p)
           (or (integerp p)
               (and (consp p)
                    (or (eql (car p) 'pop)
                        (eql (car p) 'pow)))))
  :rule-classes ()))

(local (defruled shnfp-pow-i-type
  (implies (and (shnfp x)
                (eql (car x) 'pow))
           (posp (cadr x)))
  :rule-classes :type-prescription
  :expand (shf-normp x)))

(defthm shnfp-pow-q
  (implies (and (shnfp x) (eql (car x) 'pow))
           (shnfp (cadddr x))))

(defthm shnfp-pow-p
  (implies (and (shnfp x) (eql (car x) 'pow))
           (shnfp (caddr x))))

(local (defruled shnfp-pow-p-ext
  (implies (and (shnfp x) (eql (car x) 'pow))
           (and (not (equal (caddr x) 0))
                (not (equal (cadddr (caddr x)) 0))))))

(local (defruled shnfp-pop-i-type
  (implies (and (shnfp x)
                (eql (car x) 'pop))
           (posp (cadr x)))
  :rule-classes :type-prescription
  :expand (shf-normp x)))

(local (defruled shnfp-pop-p
  (implies (and (shnfp x) (eql (car x) 'pop))
           (and (shnfp (caddr x))
                (consp (caddr x))
                (equal (car (caddr x)) 'pow)))))

(defthm shfp-pop-pow-atom
  (implies (and (shfp x) (not (eql (car x) 'pow)) (not (eql (car x) 'pop)))
           (atom x)))

(defthm shnfp-int
  (implies (integerp x)
           (shnfp x)))

(local (defruled shnfp-pop-suff
  (implies (and (posp i)
                (shnfp p)
                (eql (car p) 'pow))
           (shnfp (list 'pop i p)))))

(local (defruled shnfp-pow-suff
  (implies (and (posp i)
                (shnfp p)
                (shnfp q)
                (or (and (atom p) (not (= p 0)))
                    (eql (car p) 'pop)
                    (and (eql (car p) 'pow) (not (= (cadddr p) 0)))))
           (shnfp (list 'pow i p q)))))

(local (defruled evalh-pop
  (implies (and (shnfp x)
                (equal (car x) 'pop))
           (equal (evalh x vals)
                  (evalh (caddr x) (nthcdr (cadr x) vals))))))

(local (defruled evalh-pop-2
  (equal (evalh (list 'pop i p) vals)
         (evalh p (nthcdr i vals)))))

(local (defruled evalh-pow
  (implies (and (shnfp x)
                (equal (car x) 'pow))
           (equal (evalh x vals)
                  (+ (* (expt (if (consp vals) (car vals) 0) (cadr x))
                        (evalh (caddr x) vals))
                     (evalh (cadddr x) (cdr vals)))))))

(local (defruled evalh-pow-2
  (implies (and (shnfp x)
                (equal (car x) 'pow))
           (equal (evalh (list 'pow i p q) vals)
                  (+ (* (expt (if (consp vals) (car vals) 0) i)
                        (evalh p vals))
                     (evalh q (cdr vals)))))))

(defruled integerp-is-acl2-numberp
  (implies (integerp x)
           (acl2-numberp x)))

(defrule integerp-evalh
  (implies (and (shfp x)
                (all-integers vals))
           (integerp (evalh x vals)))
  ;; [Jared] dropping this rule-classes because the type-prescription rule
  ;; seems to be very expensive and the hyps don't look like type prescription
  ;; reasoning stuff anyway.
  ;; :rule-classes (:type-prescription :rewrite)
  :enable acl2::expt-type-prescription-integerp-base)

(acl2::with-arith5-help
 (verify-guards evalh))

(local (defruled integerp-evalh-shnfp
  (implies (and (shnfp x)
                (all-integers vals))
           (integerp (evalh x vals)))))

;; Two theories shnfp-old and shnfp-new for reasoning about shnfp.

;; Old theory enables definition and a few public theorems.
(local (deftheory shnfp-old
         '(shnfp
           shnfp-pow-p
           shnfp-pow-q
           shfp-pop-pow-atom
           shnfp-int
           integerp-evalh)))

;; New theory disables definition but provides full set of lemmas.
;; Forward rule shnfp-forward is intentionally not in the theory.
(local (deftheory shnfp-new
         '(shnfp-atom
           shnfp-label
           shnfp-pow-i-type
           shnfp-pow-q
           shnfp-pow-p
           shnfp-pow-p-ext
           shnfp-pop-i-type
           shnfp-pop-p
           shnfp-int
           shnfp-pop-suff
           shnfp-pow-suff
           evalh-pop
           evalh-pop-2
           evalh-pow
           evalh-pow-2
           integerp-evalh-shnfp)))

(local (deftheory shnfp-guard
         (union-theories '(;shnfp-atom-structure
                           shnfp-pop-structure
                           shnfp-pow-structure)
                         (theory 'shnfp-new))))

(local (in-theory (disable shnfp-old)))

;; We shall define a function norm that computes a SHNF
;; representing a polynomial with respect to a given variable ordering.

;; norm-pop normalizes (POP i p), where p is normal:

(defun norm-pop (i p)
  (declare (xargs :guard (and (natp i)
                              (shnfp p))
                  :guard-hints (("goal" :in-theory (enable shnfp-guard)))))
  (if (or (= i 0) (atom p))
      p
    (if (eql (car p) 'pop)
        (list 'pop (+ i (cadr p)) (caddr p))
      (list 'pop i p))))

(defrule norm-pop-shnfp
  (implies (and (shnfp p) (natp i))
           (shnfp (norm-pop i p)))
  :enable shnfp-new)

(defthm norm-pop-normp
  (implies (and (shnfp p) (natp i))
           (shf-normp (norm-pop i p)))
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

(defrule norm-pop-evalh
  (implies (and (shnfp p) (natp i))
           (equal (evalh (norm-pop i p) n)
                  (evalh `(pop ,i ,p) n)))
  :enable shnfp-new)

(in-theory (disable norm-pop))

;; norm-pow normalizes (POW i p q), where p and p are normal:

(defun norm-pow (i p q)
  (declare (xargs :guard (and (natp i)
                              (shnfp p)
                              (shnfp q))
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard)))))
  (if (equal p 0)
      (norm-pop 1 q)
    (if (and (consp p) (eql (car p) 'pow) (equal (cadddr p) 0))
        (list 'pow (+ i (cadr p)) (caddr p) q)
      (list 'pow i p q))))

(defrule norm-pow-shnfp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shnfp (norm-pow i p q)))
  :enable shnfp-new)

(defthm norm-pow-normp
  (implies (and (shnfp p) (shnfp q) (not (zp i)))
           (shf-normp (norm-pow i p q)))
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
                      (* (expt x i) z (expt x j)))))))
  :enable shnfp-new)

(in-theory (disable norm-pow))

;; norm-var handles the case where the polynomial is a simple variable:

(defun var-index (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
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
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
  (norm-pop (var-index x vars) '(pow 1 1 0)))

(defthm shnfp-norm-var
  (implies (member x vars)
           (shnfp (norm-var x vars))))

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
  :disable norm-var)

;; norm-add computes a normal representation of (+ a b),
;; given normal representations x and y of a and b.

(in-theory (disable norm-var))

;; add-int handles the case where x is an integer:

(defun add-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (shnfp y))
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard)))))
  (if (atom y)
      (+ x y)
    (case (car y)
      (pow (list 'pow (cadr y) (caddr y) (add-int x (cadddr y))))
      (pop (list 'pop (cadr y) (add-int x (caddr y)))))))

(defthm normp-add-int
  (implies (and (shf-normp x)
                (shf-normp y)
                (atom x))
           (shf-normp (add-int x y)))
  :hints (("Subgoal *1/5" :expand ((add-int x (caddr y))))))

(defrule shnfp-add-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (shnfp (add-int x y)))
  :prep-lemmas
  ((defrule lemma
     (implies (shnfp y)
              (equal (car (add-int x y)) (car y)))
     :enable shnfp-label))
  :enable (shnfp-new shnfp-forward))

(defrule evalh-add-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (equal (evalh (add-int x y) vals)
                  (+ (evalh x vals) (evalh y vals))))
  :enable (acl2::|(* 0 x)|
           acl2::|arith (expt 0 n)|
           shnfp-new))

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
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp x)
                              (shnfp y))
                  :verify-guards nil))
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

(defrule shnfp-norm-add
  (implies (and (shnfp x)
                (shnfp y))
           (shnfp (norm-add x y)))
  :enable shnfp-new)

(verify-guards norm-add
  :hints (("Goal" :in-theory (enable shnfp-guard))))

(defthm normp-norm-add
  (implies (and (shnfp x)
                (shnfp y))
           (shf-normp (norm-add x y)))
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

(defun car0 (vals)
  (if (consp vals) (car vals) 0))

(defthm evalh-pow-rewrite
  (implies (eql (car x) 'pow)
           (equal (evalh x vals)
                  (+ (* (expt (car0 vals) (cadr x))
                        (evalh (caddr x) vals))
                     (evalh (cadddr x) (cdr vals))))))

(in-theory (disable shf-normp norm-add evalh))

(local (defrule evalh-add-pop-pop
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (if (= i j)
                      (equal (evalh (norm-add p q) (nthcdr i vals))
                             (+ (evalh p (nthcdr i vals))
                                (evalh q (nthcdr i vals))))
                    (if (> i j)
                        (equal (evalh (norm-add (list 'pop (- i j) p) q) (nthcdr j vals))
                               (+ (evalh (list 'pop (- i j) p) (nthcdr j vals))
                                  (evalh q (nthcdr j vals))))
                      (equal (evalh (norm-add (list 'pop (- j i) q) p) (nthcdr i vals))
                             (+ (evalh (list 'pop (- j i) q) (nthcdr i vals))
                                (evalh p (nthcdr i vals)))))))
             (equal (evalh (norm-add x y) vals)
                    (+ (evalh x vals) (evalh y vals)))))
  :expand (norm-add x y)
  :enable shnfp-new
  :disable (evalh-pow evalh-pow-rewrite)))

(local (defrule evalh-add-pop-pow
  (let ((i (cadr x)) (p (caddr x))
        (r (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (if (= i 1)
                      (equal (evalh (norm-add r p) (cdr vals))
                             (+ (evalh r (cdr vals))
                                (evalh p (cdr vals))))
                    (equal (evalh (norm-add r (list 'pop (1- i) p)) (cdr vals))
                           (+ (evalh r (cdr vals))
                              (evalh (list 'pop (1- i) p) (cdr vals))))))
             (equal (evalh (norm-add x y) vals)
                    (+ (evalh x vals) (evalh y vals)))))
  :expand (norm-add x y)
  :enable shnfp-new
  :disable expt))

(local (defrule evalh-add-pow-pop
  (let ((i (cadr y)) (p (caddr y))
        (r (cadddr x)))
    (implies
     (and (shnfp x)
          (shnfp y)
          (eql (car x) 'pow)
          (eql (car y) 'pop)
          (if (= i 1)
              (equal (evalh (norm-add r p) (cdr vals))
                     (+ (evalh r (cdr vals))
                        (evalh p (cdr vals))))
            (equal (evalh (norm-add r (list 'pop (1- i) p)) (cdr vals))
                   (+ (evalh r (cdr vals))
                      (evalh (list 'pop (1- i) p) (cdr vals))))))
     (equal (evalh (norm-add x y) vals)
            (+ (evalh x vals) (evalh y vals)))))
  :expand (norm-add x y)
  :enable shnfp-new
  :disable expt))

(local (defrule evalh-add-pow-pow
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies
     (and (shnfp x)
          (shnfp y)
          (all-integers vals)
          (eql (car x) 'pow)
          (eql (car y) 'pow)
          (if (= i j)
              (and (equal (evalh (norm-add p r) vals)
                          (+ (evalh p vals)
                             (evalh r vals)))
                   (equal (evalh (norm-add q s) (cdr vals))
                          (+ (evalh q (cdr vals))
                             (evalh s (cdr vals)))))
            (if (> i j)
                (and (equal (evalh (norm-add (list 'pow (- i j) p 0) r) vals)
                            (+ (evalh (list 'pow (- i j) p 0) vals)
                               (evalh r vals)))
                     (equal (evalh (norm-add q s) (cdr vals))
                            (+ (evalh q (cdr vals))
                               (evalh s (cdr vals)))))
              (and (equal (evalh (norm-add (list 'pow (- j i) r 0) p) vals)
                          (+ (evalh (list 'pow (- j i) r 0) vals)
                             (evalh p vals)))
                   (equal (evalh (norm-add s q) (cdr vals))
                          (+ (evalh s (cdr vals))
                             (evalh q (cdr vals))))))))
     (equal (evalh (norm-add x y) vals)
            (+ (evalh x vals) (evalh y vals)))))
  :expand (norm-add x y)
  :cases ((= (cadr x) (cadr y))
          (> (cadr x) (cadr y))
          (< (cadr x) (cadr y)))
  :hints (("subgoal 2" :use (:instance lemma
                                       (i (cadr x))
                                       (j (cadr y))
                                       (p (evalh (caddr x) vals))
                                       (r (evalh (caddr y) vals))))
          ("subgoal 1" :use (:instance lemma
                                       (i (cadr y))
                                       (j (cadr x))
                                       (p (evalh (caddr y) vals))
                                       (r (evalh (caddr x) vals)))))
  :enable shnfp-new
  :disable (all-integers evalh-pow-rewrite)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (let ((x (car0 vals)))
        (implies (and (all-integers vals)
                      (posp i)
                      (posp j))
                 (equal (* (expt x j) (+ (* (expt x (- i j)) p) r))
                        (+ (* (expt x i) p)
                           (* (expt x j) r))))))))))

(defrule evalh-norm-add
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-add x y) vals)
                  (+ (evalh x vals)
                     (evalh y vals))))
  :induct (norm-add-induct x y vals)
  :enable (shnfp-new shnfp-forward)
  :disable (evalh-pow
            evalh-pow-rewrite
;           rules below may be disabled optionally
            expt
            evalh-pop
            evalh-pop-2
            evalh-pow-2
            shnfp-atom
            shnfp-int))

(in-theory (enable shf-normp evalh))

;; The remaining cases are handled by norm-neg, norm-mul, and norm-expt:

(defun norm-neg (x)
  (declare (xargs :guard (shnfp x)
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard)))))
  (if (atom x)
      (- x)
    (case (car x)
      (pop (list 'pop (cadr x) (norm-neg (caddr x))))
      (pow (list 'pow (cadr x) (norm-neg (caddr x)) (norm-neg (cadddr x)))))))

(local (defrule norm-neg-0
  (implies (and (shnfp x) (not (equal x 0)))
           (not (equal (norm-neg x) 0)))
  :enable (shnfp-new shnfp-forward)))

(defrule shnfp-norm-neg
  (implies (shnfp x)
           (shnfp (norm-neg x)))
  :enable (shnfp-old)
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
      :disable (evalh norm-neg))))
  :enable shnfp-new)

(defun mul-int (x y)
  (declare (xargs :guard (and (integerp x)
                              (shnfp y))
                  :verify-guards nil))
  (if (= x 0)
      0
    (if (atom y)
        (* x y)
      (case (car y)
        (pop (norm-pop (cadr y) (mul-int x (caddr y))))
        (pow (norm-pow (cadr y) (mul-int x (caddr y)) (mul-int x (cadddr y))))))))

(defrule shnfp-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (shnfp (mul-int x y)))
  :enable shnfp-new
  :prep-lemmas
  ((defrule lemma
     (implies (and (shnfp x)
                   (shnfp y)
                   (atom x)
                   (atom y))
              (shnfp (* x y)))
     :enable shnfp)))

(verify-guards mul-int
  :hints (("Goal" :in-theory (enable shnfp-guard))))

(local-defthm normp-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x))
           (shf-normp (mul-int x y)))
  :hints (("Goal" :use shnfp-mul-int :in-theory (disable shnfp-mul-int))))

(defrule evalh-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (atom x)
                (all-integers vals))
           (equal (evalh (mul-int x y) vals)
                  (* (evalh x vals) (evalh y vals))))
  :enable (acl2::|arith (* y (* x z))|
                 shnfp-new))

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
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp x)
                              (shnfp y))
                  :verify-guards nil))
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

(in-theory (disable norm-pop norm-pow))

(defthm evalh-norm-mul-int
  (implies (and (shnfp x)
                (shnfp y)
                (or (atom x) (atom y))
                (all-integers vals))
           (equal (evalh (norm-mul x y) vals)
                  (* (evalh x vals) (evalh y vals)))))

(defrule shnfp-norm-mul
  (implies (and (shnfp x)
                (shnfp y))
           (shnfp (norm-mul x y)))
  :enable shnfp-new)

(verify-guards norm-mul
  :hints (("Goal" :in-theory (enable shnfp-guard))))

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

(local (defrule evalh-mul-pop-pop
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (if (= i j)
                      (= (evalh (norm-mul p q) (nthcdr i vals))
                         (* (evalh p (nthcdr i vals))
                            (evalh q (nthcdr i vals))))
                    (if (> i j)
                        (= (evalh (norm-mul (list 'pop (- i j) p) q) (nthcdr j vals))
                           (* (evalh (list 'pop (- i j) p) (nthcdr j vals))
                              (evalh q (nthcdr j vals))))
                      (= (evalh (norm-mul (list 'pop (- j i) q) p) (nthcdr i vals))
                         (* (evalh (list 'pop (- j i) q) (nthcdr i vals))
                            (evalh p (nthcdr i vals)))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :enable shnfp-new
  :disable (expt evalh-pow evalh-pow-rewrite)))

(local (defrule evalh-mul-pop-pow
  (let ((i (cadr x)) (p (caddr x)) (q (caddr y)) (r (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (if (= i 1)
                      (and (= (evalh (norm-mul x q) vals)
                              (* (evalh x vals) (evalh q vals)))
                           (= (evalh (norm-mul p r) (cdr vals))
                              (* (evalh p (cdr vals)) (evalh r (cdr vals)))))
                    (and (= (evalh (norm-mul x q) vals)
                            (* (evalh x vals) (evalh q vals)))
                         (= (evalh (norm-mul (list 'pop (1- i) p) r) (cdr vals))
                            (* (evalh (list 'pop (1- i) p) (cdr vals))
                               (evalh r (cdr vals)))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :enable (shnfp-new acl2::|arith (* y (* x z))|)
  :disable (expt evalh-pow evalh-pow-rewrite)))

(local (defrule evalh-mul-pow-pop
  (let ((i (cadr y)) (p (caddr y)) (q (caddr x)) (r (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (eql (car x) 'pow)
                  (eql (car y) 'pop)
                  (if (= i 1)
                      (and (= (evalh (norm-mul y q) vals)
                              (* (evalh y vals) (evalh q vals)))
                           (= (evalh (norm-mul p r) (cdr vals))
                              (* (evalh p (cdr vals)) (evalh r (cdr vals)))))
                    (and (= (evalh (norm-mul y q) vals)
                            (* (evalh y vals) (evalh q vals)))
                         (= (evalh (norm-mul (list 'pop (1- i) p) r) (cdr vals))
                            (* (evalh (list 'pop (1- i) p) (cdr vals))
                               (evalh r (cdr vals)))))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :enable (shnfp-new acl2::|arith (* y (* x z))|)
  :disable (expt evalh-pow evalh-pow-rewrite)))

(local (defrule evalh-mul-pow-pow
  (let ((p (caddr x)) (q (cadddr x))
        (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers vals)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (= (evalh (norm-mul p r) vals)
                     (* (evalh p vals) (evalh r vals)))
                  (= (evalh (norm-mul q s) (cdr vals))
                     (* (evalh q (cdr vals)) (evalh s (cdr vals))))
                  (= (evalh (norm-mul p (norm-pop 1 s)) vals)
                     (* (evalh p vals) (evalh (norm-pop 1 s) vals)))
                  (= (evalh (norm-mul r (norm-pop 1 q)) vals)
                     (* (evalh r vals) (evalh (norm-pop 1 q) vals))))
             (equal (evalh (norm-mul x y) vals)
                    (* (evalh x vals) (evalh y vals)))))
  :enable (shnfp-new acl2::|arith (* y (* x z))|
                     acl2::|arith (expt x (+ m n))|)
  :disable (expt evalh-pow evalh-pow-rewrite)))

(in-theory (disable shnfp shf-normp norm-mul evalh))

(defrule evalh-norm-mul
  (implies (and (shnfp x)
                (shnfp y)
                (all-integers vals))
           (equal (evalh (norm-mul x y) vals)
                  (* (evalh x vals)
                     (evalh y vals))))
  :induct (norm-mul-induct x y vals)
  :enable shnfp-new
  :disable (evalh-pow-rewrite evalh-pow))

(defun norm-expt (x k)
  (declare (xargs :guard (and (shnfp x)
                              (natp k))
                  :verify-guards nil))
  (if (zp k)
      1
    (norm-mul x (norm-expt x (1- k)))))

(defthm shnfp-norm-expt
  (implies (shnfp x)
           (shnfp (norm-expt x k))))

(verify-guards norm-expt)

(defthm evalh-norm-expt
  (implies (and (shnfp x)
                (natp k)
                (all-integers vals))
           (equal (evalh (norm-expt x k) vals)
                 (expt (evalh x vals) k)))
  :hints (("Goal" :induct (norm-expt x k))))

(defun norm (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (polyp x vars))
                  :verify-guards nil))
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

(verify-guards norm
  :hints (("Goal" :in-theory (enable shnfp-guard))))

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
  :hints (("Goal" :expand ((shnfp z) (shf-normp z))
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
                  :expand ((evalh x (cons k (cdr n))) (shnfp x) (shfp x) (shf-normp x)))))

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
                  :expand ((shf-normp x) (shf-normp (caddr x)) (shnfp x)))))

(local (defrule ew-9
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
  :expand ((shf-normp x) (shf-normp (caddr x)) (shnfp x))
  :enable shnfp-old
  :disable (evalh evalh-pow-rewrite)))

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

(local (defruled ew-12
  (let ((p (caddr x)) (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (all-integers n)
                  (eq (car x) 'pow)
                  (not (= (evalh p (ew p y)) 0)))
             (and (integerp (evalh q (cdr n)))
                  (integerp (evalh y (cdr n))))))
  :enable shnfp-new))

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
                  :in-theory (disable integerp-evalh integerp-evalh-shnfp evalh-pow-rewrite)
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
  :hints (("Goal" :expand ((shf-normp x) (shfp x) (shnfp x)))))

(local (defruled ew-15
  (let ((p (caddr x))
        (q (cadddr x)))
    (implies (and (shnfp x)
                  (shnfp y)
                  (eq (car x) 'pow)
                  (all-integers n))
             (and (integerp (evalh p n))
                  (integerp (evalh q (cdr n)))
                  (integerp (evalh y (cdr n))))))
  :use ew-14
  :expand (shnfp y)
  :enable shnfp-new))

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
                  :in-theory (disable integerp-evalh))))

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
                  :in-theory (disable abs integerp-evalh))))

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

(local (defruled ew-24
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
  :use ew-23
  :enable shnfp-new
  :disable (evalh-pow evalh-pow-rewrite)))

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

(local (defruled ew-26
  (let* ((p (caddr x)))
    (implies (and (shnfp x)
                  (all-integers n)
		  (eq (car x) 'pow))
             (integerp (evalh p n))))
  :enable shnfp-new))

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
  :hints (("Goal" :expand ((shnfp x) (shfp x) (shf-normp x)))))

(local-defthm ew-34
  (implies (and (shnfp x) (eq (car x) 'pop))
           (and (not (zp (cadr x)))
	        (shnfp (caddr x))
		(eq (caaddr x) 'pow)))
  :rule-classes ()
  :hints (("Goal" :expand ((shnfp x) (shfp x) (shf-normp x)))))

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
  :hints (("Goal" :expand ((shnfp y) (shf-normp y))
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
  :hints (("Goal" :expand ((shnfp x) (shf-normp x))
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
  :hints (("Goal" :expand ((shnfp x) (shf-normp x))
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
                  :expand ((:free (x) (shnfp x)) (shf-normp x) (shf-normp y)
                           (:free (i p) (shnfp (list 'pop i p)))
                           (:free (i p) (shf-normp (list 'pop i p)))))))

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
  :hints (("Goal" :expand ((shnfp y) (shf-normp y))
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
  :hints (("Goal" :expand ((shnfp x) (shf-normp x))
                  :use (na0-16 na0-23))))

(local (defrule na0-25
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
  :use (na0-18 na0-21 na0-24)
  :enable shnfp-new))

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
                  :expand ((:free (x) (shnfp x)) (shf-normp x) (shf-normp y)
                           (:free (i p q) (shnfp (list 'pow i p q)))
                           (:free (i p q) (shf-normp (list 'pow i p q)))))))

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

(local (defrule norm-add-0
  (implies (and (shnfp x)
                (shnfp y)
		(equal (norm-add x y) 0))
           (equal (norm-neg x) y))
  :rule-classes ()
  :induct (norm-add x y)
  :expand (norm-add x y)
  :hints (
          ("Subgoal *1/13" :use (na0-27))
          ("Subgoal *1/12" :use (na0-27))
          ("Subgoal *1/11" :use (na0-27))
          ("Subgoal *1/10" :use (na0-16))
          ("Subgoal *1/9" :use (na0-16))
          ("Subgoal *1/5" :use (na0-15))
          ("Subgoal *1/4" :use (na0-15))
          ("Subgoal *1/3" :use (na0-15))
          ("Subgoal *1/2" :use (na0-4 na0-16))
          ("Subgoal *1/1" :use (na0-3)))
  :enable shnfp-new))

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
          ("Subgoal *1/3" :expand ((evalh x n) (evalh x n0) (shnfp x) (shfp x) (shf-normp x)))
          ("Subgoal *1/2" :expand ((evalh x n) (evalh x n0) (shnfp x) (shfp x) (shf-normp x)))))

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

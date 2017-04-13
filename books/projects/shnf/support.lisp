(in-package "RTL")

(include-book "tools/def-functional-instance" :dir :system)

; Use support books to be certifiable by ACL2(r)
(include-book "rtl/rel11/support/basic" :dir :system)
(include-book "rtl/rel11/support/util" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))


;; [Jared] trying to speed up this book
;; [Dima] Remove those rules which are already disabled using with-arith5-help
(local (deftheory jared-disables
         '(default-car
           default-cdr)))

(local (in-theory (disable jared-disables)))


;;*********************************************************************************
;;                              Subring of Complex
;;*********************************************************************************

;; Poly coefficients and variables are in subring recognized by ?p.
;; Functions which depends on ?p have suffix "[?p]".

;; Subring axions:
(encapsulate
  (((?p *) => *))

  (local (defun ?p (x)
           (integerp x)))

  (defrule subring-of-acl2-numbers[?p]
    (implies (?p x)
             (acl2-numberp x)))

  (defrule closure-+[?p]
    (implies (and (?p x)
                  (?p y))
             (?p (+ x y))))

  (defrule closure-*[?p]
    (implies (and (?p x)
                  (?p y))
             (?p (* x y))))

  (defrule closure--1[?p]
    (?p -1)))

(acl2::with-arith5-help
 (defrule closure--[?p]
   (implies (?p x)
            (?p (- x)))
   :use (:instance closure-*[?p] (y -1))))

(defrule integerp-is-subring[?p]
  (implies (integerp x)
           (?p x))
  :induct (expt 1 x)
  :prep-lemmas
  ((defrule subtingp-1
     (?p 1)
     :use (:instance closure--[?p] (x -1)))
   (defrule subtingp-0
     (?p 0)
     :use (:instance closure-+[?p] (x -1) (y 1)))
   (defrule lemma1
     (implies (and (?p (1- x))
                   (integerp x))
              (?p x))
     :use (:instance closure-+[?p] (x (1- x)) (y 1)))
   (defrule lemma2
     (implies (and (?p (1+ x))
                   (integerp x))
              (?p x))
     :use (:instance closure-+[?p] (x (1+ x)) (y -1)))))

(defrule closure-expt[?p]
  (implies (and (?p x)
                (natp i))
           (?p (expt x i))))

(defn list[?p] (vals)
  (if (consp vals)
      (and (list[?p] (cdr vals))
           (?p (car vals)))
    (null vals)))

(defrule true-listp-list[?p]
  (implies (list[?p] vals)
           (true-listp vals)))

(defrule list-cdr[?p]
  (implies (list[?p] n)
           (list[?p] (cdr n))))

(defrule list-nthcdr[?p]
  (implies (list[?p] vals)
           (list[?p] (nthcdr n vals))))

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

(defun polyp[?p] (x vars)
  (declare (xargs :guard (distinct-symbols vars)))
  (if (atom x)
      (or (?p x) (member x vars))
    (and (true-listp x)
         (case (len x)
           (2 (let ((y (cadr x)))
                (case (car x)
                  (- (polyp[?p] y vars)))))
           (3 (let ((y (cadr x)) (z (caddr x)))
                (case (car x)
                  (+ (and (polyp[?p] y vars) (polyp[?p] z vars)))
                  (- (and (polyp[?p] y vars) (polyp[?p] z vars)))
                  (* (and (polyp[?p] y vars) (polyp[?p] z vars)))
                  (expt (and (polyp[?p] y vars) (natp z))))))))))

;; Evaluation of a polynomial term:

(defun evalp[?p] (x alist)
  (if (?p x)
      x
    (if (atom x)
        (cdr (assoc x alist))
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (+ (evalp[?p] y alist) (evalp[?p] z alist)))
          (- (if (cddr x) (- (evalp[?p] y alist) (evalp[?p] z alist)) (- (evalp[?p] y alist))))
          (* (* (evalp[?p] y alist) (evalp[?p] z alist)))
          (expt (expt (evalp[?p] y alist) (evalp[?p] z alist))))))))

(defrule closure-evalp[?p]
  (implies (and (distinct-symbols vars)
                (list[?p] vals)
                (<= (len vars) (len vals))
                (polyp[?p] x vars))
           (?p (evalp[?p] x (pairlis$ vars vals))))
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

(defn shfp[?p] (x)
  (if (atom x)
      (?p x)
    (case (car x)
      (pop (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (shfp[?p] (caddr x))
                (null (cdddr x))))
      (pow (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (shfp[?p] (caddr x))
                (consp (cdddr x)) (shfp[?p] (cadddr x))
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

(local (defrule shf-count-shfp[?p]
  (implies (shfp[?p] x)
           (>= (shf-count x) 1))
  :rule-classes :linear))

(local (defrule shf-cound-pow-q
  (implies (eql (car x) 'pow)
           (<= (shf-count (cadddr x)) (- (shf-count x) 2)))
  :rule-classes :linear))

(local (defrule shf-cound-pow-q-shfp[?p]
  (implies (and (shfp[?p] x)
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

(defun evalh[?p] (x vals)
  (declare (xargs :guard (and (shfp[?p] x)
                              (list[?p] vals))
                  :verify-guards nil))
  (if (atom x)
      x
    (case (car x)
      (pop (evalh[?p] (caddr x) (nthcdr (cadr x) vals)))
      (pow (+ (* (expt (if (consp vals) (car vals) 0) (cadr x))
                 (evalh[?p] (caddr x) vals))
              (evalh[?p] (cadddr x) (cdr vals)))))))

(defrule evalh-num[?p]
  (implies (atom x)
           (equal (evalh[?p] x vals)
                  x)))

;; A SHF x is normal if the following conditions hold:
;;    (1) x = (POP i p) => p is a POW
;;    (2) x = (POW i p q) => p neither 0 nor (POW j r 0)

(defun shf-normp[?p] (x)
  (declare (xargs :guard (shfp[?p] x)))
  (if (atom x)
      t
    (let ((i (cadr x)) (p (caddr x)) (q (cadddr x)))
      (case (car x)
        (pop (and (not (= i 0))
                  (consp p)
                  (eql (car p) 'pow)
                  (shf-normp[?p] p)))
        (pow (and (not (= i 0))
                  (shf-normp[?p] p)
                  (shf-normp[?p] q)
                  (if (atom p)
                      (not (= p 0))
                    (not (and (eql (car p) 'pow)
                              (equal (cadddr p) 0))))))))))

(defn shnfp[?p] (x)
  (and (shfp[?p] x) (shf-normp[?p] x)))

(defrule shnfp-shfp[?p]
  (implies (shnfp[?p] x)
           (shfp[?p] x))
  ;; [Jared] trying to cheapen this very expensive rule.
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(local (defruled shnfp-pop-structure[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pop))
           (and (consp (cdr x))
                (consp (cddr x))))
  :enable shnfp[?p]))

(local (defruled shnfp-pow-structure[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pow))
           (and (consp (cdr x))
                (consp (cddr x))
                (consp (cdddr x))))
  :enable shnfp[?p]))

(local (defruled shnfp-atom[?p]
  (implies (and (shnfp[?p] x)
                (not (consp x)))
           (?p x))))

(local (defruled shnfp-forward[?p]
  (implies (shnfp[?p] x)
           (or (?p x)
               (and (consp x)
                    (or (eql (car x) 'pop)
                        (eql (car x) 'pow)))))
  :rule-classes :forward-chaining))

(local (defruled shnfp-label[?p]
  (implies (and (shnfp[?p] x)
                (consp x))
           (and (implies (not (equal (car x) 'pop))
                         (equal (equal (car x) 'pow) t))
                (implies (not (equal (car x) 'pow))
                         (equal (equal (car x) 'pop) t))))))

(local (defrule shnfp-split[?p]
  (implies (shnfp[?p] p)
           (or (?p p)
               (and (consp p)
                    (or (eql (car p) 'pop)
                        (eql (car p) 'pow)))))
  :rule-classes ()))

(local (defruled shnfp-pow-i-type[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pow))
           (posp (cadr x)))
  :rule-classes :type-prescription
  :expand (shf-normp[?p] x)))

(defrule shnfp-pow-q[?p]
  (implies (and (shnfp[?p] x) (eql (car x) 'pow))
           (shnfp[?p] (cadddr x))))

(defrule shnfp-pow-p[?p]
  (implies (and (shnfp[?p] x) (eql (car x) 'pow))
           (shnfp[?p] (caddr x))))

(local (defruled shnfp-pow-p-ext[?p]
  (implies (and (shnfp[?p] x) (eql (car x) 'pow))
           (and (not (equal (caddr x) 0))
                (not (equal (cadddr (caddr x)) 0))))))

(local (defruled shnfp-pop-i-type[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pop))
           (posp (cadr x)))
  :rule-classes :type-prescription
  :expand (shf-normp[?p] x)))

(local (defruled shnfp-pop-p[?p]
  (implies (and (shnfp[?p] x) (eql (car x) 'pop))
           (and (shnfp[?p] (caddr x))
                (consp (caddr x))
                (equal (car (caddr x)) 'pow)))))

(defrule shfp-pop-pow-atom[?p]
  (implies (and (shfp[?p] x) (not (eql (car x) 'pow)) (not (eql (car x) 'pop)))
           (atom x)))

(defrule shnfp-num[?p]
  (implies (?p x)
           (shnfp[?p] x))
  :disable subring-of-acl2-numbers[?p]
  :use subring-of-acl2-numbers[?p])

(local (defruled shnfp-pop-suff[?p]
  (implies (and (posp i)
                (shnfp[?p] p)
                (eql (car p) 'pow))
           (shnfp[?p] (list 'pop i p)))))

(local (defruled shnfp-pow-suff[?p]
  (implies (and (posp i)
                (shnfp[?p] p)
                (shnfp[?p] q)
                (or (and (atom p) (not (= p 0)))
                    (eql (car p) 'pop)
                    (and (eql (car p) 'pow) (not (= (cadddr p) 0)))))
           (shnfp[?p] (list 'pow i p q)))))

(local (defruled evalh-pop[?p]
  (implies (equal (car x) 'pop)
           (equal (evalh[?p] x vals)
                  (evalh[?p] (caddr x) (nthcdr (cadr x) vals))))))

(local (defruled evalh-pop-2[?p]
  (equal (evalh[?p] (list 'pop i p) vals)
         (evalh[?p] p (nthcdr i vals)))))

(local (defruled evalh-pow-2[?p]
  (implies (and (shnfp[?p] x)
                (equal (car x) 'pow))
           (equal (evalh[?p] (list 'pow i p q) vals)
                  (+ (* (expt (if (consp vals) (car vals) 0) i)
                        (evalh[?p] p vals))
                     (evalh[?p] q (cdr vals)))))))

(defrule closure-evalh[?p]
  (implies (and (shfp[?p] x)
                (list[?p] vals))
           (?p (evalh[?p] x vals))))

(verify-guards evalh[?p])

(local (defruled closure-evalh-shnfp[?p]
  (implies (and (shnfp[?p] x)
                (list[?p] vals))
           (?p (evalh[?p] x vals)))))

;; This theory disables definition but provides full set of lemmas.
;; Forward rule shnfp-forward is intentionally not in the theory.

(local (deftheory shnfp-new[?p]
         '(shnfp-atom[?p]
           shnfp-label[?p]
           shnfp-pow-i-type[?p]
           shnfp-pow-q[?p]
           shnfp-pow-p[?p]
           shnfp-pow-p-ext[?p]
           shnfp-pop-i-type[?p]
           shnfp-pop-p[?p]
           shnfp-num[?p]
           shnfp-pop-suff[?p]
           shnfp-pow-suff[?p]
;           evalh-pop
           evalh-pop-2[?p]
;           evalh-pow
           evalh-pow-2[?p]
           closure-evalh-shnfp[?p])))

(local (deftheory shnfp-guard[?p]
         (union-theories '(shnfp-pop-structure[?p]
                           shnfp-pow-structure[?p])
                         (theory 'shnfp-new[?p]))))

(local (in-theory (disable shnfp[?p] shnfp-pow-p[?p] shnfp-pow-q[?p]
                           shnfp-num[?p] closure-evalh[?p])))


;; We shall define a function norm that computes a SHNF
;; representing a polynomial with respect to a given variable ordering.

;; norm-pop normalizes (POP i p), where p is normal:

(defun norm-pop[?p] (i p)
  (declare (xargs :guard (and (natp i)
                              (shnfp[?p] p))
                  :guard-hints (("goal" :in-theory (enable shnfp-guard[?p])))))
  (if (or (= i 0) (atom p))
      p
    (if (eql (car p) 'pop)
        (list 'pop (+ i (cadr p)) (caddr p))
      (list 'pop i p))))

(defrule norm-pop-shnfp[?p]
  (implies (and (shnfp[?p] p) (natp i))
           (shnfp[?p] (norm-pop[?p] i p)))
  :enable shnfp-new[?p])

(defrule norm-pop-normp[?p]
  (implies (and (shnfp[?p] p) (natp i))
           (shf-normp[?p] (norm-pop[?p] i p)))
  :enable shnfp[?p]
  :use norm-pop-shnfp[?p])

(defrule norm-pop-shfp[?p]
  (implies (and (shnfp[?p] p) (natp i))
           (shfp[?p] (norm-pop[?p] i p)))
  :use norm-pop-shnfp[?p])

(defrule nthcdr+
  (implies (and (natp m) (natp n))
           (equal (nthcdr m (nthcdr n x))
                  (nthcdr (+ m n) x)))
  :induct (nthcdr n x))

(defrule norm-pop-evalh[?p]
  (implies (and (shnfp[?p] p) (natp i))
           (equal (evalh[?p] (norm-pop[?p] i p) n)
                  (evalh[?p] `(pop ,i ,p) n)))
  :enable shnfp-new[?p])

(in-theory (disable norm-pop[?p]))

;; norm-pow normalizes (POW i p q), where p and p are normal:

(defun norm-pow[?p] (i p q)
  (declare (xargs :guard (and (natp i)
                              (shnfp[?p] p)
                              (shnfp[?p] q))
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard[?p])))))
  (if (equal p 0)
      (norm-pop[?p] 1 q)
    (if (and (consp p) (eql (car p) 'pow) (equal (cadddr p) 0))
        (list 'pow (+ i (cadr p)) (caddr p) q)
      (list 'pow i p q))))

(defrule norm-pow-shnfp[?p]
  (implies (and (shnfp[?p] p) (shnfp[?p] q) (not (zp i)))
           (shnfp[?p] (norm-pow[?p] i p q)))
  :enable shnfp-new[?p])

(defrule norm-pow-normp[?p]
  (implies (and (shnfp[?p] p) (shnfp[?p] q) (not (zp i)))
           (shf-normp[?p] (norm-pow[?p] i p q)))
  :use norm-pow-shnfp[?p]
  :enable shnfp[?p])

(defrule norm-pow-shfp[?p]
  (implies (and (shnfp[?p] p) (shnfp[?p] q) (not (zp i)))
           (shfp[?p] (norm-pow[?p] i p q)))
  :use norm-pow-shnfp[?p])

(defrule norm-pow-evalh[?p]
  (implies (and (shnfp[?p] p) (shnfp[?p] q) (not (zp i)) (list[?p] vals))
           (equal (evalh[?p] (norm-pow[?p] i p q) vals)
                  (evalh[?p] `(pow ,i ,p ,q) vals)))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (acl2-numberp x)
                    (natp i)
                    (natp j))
               (equal (* z (expt x (+ i j)))
                      (* (expt x i) z (expt x j)))))))
  :enable shnfp-new[?p])

(in-theory (disable norm-pow[?p]))

;; norm-var handles the case where the polynomial is a simple variable:

(defun var-index (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
  (if (consp vars)
      (if (eql x (car vars))
          0
        (1+ (var-index x (cdr vars))))
    ()))

(defrule natp-var-index
  (implies (member x vars)
           (natp (var-index x vars)))
  :rule-classes (:type-prescription :rewrite))

(defun norm-var[?p] (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))
                  :guard-hints (("goal" :in-theory (e/d (shnfp-guard[?p]) ((shnfp[?p])))))))
  (norm-pop[?p] (var-index x vars) '(pow 1 1 0)))

(defrule shnfp-norm-var[?p]
  (implies (member x vars)
           (shnfp[?p] (norm-var[?p] x vars)))
  :enable shnfp-new[?p])

(defrule car-nthcdr
  (equal (car (nthcdr i l))
         (nth i l)))

(defrule consp-nthcdr
  (implies (and (natp i)
                (< i (len l)))
           (consp (nthcdr i l))))

(defrule member-len-pos
  (implies (= (len l) 0)
           (not (member x l))))

(local (defrule var-index-len
  (implies (member x vars)
           (< (var-index x vars) (len vars)))
  :rule-classes ()))

(defrule nth-list[?p]
  (implies (and (list[?p] vals)
                (natp i)
                (< i (len vals)))
           (?p (nth i vals)))
  :rule-classes (:type-prescription :rewrite))

(defrule evalh-norm-var-rewrite[?p]
  (implies (and (distinct-symbols vars)
                (list[?p] vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (evalh[?p] (norm-var[?p] x vars) vals)
                  (nth (var-index x vars) vals)))
  :use var-index-len
  :enable (shnfp-new[?p] ACL2::|arith (expt x 1)|))

(defrule distinct-symbols-atom
  (implies (and (distinct-symbols vars)
                (member x vars))
           (atom x)))

(defrule evalp-var[?p]
  (implies (and (distinct-symbols vars)
                (member x vars))
           (equal (evalp[?p] x a)
                  (cdr (assoc x a))))
  :prep-lemmas
  ((defrule lemma
     (implies (?p x)
              (not (symbolp x)))
     :use subring-of-acl2-numbers[?p])))

(defrule nth-var-index-vals[?p]
  (implies (and (distinct-symbols vars)
                (list[?p] vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (nth (var-index x vars) vals)
                  (cdr (assoc x (pairlis$ vars vals))))))

(defrule evalh-norm-var[?p]
  (implies (and (distinct-symbols vars)
                (list[?p] vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (evalh[?p] (norm-var[?p] x vars) vals)
                  (evalp[?p] x (pairlis$ vars vals))))
  :disable norm-var[?p])

;; norm-add computes a normal representation of (+ a b),
;; given normal representations x and y of a and b.

(in-theory (disable norm-var[?p]))

;; add-num handles the case where x is an integer:

(defun add-num[?p] (x y)
  (declare (xargs :guard (and (?p x)
                              (shnfp[?p] y))
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard[?p])))))
  (if (atom y)
      (+ x y)
    (case (car y)
      (pow (list 'pow (cadr y) (caddr y) (add-num[?p] x (cadddr y))))
      (pop (list 'pop (cadr y) (add-num[?p] x (caddr y)))))))

(defrule shnfp-add-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (atom x))
           (shnfp[?p] (add-num[?p] x y)))
  :enable (shnfp-new[?p] shnfp-forward[?p])
  :prep-lemmas
  ((defrule lemma
     (implies (shnfp[?p] y)
              (equal (car (add-num[?p] x y)) (car y)))
     :enable shnfp-label[?p])))

(defrule normp-add-num[?p]
  (implies (and (shf-normp[?p] x)
                (shf-normp[?p] y)
                (atom x))
           (shf-normp[?p] (add-num[?p] x y)))
  :hints (("Subgoal *1/5" :expand ((add-num[?p] x (caddr y))))))

(defrule evalh-add-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (atom x))
           (equal (evalh[?p] (add-num[?p] x y) vals)
                  (+ (evalh[?p] x vals) (evalh[?p] y vals))))
  :enable (acl2::|(* 0 x)|
           acl2::|arith (expt 0 n)|
           shnfp-new[?p]))

(in-theory (disable add-num[?p]))

(defmacro add-pop-pop[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (norm-pop[?p] i (norm-add[?p] p q))
       (if (> i j)
           (norm-pop[?p] j (norm-add[?p] (list 'pop (- i j) p) q))
         (norm-pop[?p] i (norm-add[?p] (list 'pop (- j i) q) p))))))

(defmacro add-pop-pow[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (list 'pow j q (norm-add[?p] r p))
       (list 'pow j q (norm-add[?p] r (list 'pop (1- i) p))))))

(defmacro add-pow-pow[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))
     (if (= i j)
         (norm-pow[?p] i (norm-add[?p] p r) (norm-add[?p] q s))
       (if (> i j)
           (norm-pow[?p] j (norm-add[?p] (list 'pow (- i j) p 0) r) (norm-add[?p] q s))
        (norm-pow[?p] i (norm-add[?p] (list 'pow (- j i) r 0) p) (norm-add[?p] s q))))))

(defun norm-add[?p] (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp[?p] x)
                              (shnfp[?p] y))
                  :verify-guards nil))
  (if (atom x)
      (add-num[?p] x y)
    (if (atom y)
        (add-num[?p] y x)
      (case (car x)
        (pop (case (car y)
               (pop (add-pop-pop[?p] x y))
               (pow (add-pop-pow[?p] x y))))
        (pow (case (car y)
               (pop (add-pop-pow[?p] y x))
               (pow (add-pow-pow[?p] x y))))))))

(defrule evalh-norm-add-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (or (atom x) (atom y)))
           (equal (evalh[?p] (norm-add[?p] x y) vals)
                  (+ (evalh[?p] x vals) (evalh[?p] y vals)))))

(defrule shnfp-norm-add[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y))
           (shnfp[?p] (norm-add[?p] x y)))
  :enable shnfp-new[?p])

(verify-guards norm-add[?p]
  :hints (("Goal" :in-theory (enable shnfp-guard[?p]))))

(defrule normp-norm-add[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y))
           (shf-normp[?p] (norm-add[?p] x y)))
  :enable shnfp[?p]
  :disable shnfp-norm-add[?p]
  :use shnfp-norm-add[?p])

(defun norm-add-induct[?p] (x y vals)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (if (or (not (shnfp[?p] x))
          (not (shnfp[?p] y))
          (atom x)
          (atom y)
          (not (member (car x) '(pop pow)))
          (not (member (car y) '(pop pow))))
      (list x y vals)
    (if (and (eql (car x) 'pop) (eql (car y) 'pop))
        (let ((i (cadr x)) (p (caddr x))
              (j (cadr y)) (q (caddr y)))
          (if (= i j)
              (norm-add-induct[?p] p q (nthcdr i vals))
            (if (> i j)
                (norm-add-induct[?p] (list 'pop (- i j) p) q (nthcdr j vals))
              (norm-add-induct[?p] (list 'pop (- j i) q) p (nthcdr i vals)))))
      (if (and (eql (car x) 'pop) (eql (car y) 'pow))
          (let ((i (cadr x)) (p (caddr x)) (r (cadddr y)))
            (if (= i 1)
                (norm-add-induct[?p] r p (cdr vals))
              (norm-add-induct[?p] r (list 'pop (1- i) p) (cdr vals))))
        (if (and (eql (car x) 'pow) (eql (car y) 'pop))
            (let ((i (cadr y)) (p (caddr y)) (r (cadddr x)))
              (if (= i 1)
                  (norm-add-induct[?p] r p (cdr vals))
                (norm-add-induct[?p] r (list 'pop (1- i) p) (cdr vals))))
          (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
                (j (cadr y)) (r (caddr y)) (s (cadddr y)))
            (if (= i j)
                (list (norm-add-induct[?p] p r vals)
                      (norm-add-induct[?p] q s (cdr vals) ))
              (if (> i j)
                  (list (norm-add-induct[?p] (list 'pow (- i j) p 0) r vals)
                        (norm-add-induct[?p] q s (cdr vals)))
                (list (norm-add-induct[?p] (list 'pow (- j i) r 0) p vals)
                      (norm-add-induct[?p] s q (cdr vals)))))))))))

(defn car0 (vals)
  (if (consp vals) (car vals) 0))

(defrule evalh-pow-rewrite[?p]
  (implies (eql (car x) 'pow)
           (equal (evalh[?p] x vals)
                  (+ (* (expt (car0 vals) (cadr x))
                        (evalh[?p] (caddr x) vals))
                     (evalh[?p] (cadddr x) (cdr vals))))))

(in-theory (disable shf-normp[?p] norm-add[?p] evalh[?p]))

(local (defrule evalh-add-pop-pop[?p]
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (if (= i j)
                      (equal (evalh[?p] (norm-add[?p] p q) (nthcdr i vals))
                             (+ (evalh[?p] p (nthcdr i vals))
                                (evalh[?p] q (nthcdr i vals))))
                    (if (> i j)
                        (equal (evalh[?p] (norm-add[?p] (list 'pop (- i j) p) q) (nthcdr j vals))
                               (+ (evalh[?p] (list 'pop (- i j) p) (nthcdr j vals))
                                  (evalh[?p] q (nthcdr j vals))))
                      (equal (evalh[?p] (norm-add[?p] (list 'pop (- j i) q) p) (nthcdr i vals))
                             (+ (evalh[?p] (list 'pop (- j i) q) (nthcdr i vals))
                                (evalh[?p] p (nthcdr i vals)))))))
             (equal (evalh[?p] (norm-add[?p] x y) vals)
                    (+ (evalh[?p] x vals) (evalh[?p] y vals)))))
  :expand ((norm-add[?p] x y) (evalh[?p] x vals) (evalh[?p] y vals))
  :enable shnfp-new[?p]
  :disable evalh-pow-rewrite[?p]))

(local (defrule evalh-add-pop-pow[?p]
  (let ((i (cadr x)) (p (caddr x))
        (r (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (if (= i 1)
                      (equal (evalh[?p] (norm-add[?p] r p) (cdr vals))
                             (+ (evalh[?p] r (cdr vals))
                                (evalh[?p] p (cdr vals))))
                    (equal (evalh[?p] (norm-add[?p] r (list 'pop (1- i) p)) (cdr vals))
                           (+ (evalh[?p] r (cdr vals))
                              (evalh[?p] (list 'pop (1- i) p) (cdr vals))))))
             (equal (evalh[?p] (norm-add[?p] x y) vals)
                    (+ (evalh[?p] x vals) (evalh[?p] y vals)))))
  :expand ((norm-add[?p] x y) (evalh[?p] x vals))
  :enable shnfp-new[?p]
  :disable expt))

(local (defrule evalh-add-pow-pop[?p]
  (let ((i (cadr y)) (p (caddr y))
        (r (cadddr x)))
    (implies
     (and (shnfp[?p] x)
          (shnfp[?p] y)
          (eql (car x) 'pow)
          (eql (car y) 'pop)
          (if (= i 1)
              (equal (evalh[?p] (norm-add[?p] r p) (cdr vals))
                     (+ (evalh[?p] r (cdr vals))
                        (evalh[?p] p (cdr vals))))
            (equal (evalh[?p] (norm-add[?p] r (list 'pop (1- i) p)) (cdr vals))
                   (+ (evalh[?p] r (cdr vals))
                      (evalh[?p] (list 'pop (1- i) p) (cdr vals))))))
     (equal (evalh[?p] (norm-add[?p] x y) vals)
            (+ (evalh[?p] x vals) (evalh[?p] y vals)))))
  :expand ((norm-add[?p] x y) (evalh[?p] y vals))
  :enable shnfp-new[?p]
  :disable expt))

(local (defrule evalh-add-pow-pow[?p]
  (let ((i (cadr x)) (p (caddr x)) (q (cadddr x))
        (j (cadr y)) (r (caddr y)) (s (cadddr y)))
    (implies
     (and (shnfp[?p] x)
          (shnfp[?p] y)
          (list[?p] vals)
          (eql (car x) 'pow)
          (eql (car y) 'pow)
          (if (= i j)
              (and (equal (evalh[?p] (norm-add[?p] p r) vals)
                          (+ (evalh[?p] p vals)
                             (evalh[?p] r vals)))
                   (equal (evalh[?p] (norm-add[?p] q s) (cdr vals))
                          (+ (evalh[?p] q (cdr vals))
                             (evalh[?p] s (cdr vals)))))
            (if (> i j)
                (and (equal (evalh[?p] (norm-add[?p] (list 'pow (- i j) p 0) r) vals)
                            (+ (evalh[?p] (list 'pow (- i j) p 0) vals)
                               (evalh[?p] r vals)))
                     (equal (evalh[?p] (norm-add[?p] q s) (cdr vals))
                            (+ (evalh[?p] q (cdr vals))
                               (evalh[?p] s (cdr vals)))))
              (and (equal (evalh[?p] (norm-add[?p] (list 'pow (- j i) r 0) p) vals)
                          (+ (evalh[?p] (list 'pow (- j i) r 0) vals)
                             (evalh[?p] p vals)))
                   (equal (evalh[?p] (norm-add[?p] s q) (cdr vals))
                          (+ (evalh[?p] s (cdr vals))
                             (evalh[?p] q (cdr vals))))))))
     (equal (evalh[?p] (norm-add[?p] x y) vals)
            (+ (evalh[?p] x vals) (evalh[?p] y vals)))))
  :expand (norm-add[?p] x y)
  :cases ((= (cadr x) (cadr y))
          (> (cadr x) (cadr y))
          (< (cadr x) (cadr y)))
  :hints (("subgoal 2" :use (:instance lemma
                                       (i (cadr x))
                                       (j (cadr y))
                                       (p (evalh[?p] (caddr x) vals))
                                       (r (evalh[?p] (caddr y) vals))))
          ("subgoal 1" :use (:instance lemma
                                       (i (cadr y))
                                       (j (cadr x))
                                       (p (evalh[?p] (caddr y) vals))
                                       (r (evalh[?p] (caddr x) vals)))))
  :enable shnfp-new[?p]
  :disable list[?p]
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (let ((x (car0 vals)))
        (implies (and (list[?p] vals)
                      (posp i)
                      (posp j))
                 (equal (* (expt x j) (+ (* (expt x (- i j)) p) r))
                        (+ (* (expt x i) p)
                           (* (expt x j) r))))))))))

(defrule evalh-norm-add[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (list[?p] vals))
           (equal (evalh[?p] (norm-add[?p] x y) vals)
                  (+ (evalh[?p] x vals)
                     (evalh[?p] y vals))))
  :induct (norm-add-induct[?p] x y vals)
  :enable (shnfp-new[?p] shnfp-forward[?p])
  :disable (evalh-pow-rewrite[?p]
;           rules below may be disabled optionally
            expt
            evalh-pop[?p]
            evalh-pop-2[?p]
            evalh-pow-2[?p]
            shnfp-atom[?p])
  :prep-lemmas
  ((defrule lemma
     (implies (and (shnfp[?p] x)
                   (consp x))
              (posp (cadr x)))
     :enable (shnfp[?p] shfp[?p] shf-normp[?p])
     :expand (shf-normp[?p] x)
    :rule-classes (:type-prescription))))

(in-theory (enable shf-normp[?p] evalh[?p]))

;; The remaining cases are handled by norm-neg, norm-mul, and norm-expt:

(defun norm-neg[?p] (x)
  (declare (xargs :guard (shnfp[?p] x)
                  :guard-hints (("Goal" :in-theory (enable shnfp-guard[?p])))))
  (if (atom x)
      (- x)
    (case (car x)
      (pop (list 'pop (cadr x) (norm-neg[?p] (caddr x))))
      (pow (list 'pow (cadr x) (norm-neg[?p] (caddr x)) (norm-neg[?p] (cadddr x)))))))

(local (defrule norm-neg-0[?p]
  (implies (and (shnfp[?p] x) (not (equal x 0)))
           (not (equal (norm-neg[?p] x) 0)))
  :enable (shnfp-new[?p] shnfp-forward[?p])))

(local (defrule car-norm-neg[?p]
  (implies (shnfp[?p] x)
           (equal (car (norm-neg[?p] x))
                  (car x)))
  :enable shnfp-new[?p]))

(local (defrule shnfp-norm-neg-atom[?p]
  (implies (and (shnfp[?p] x)
                (not (consp x))
                (shnfp[?p] x))
           (shnfp[?p] (- x)))
  :enable (shnfp[?p] shf-normp[?p])))

(local (defrule shnfp-norm-neg-pow[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pow)
                (shnfp[?p] (norm-neg[?p] (caddr x)))
                (shnfp[?p] (norm-neg[?p] (cadddr x))))
           (shnfp[?p] (list 'pow (cadr x) (norm-neg[?p] (caddr x)) (norm-neg[?p] (cadddr x)))))
  :enable shnfp-new[?p]
  :use (:instance shnfp-pow-suff[?p]
                  (i (cadr x))
                  (p (norm-neg[?p] (caddr x)))
                  (q (norm-neg[?p] (cadddr x))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (shnfp[?p] x)
                   (eql (car x) 'pow)
                   (not (equal (cadddr x) 0)))
              (not (equal (cadddr (norm-neg[?p] x)) 0)))
     :enable shnfp-new[?p]))))

(defrule shnfp-norm-neg[?p]
  (implies (shnfp[?p] x)
           (shnfp[?p] (norm-neg[?p] x)))
  :enable shnfp-new[?p])

(defrule evalh-norm-neg[?p]
  (implies (and (shnfp[?p] x)
                (list[?p] vals))
           (equal (evalh[?p] (norm-neg[?p] x) vals)
                  (- (evalh[?p] x vals))))
  :induct (evalh[?p] x vals)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (equal (evalh[?p] (norm-neg[?p] x) vals)
                      (- (evalh[?p] x vals)))
               (equal (* y (evalh[?p] (norm-neg[?p] x) vals))
                      (- (* (evalh[?p] x vals) y))))
      :disable (evalh[?p] norm-neg[?p]))))
  :enable (shnfp-new[?p] evalh[?p])
  :disable list[?p])

(defun mul-num[?p] (x y)
  (declare (xargs :guard (and (?p x)
                              (shnfp[?p] y))
                  :verify-guards nil))
  (if (= x 0)
      0
    (if (atom y)
        (* x y)
      (case (car y)
        (pop (norm-pop[?p] (cadr y) (mul-num[?p] x (caddr y))))
        (pow (norm-pow[?p] (cadr y) (mul-num[?p] x (caddr y)) (mul-num[?p] x (cadddr y))))))))

(defrule shnfp-mul-num-alt[?p]
  (implies (and (?p x)
                (shnfp[?p] y))
           (shnfp[?p] (mul-num[?p] x y)))
  :enable shnfp-new[?p])

(defrule shnfp-mul-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (atom x))
           (shnfp[?p] (mul-num[?p] x y)))
  :enable shnfp-atom[?p])

(verify-guards mul-num[?p]
  :hints (("Goal" :in-theory (enable shnfp-guard[?p]))))

(local (defrule normp-mul-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (atom x))
           (shf-normp[?p] (mul-num[?p] x y)))
  :enable shnfp[?p]))

(defrule evalh-mul-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (atom x)
                (list[?p] vals))
           (equal (evalh[?p] (mul-num[?p] x y) vals)
                  (* (evalh[?p] x vals) (evalh[?p] y vals))))
  :enable (acl2::|arith (* y (* x z))|
                 shnfp-new[?p]))

(in-theory (disable mul-num[?p]))

(defmacro mul-pop-pop[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (norm-pop[?p] i (norm-mul[?p] p q))
       (if (> i j)
           (norm-pop[?p] j (norm-mul[?p] (list 'pop (- i j) p) q))
         (norm-pop[?p] i (norm-mul[?p] (list 'pop (- j i) q) p))))))

(defmacro mul-pop-pow[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (norm-pow[?p] j (norm-mul[?p] ,x q) (norm-mul[?p] p r))
       (norm-pow[?p] j (norm-mul[?p] ,x q) (norm-mul[?p] (list 'pop (1- i) p) r)))))

(defmacro mul-pow-pow[?p] (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))   ;x = p * z^i + q
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))  ;y = r * z^j + s
     (norm-add[?p]
      (norm-add[?p] (norm-pow[?p] (+ i j) (norm-mul[?p] p r) (norm-mul[?p] q s))  ;p * r * z^(i+j) + q * s
                    (norm-pow[?p] i (norm-mul[?p] p (norm-pop[?p] 1 s)) 0))       ;p * s * z^i
      (norm-pow[?p] j (norm-mul[?p] r (norm-pop[?p] 1 q)) 0))))                   ;r * q * z^j

(in-theory (enable norm-pop[?p] norm-pow[?p]))

(defun norm-mul[?p] (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (shnfp[?p] x)
                              (shnfp[?p] y))
                  :verify-guards nil))
  (if (atom x)
      (mul-num[?p] x y)
    (if (atom y)
        (mul-num[?p] y x)
      (case (car x)
        (pop (case (car y)
               (pop (mul-pop-pop[?p] x y))
               (pow (mul-pop-pow[?p] x y))))
        (pow (case (car y)
               (pop (mul-pop-pow[?p] y x))
               (pow (mul-pow-pow[?p] x y))))))))

(in-theory (disable norm-pop[?p] norm-pow[?p]))

(defrule evalh-norm-mul-num[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (or (atom x) (atom y))
                (list[?p] vals))
           (equal (evalh[?p] (norm-mul[?p] x y) vals)
                  (* (evalh[?p] x vals) (evalh[?p] y vals)))))

(defrule shnfp-norm-mul[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y))
           (shnfp[?p] (norm-mul[?p] x y)))
  :enable shnfp-new[?p])

(verify-guards norm-mul[?p]
  :hints (("Goal" :in-theory (e/d (shnfp-guard[?p]) ((shnfp[?p]))))))

(in-theory (enable norm-pop[?p] norm-pow[?p]))

(defun norm-mul-induct[?p] (x y vals)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))))
  (if (or (not (shnfp[?p] x))
          (not (shnfp[?p] y))
          (atom x)
          (atom y)
          (not (member (car x) '(pop pow)))
          (not (member (car y) '(pop pow)))
          (not (list[?p] vals)))
      (list x y vals)
    (if (and (eql (car x) 'pop) (eql (car y) 'pop))
        (let ((i (cadr x)) (p (caddr x))
              (j (cadr y)) (q (caddr y)))
          (if (= i j)
              (norm-mul-induct[?p] p q (nthcdr i vals))
            (if (> i j)
                (norm-mul-induct[?p] (list 'pop (- i j) p) q (nthcdr j vals))
              (norm-mul-induct[?p] (list 'pop (- j i) q) p (nthcdr i vals)))))
      (if (and (eql (car x) 'pop) (eql (car y) 'pow))
          (let ((i (cadr x)) (p (caddr x)) (q (caddr y)) (r (cadddr y)))
            (if (= i 1)
                (list (norm-mul-induct[?p] x q vals)
                      (norm-mul-induct[?p] p r (cdr vals)))
              (list (norm-mul-induct[?p] x q vals)
                    (norm-mul-induct[?p] (list 'pop (1- i) p) r (cdr vals)))))
        (if (and (eql (car x) 'pow) (eql (car y) 'pop))
            (let ((i (cadr y)) (p (caddr y)) (q (caddr x)) (r (cadddr x)))
              (if (= i 1)
                  (list (norm-mul-induct[?p] y q vals)
                        (norm-mul-induct[?p] p r (cdr vals)))
                (list (norm-mul-induct[?p] y q vals)
                      (norm-mul-induct[?p] (list 'pop (1- i) p) r (cdr vals)))))
          (let ((p (caddr x)) (q (cadddr x))
                (r (caddr y)) (s (cadddr y)))
            (list (norm-mul-induct[?p] p r vals)
                  (norm-mul-induct[?p] q s (cdr vals))
                  (norm-mul-induct[?p] p (norm-pop[?p] 1 s) vals)
                  (norm-mul-induct[?p] r (norm-pop[?p] 1 q) vals))))))))

(in-theory (disable norm-pop[?p] norm-pow[?p]))

(local (defrule evalh-mul-pop-pop[?p]
  (let ((i (cadr x)) (p (caddr x))
        (j (cadr y)) (q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (list[?p] vals)
                  (eql (car x) 'pop)
                  (eql (car y) 'pop)
                  (if (= i j)
                      (= (evalh[?p] (norm-mul[?p] p q) (nthcdr i vals))
                         (* (evalh[?p] p (nthcdr i vals))
                            (evalh[?p] q (nthcdr i vals))))
                    (if (> i j)
                        (= (evalh[?p] (norm-mul[?p] (list 'pop (- i j) p) q) (nthcdr j vals))
                           (* (evalh[?p] (list 'pop (- i j) p) (nthcdr j vals))
                              (evalh[?p] q (nthcdr j vals))))
                      (= (evalh[?p] (norm-mul[?p] (list 'pop (- j i) q) p) (nthcdr i vals))
                         (* (evalh[?p] (list 'pop (- j i) q) (nthcdr i vals))
                            (evalh[?p] p (nthcdr i vals)))))))
             (equal (evalh[?p] (norm-mul[?p] x y) vals)
                    (* (evalh[?p] x vals) (evalh[?p] y vals)))))
  :enable shnfp-new[?p]
  :disable (expt evalh-pow-rewrite[?p])))

(local (defrule evalh-mul-pop-pow[?p]
  (let ((i (cadr x)) (p (caddr x)) (q (caddr y)) (r (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (list[?p] vals)
                  (eql (car x) 'pop)
                  (eql (car y) 'pow)
                  (if (= i 1)
                      (and (= (evalh[?p] (norm-mul[?p] x q) vals)
                              (* (evalh[?p] x vals) (evalh[?p] q vals)))
                           (= (evalh[?p] (norm-mul[?p] p r) (cdr vals))
                              (* (evalh[?p] p (cdr vals)) (evalh[?p] r (cdr vals)))))
                    (and (= (evalh[?p] (norm-mul[?p] x q) vals)
                            (* (evalh[?p] x vals) (evalh[?p] q vals)))
                         (= (evalh[?p] (norm-mul[?p] (list 'pop (1- i) p) r) (cdr vals))
                            (* (evalh[?p] (list 'pop (1- i) p) (cdr vals))
                               (evalh[?p] r (cdr vals)))))))
             (equal (evalh[?p] (norm-mul[?p] x y) vals)
                    (* (evalh[?p] x vals) (evalh[?p] y vals)))))
  :enable (shnfp-new[?p] acl2::|arith (* y (* x z))|)
  :disable (expt evalh-pow-rewrite[?p] list[?p])))

(local (defrule evalh-mul-pow-pop[?p]
  (let ((i (cadr y)) (p (caddr y)) (q (caddr x)) (r (cadddr x)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (list[?p] vals)
                  (eql (car x) 'pow)
                  (eql (car y) 'pop)
                  (if (= i 1)
                      (and (= (evalh[?p] (norm-mul[?p] y q) vals)
                              (* (evalh[?p] y vals) (evalh[?p] q vals)))
                           (= (evalh[?p] (norm-mul[?p] p r) (cdr vals))
                              (* (evalh[?p] p (cdr vals)) (evalh[?p] r (cdr vals)))))
                    (and (= (evalh[?p] (norm-mul[?p] y q) vals)
                            (* (evalh[?p] y vals) (evalh[?p] q vals)))
                         (= (evalh[?p] (norm-mul[?p] (list 'pop (1- i) p) r) (cdr vals))
                            (* (evalh[?p] (list 'pop (1- i) p) (cdr vals))
                               (evalh[?p] r (cdr vals)))))))
             (equal (evalh[?p] (norm-mul[?p] x y) vals)
                    (* (evalh[?p] x vals) (evalh[?p] y vals)))))
  :enable (shnfp-new[?p] acl2::|arith (* y (* x z))|)
  :disable (expt evalh-pow-rewrite[?p] list[?p])))

(local (defrule evalh-mul-pow-pow[?p]
  (let ((p (caddr x)) (q (cadddr x))
        (r (caddr y)) (s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (list[?p] vals)
                  (eql (car x) 'pow)
                  (eql (car y) 'pow)
                  (= (evalh[?p] (norm-mul[?p] p r) vals)
                     (* (evalh[?p] p vals) (evalh[?p] r vals)))
                  (= (evalh[?p] (norm-mul[?p] q s) (cdr vals))
                     (* (evalh[?p] q (cdr vals)) (evalh[?p] s (cdr vals))))
                  (= (evalh[?p] (norm-mul[?p] p (norm-pop[?p] 1 s)) vals)
                     (* (evalh[?p] p vals) (evalh[?p] (norm-pop[?p] 1 s) vals)))
                  (= (evalh[?p] (norm-mul[?p] r (norm-pop[?p] 1 q)) vals)
                     (* (evalh[?p] r vals) (evalh[?p] (norm-pop[?p] 1 q) vals))))
             (equal (evalh[?p] (norm-mul[?p] x y) vals)
                    (* (evalh[?p] x vals) (evalh[?p] y vals)))))
  :enable (shnfp-new[?p] acl2::|arith (* y (* x z))|
                         acl2::|arith (expt x (+ m n))|)
  :disable (expt evalh-pow-rewrite[?p] list[?p])))

(in-theory (disable shnfp[?p] shf-normp[?p] norm-mul[?p] evalh[?p]))

(defrule evalh-norm-mul[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
                (list[?p] vals))
           (equal (evalh[?p] (norm-mul[?p] x y) vals)
                  (* (evalh[?p] x vals)
                     (evalh[?p] y vals))))
  :induct (norm-mul-induct[?p] x y vals)
  :enable shnfp-new[?p]
  :disable evalh-pow-rewrite[?p])

(defun norm-expt[?p] (x k)
  (declare (xargs :guard (and (shnfp[?p] x)
                              (natp k))
                  :verify-guards nil))
  (if (zp k)
      1
    (norm-mul[?p] x (norm-expt[?p] x (1- k)))))

(defrule shnfp-norm-expt[?p]
  (implies (shnfp[?p] x)
           (shnfp[?p] (norm-expt[?p] x k)))
  :enable shnfp-new[?p])

(verify-guards norm-expt[?p])

(defrule evalh-norm-expt[?p]
  (implies (and (shnfp[?p] x)
                (natp k)
                (list[?p] vals))
           (equal (evalh[?p] (norm-expt[?p] x k) vals)
                 (expt (evalh[?p] x vals) k)))
  :induct (norm-expt[?p] x k))

(defun norm[?p] (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (polyp[?p] x vars))
                  :verify-guards nil))
  (if (?p x)
      x
    (if (atom x)
        (norm-var[?p] x vars)
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (norm-add[?p] (norm[?p] y vars) (norm[?p] z vars)))
          (- (if (cddr x)
                 (norm-add[?p] (norm[?p] y vars) (norm-neg[?p] (norm[?p] z vars)))
               (norm-neg[?p] (norm[?p] y vars))))
          (* (norm-mul[?p] (norm[?p] y vars) (norm[?p] z vars)))
          (expt (norm-expt[?p] (norm[?p] y vars) (norm[?p] z vars))))))))

(defrule shnfp-norm[?p]
  (implies (and (distinct-symbols vars)
                (polyp[?p] x vars))
           (shnfp[?p] (norm[?p] x vars)))
  :enable shnfp-num[?p])

(verify-guards norm[?p]
  :hints (("Goal" :in-theory (enable shnfp-guard[?p]))))

(defrule evalh-norm[?p]
  (implies (and (distinct-symbols vars)
                (list[?p] vals)
                (<= (len vars) (len vals))
                (polyp[?p] x vars))
           (and (shnfp[?p] (norm[?p] x vars))
                (equal (evalh[?p] (norm[?p] x vars) vals)
                       (evalp[?p] x (pairlis$ vars vals)))))
  :disable norm-neg[?p]
  :prep-lemmas
  ((defrule lemma
     (implies (?p x)
              (not (consp x)))
     :use subring-of-acl2-numbers[?p]
     :enable shnfp-new[?p])))

;;*********************************************************************************
;;                                   Completeness
;;*********************************************************************************

(defun pad0 (i n)
  (declare (xargs :guard (natp i)))
  (if (zp i)
      n
    (cons 0 (pad0 (1- i) n))))

(local (defrule abs-type
  (implies (real/rationalp x)
           (and (real/rationalp (abs x))
                (>= (abs x) 0)))
  :rule-classes :type-prescription))

; Consider complex number as two-dimensional vector.
; This is 1-norm of this vector.
(local (defun 1-norm (x)
  (declare (xargs :guard (acl2-numberp x)))
  (+ (abs (realpart x)) (abs (imagpart x)))))

(local (defrule positive-1-norm
  (implies (and (not (= x 0))
                (acl2-numberp x))
           (and (real/rationalp (1-norm x))
                (> (1-norm x) 0)))
  :rule-classes :type-prescription))

(local (defrule 1-norm-add
  (<= (1-norm (+ x y)) (+ (1-norm x) (1-norm y)))
  :rule-classes :linear))

(local
 (acl2::with-arith5-help
  (defrule 1-norm-scale
    (implies (real/rationalp a)
             (and (equal (1-norm (* a x))
                         (* (abs a) (1-norm x)))
                  (equal (1-norm (* x a))
                         (* (abs a) (1-norm x)))))
    :prep-lemmas
    ((acl2::with-arith5-help
      (defrule lemma
        (implies (real/rationalp a)
                 (and (equal (realpart (* a x)) (* a (realpart x)))
                      (equal (imagpart (* a x)) (* a (imagpart x)))))
        :use ((:instance complex-definition
                         (x (realpart x))
                        (y (imagpart x)))
              (:instance complex-definition
                         (x (* a (realpart x)))
                         (y (* a (imagpart x)))))))))))

(local (in-theory (disable 1-norm)))

; Invariant of evalh-witness:
; Let (list n0 n1 n2 ...) is (evalh-witness x) and x is not atom.
; Then (1-norm (evalh x (list v n1 n2 ...))) >= 1 for all rational v >= n0
(defun evalh-witness[?p] (x)
  (declare (xargs :guard (shnfp[?p] x)
                  :verify-guards nil))
  (if (atom x)
      ()
    (case (car x)
      (pop (let ((i (cadr x))
                 (p (caddr x)))
             (pad0 i (evalh-witness[?p] p))))
      (pow (let* ((p (caddr x))
                  (q (cadddr x))
                  (n (evalh-witness[?p] p))
                  (vq (evalh[?p] q (cdr n)))
                  (normq (+ (abs (realpart vq)) (abs (imagpart vq)))))
             (if (atom p)
                 (let ((normp (+ (abs (realpart p)) (abs (imagpart p)))))
                   (list (max 1 (cg (/ (1+ normq) normp)))))
               (cons (max (car n) (1+ (cg normq))) (cdr n))))))))

(defn all-integers (vals)
  (if (consp vals)
      (and (all-integers (cdr vals))
           (integerp (car vals)))
    (null vals)))

(defrule all-integers-evalh-witness[?p]
  (all-integers (evalh-witness[?p] x)))

(defrule list-all-integers[?p]
  (implies (all-integers n)
           (list[?p] n)))

(defrule real/rationalp-car-all-integers
  (implies (and (all-integers n)
                (consp n))
           (real/rationalp (car n))))

(defrule consp-evalh-witness[?p]
  (implies (and (shnfp[?p] x)
                (consp x))
           (consp (evalh-witness[?p] x)))
  :enable shnfp-new[?p])

(verify-guards evalh-witness[?p]
  :hints (("goal" :in-theory (e/d (shnfp-guard[?p] 1-norm) (abs))
           :use (:instance positive-1-norm (x (caddr x))))))

(local (defun evalh-witness-induct[?p] (x v)
  (if (and (shnfp[?p] x)
           (consp x))
      (case (car x)
        (pop (evalh-witness-induct[?p] (caddr x) (car (evalh-witness[?p] (caddr x)))))
        (pow (evalh-witness-induct[?p] (caddr x) v)))
    (list x v))))

(defrule evalh-witness-pop[?p]
  (implies (and (shnfp[?p] x)
                (eql (car x) 'pop))
           (equal (evalh[?p] x (cons v (cdr (evalh-witness[?p] x))))
                  (evalh[?p] (caddr x) (evalh-witness[?p] (caddr x)))))
  :enable (shnfp-new[?p] evalh-pop[?p])
  :disable evalh-pow-rewrite[?p]
  :prep-lemmas
  ((defrule lemma1
     (implies (posp i)
              (equal (nthcdr i (cons v (cdr n)))
                     (nthcdr i n))))
   (defrule lemma2
     (implies (natp i)
              (equal (nthcdr i (pad0 i n)) n)))))

(local (defrule evalh-witness-pow[?p]
  (let ((p (caddr x))
        (n (evalh-witness[?p] x)))
    (implies (and (shnfp[?p] x)
                  (eql (car x) 'pow)
                  (real/rationalp v)
                  (>= v (car n))
                  (or (not (consp p))
                      (>= (1-norm (evalh[?p] p (cons v (cdr (evalh-witness[?p] p))))) 1)))
             (>= (1-norm (evalh[?p] x (cons v (cdr n)))) 1)))
  :enable shnfp-new[?p]
  :disable (abs 1-norm-scale)
  :prep-lemmas
  ((defrule arith-1
     (implies (and (acl2-numberp p)
                   (not (= p 0)))
              (not (equal (/ (1-norm p)) 0))))
  (acl2::with-arith5-help
   (defruled arith-2
     (implies (and (real/rationalp v)
                   (>= v 1)
                   (posp i))
              (>= (expt v i) v))
     :rule-classes :linear))
   (acl2::with-arith5-nonlinear++-help
    (defrule arith-3
      (implies (and (real/rationalp np)
                    (>= np npbnd)
                    (real/rationalp npbnd)
                    (> npbnd 0)
                    (real/rationalp nq)
                    (>= nq 0)
                    (real/rationalp nx)
                    (>= nx 0)
                    (real/rationalp v)
                    (>= v (/ (1+ nq) npbnd))
                    (>= v 1)
                    (posp i)
                    (>= (+ nx nq) (* (expt v i) np)))
               (>= nx 1))
     :use arith-2
     :disable expt))
   (defruled arith-4
     (equal (+ q (* -1 q) x) (fix x)))
   (defrule inequality-1
     (implies (and (posp i)
                   (>= (1-norm p) np)
                   (real/rationalp np)
                   (> np 0)
                   (real/rationalp v)
                   (>= v 1)
                   (>= v (/ (1+ (1-norm q)) np)))
              (>= (1-norm (+ q (* (expt v i) p))) 1))
     :enable arith-4
     :disable expt
     :use ((:instance 1-norm-add (x (* -1 q)) (y (+ q (* p (expt v i)))))
           (:instance arith-3
                      (np (1-norm p))
                      (npbnd np)
                      (nq (1-norm q))
                      (nx (1-norm (+ q (* (expt v i) p)))))))
   (defrule inequality-2
     (implies (and (posp i)
                   (real/rationalp v)
                   (acl2-numberp p)
                   (not (= p 0))
                   (>= v 1)
                   (>= v (/ (1+ (1-norm q)) (1-norm p))))
              (>= (1-norm (+ q (* p (expt v i)))) 1))
     :use (:instance inequality-1 (np (1-norm p)))
     :disable expt)
   (defrule 1-norm-recognizer
     (equal (+ (abs (imagpart x)) (abs (realpart x))) (1-norm x))
     :enable 1-norm
     :disable abs))))

(local (defrule evalh-witness-lemma[?p]
  (let ((n (evalh-witness[?p] x)))
    (implies (and (shnfp[?p] x)
                  (consp x)
                  (real/rationalp v)
                  (>= v (car n)))
             (>= (1-norm (evalh[?p] x (cons v (cdr n)))) 1)))
  :rule-classes :linear
  :enable shnfp-new[?p]
  :induct (evalh-witness-induct[?p] x v)
  :disable (1-norm abs car0 max evalh-pow-rewrite[?p] evalh-witness[?p])
  :prep-lemmas
  ((defrule lemma1
     (implies (and (shnfp[?p] x)
                   (equal (car x) 'pow)
                   (consp (caddr x)))
              (>= (car (evalh-witness[?p] x))
                  (car (evalh-witness[?p] (caddr x)))))
     :rule-classes :linear)
   (defrule lemma2
     (implies (and (shnfp[?p] x)
                   (eql (car x) 'pow))
              (>= (car (evalh-witness[?p] x)) (car (evalh-witness[?p] (caddr x)))))
     :rule-classes :linear))))

(defruled evalh-not-zero[?p]
  (implies (and (shnfp[?p] x)
                (not (= x 0)))
	   (let ((n (evalh-witness[?p] x)))
	     (and (list[?p] n)
                  (not (equal (evalh[?p] x n) 0)))))
  :cases ((consp x))
  :use (:instance evalh-witness-lemma[?p]
                  (v (car (evalh-witness[?p] x)))))

(local (defrule na0-1[?p]
  (implies (equal (norm-pop[?p] i p) 0)
           (equal p 0))
  :rule-classes ()
  :expand ((norm-pop[?p] i p))))

(local (defrule na0-2[?p]
  (implies (equal (norm-pow[?p] i p q) 0)
           (and (equal p 0) (equal q 0)))
  :rule-classes ()
  :expand (:free (p q) (norm-pow[?p] i p q))
  :use (:instance na0-1[?p] (i 1) (p q))))

(local (defrule na0-3[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
		(or (atom x) (atom y))
		(equal (norm-add[?p] x y) 0))
           (equal y (norm-neg[?p] x)))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shfp[?p] y) (add-num[?p] x y) (add-num[?p] y x) (norm-add[?p] x y))))

(defruled norm-neg-norm-neg[?p]
  (implies (shfp[?p] x)
           (equal (norm-neg[?p] (norm-neg[?p] x)) x))
  :expand (shfp[?p] x))

(local (defruled na0-4[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
		(eq (car x) 'pop)
		(equal (norm-add[?p] x y) 0))
           (equal (car y) 'pop))
  :expand ((add-num[?p] x y) (add-num[?p] y x) (shnfp[?p] y) (shfp[?p] y) (norm-add[?p] x y))))

(local (defrule na0-5[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (= i j))
	     (equal (norm-add[?p] p q) 0)))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-4[?p] (:instance na0-1[?p] (i (cadr x)) (p (norm-add[?p] (caddr x) (caddr y)))))))

(local (defrule na0-6[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (= i j)
		  (implies (equal (norm-add[?p] p q) 0)
		           (equal q (norm-neg[?p] p))))
	     (equal (norm-neg[?p] x) y)))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shfp[?p] y) (norm-neg[?p] x))
  :use (na0-4[?p] na0-5[?p])))

(local (defrule na0-7[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (> i j))
	     (equal (norm-add[?p] (list 'pop (- i j) p) q) 0)))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-4[?p]
        (:instance na0-1[?p]
                   (i (cadr y))
                   (p (norm-add[?p] (list 'pop (- (cadr x) (cadr y)) (caddr x)) (caddr y)))))))

(local (defrule na0-8[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (> i j)
		  (implies (equal (norm-add[?p] (list 'pop (- i j) p) q) 0)
		           (equal q (norm-neg[?p] (list 'pop (- i j) p)))))
	     (equal (caaddr y) 'pop)))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shfp[?p] y) (:free (i) (norm-neg[?p] (list 'pop i p))))
  :use (na0-4[?p] na0-7[?p])))

(local (defrule na0-9[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (implies (equal (norm-add[?p] (list 'pop (- i j) p) q) 0)
		           (equal q (norm-neg[?p] (list 'pop (- i j) p)))))
	     (not (> i j))))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shf-normp[?p] y))
  :use (na0-4[?p] na0-8[?p])))

(local (defrule na0-10[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (< i j))
	     (equal (norm-add[?p] (list 'pop (- j i) q) p) 0)))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-4[?p]
        (:instance na0-1[?p]
                   (i (cadr x))
                   (p (norm-add[?p] (list 'pop (- (cadr y) (cadr x)) (caddr y)) (caddr x)))))))

(local (defrule na0-11[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (< i j)
		  (implies (equal (norm-add[?p] (list 'pop (- j i) q) p) 0)
		           (equal p (norm-neg[?p] (list 'pop (- j i) q)))))
	     (equal (caaddr x) 'pop)))
  :rule-classes ()
  :expand ((shnfp[?p] x) (shfp[?p] x) (:free (i) (norm-neg[?p] (list 'pop i p))))
  :use (na0-4[?p] na0-10[?p])))

(local (defrule na0-12[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (implies (equal (norm-add[?p] (list 'pop (- j i) q) p) 0)
		           (equal p (norm-neg[?p] (list 'pop (- j i) q)))))
	     (not (< i j))))
  :rule-classes ()
  :expand ((shnfp[?p] x) (shf-normp[?p] x))
  :use (na0-4[?p] na0-11[?p])))

(local (defruled na0-13[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (implies (and (= i j) (equal (norm-add[?p] p q) 0))
		           (equal q (norm-neg[?p] p)))
		  (implies (and (> i j) (equal (norm-add[?p] (list 'pop (- i j) p) q) 0))
		           (equal q (norm-neg[?p] (list 'pop (- i j) p))))
		  (implies (and (< i j) (equal (norm-add[?p] (list 'pop (- j i) q) p) 0))
		           (equal p (norm-neg[?p] (list 'pop (- j i) q)))))
	     (equal (norm-neg[?p] x) y)))
  :expand ((shnfp[?p] x) (shf-normp[?p] x))
  :use (na0-6[?p] na0-9[?p] na0-12[?p])))

(local (defruled na0-14[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0))
	     (and (shnfp[?p] p)
	          (shnfp[?p] q)
		  (implies (> i j) (shnfp[?p] (list 'pop (- i j) p)))
		  (implies (< i j) (shnfp[?p] (list 'pop (- j i) q))))))
  :use na0-4[?p]
  :expand ((:free (x) (shnfp[?p] x)) (shf-normp[?p] x) (shf-normp[?p] y)
           (:free (i p) (shnfp[?p] (list 'pop i p)))
           (:free (i p) (shf-normp[?p] (list 'pop i p))))))

(local (defruled na0-15[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(q (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pop)
		  (equal (norm-add[?p] x y) 0)
		  (implies (and (= i j)
		                (shnfp[?p] p)
                                (shnfp[?p] q)
		                (equal (norm-add[?p] p q) 0))
		           (equal q (norm-neg[?p] p)))
		  (implies (and (> i j)
		                (shnfp[?p] (list 'pop (- i j) p))
                                (shnfp[?p] q)
		                (equal (norm-add[?p] (list 'pop (- i j) p) q) 0))
		           (equal q (norm-neg[?p] (list 'pop (- i j) p))))
		  (implies (and (< i j)
		                (shnfp[?p] (list 'pop (- j i) q))
		                (shnfp[?p] p)
		                (equal (norm-add[?p] (list 'pop (- j i) q) p) 0))
		           (equal p (norm-neg[?p] (list 'pop (- j i) q)))))
	     (equal (norm-neg[?p] x) y)))
  :use (na0-14[?p] na0-13[?p])))

(local (defruled na0-16[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
		(eq (car x) 'pow)
		(equal (norm-add[?p] x y) 0))
           (equal (car y) 'pow))
  :expand ((add-num[?p] x y) (add-num[?p] y x) (shnfp[?p] y) (shfp[?p] y) (norm-add[?p] x y))))

(local (defrule na0-17[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (= i j))
	     (and (equal (norm-add[?p] p r) 0)
	          (equal (norm-add[?p] q s) 0))))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-16[?p]
        (:instance na0-2[?p]
                   (i (cadr x))
                   (p (norm-add[?p] (caddr x) (caddr y)))
                   (q (norm-add[?p] (cadddr x) (cadddr y)))))))

(local (defrule na0-18[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (= i j)
		  (implies (equal (norm-add[?p] p r) 0)
		           (equal r (norm-neg[?p] p)))
		  (implies (equal (norm-add[?p] q s) 0)
		           (equal s (norm-neg[?p] q))))
	     (equal (norm-neg[?p] x) y)))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shfp[?p] y) (norm-neg[?p] x))
  :use (na0-16[?p] na0-17[?p])))

(local (defrule na0-19[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (> i j))
	     (and (equal (norm-add[?p] (list 'pow (- i j) p 0) r) 0)
	          (equal (norm-add[?p] q s) 0))))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-16[?p]
        (:instance na0-2[?p]
                   (i (cadr y))
                   (p (norm-add[?p] (list 'pow (- (cadr x) (cadr y)) (caddr x) 0) (caddr y)))
                   (q (norm-add[?p] (cadddr x) (cadddr y)))))))

(local (defrule na0-20[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (> i j)
		  (implies (equal (norm-add[?p] (list 'pow (- i j) p 0) r) 0)
		           (equal r (norm-neg[?p] (list 'pow (- i j) p 0)))))
	     (and (eq (car r) 'pow)
	          (= (cadddr r) 0))))
  :rule-classes ()
  :disable ((norm-neg[?p]))
  :expand ((shnfp[?p] y) (shfp[?p] y) (:free (i) (norm-neg[?p] (list 'pow i p 0))))
  :use (na0-12[?p] na0-19[?p])))

(local (defrule na0-21[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (implies (equal (norm-add[?p] (list 'pow (- i j) p 0) r) 0)
		           (equal r (norm-neg[?p] (list 'pow (- i j) p 0)))))
	     (not (> i j))))
  :rule-classes ()
  :expand ((shnfp[?p] y) (shf-normp[?p] y))
  :use (na0-16[?p] na0-20[?p])))

(local (defrule na0-22[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (< i j))
	     (and (equal (norm-add[?p] (list 'pow (- j i) r 0) p) 0)
	          (equal (norm-add[?p] s q) 0))))
  :rule-classes ()
  :expand (norm-add[?p] x y)
  :use (na0-16[?p]
        (:instance na0-2[?p]
                   (i (cadr x))
                   (p (norm-add[?p] (list 'pow (- (cadr y) (cadr x)) (caddr y) 0) (caddr x)))
                   (q (norm-add[?p] (cadddr y) (cadddr x)))))))

(local (defrule na0-23[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (< i j)
		  (implies (equal (norm-add[?p] (list 'pow (- j i) r 0) p) 0)
		           (equal p (norm-neg[?p] (list 'pow (- j i) r 0)))))
	     (and (eq (car p) 'pow)
	          (= (cadddr p) 0))))
  :rule-classes ()
  :disable ((norm-neg[?p]))
  :expand ((shnfp[?p] y) (shfp[?p] y) (:free (i) (norm-neg[?p] (list 'pow i p 0))))
  :use (na0-12[?p] na0-22[?p])))

(local (defrule na0-24[?p]
  (let ((i (cadr x))
        (p (caddr x))
	(j (cadr y))
	(r (caddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (implies (equal (norm-add[?p] (list 'pow (- j i) r 0) p) 0)
		           (equal p (norm-neg[?p] (list 'pow (- j i) r 0)))))
	     (not (< i j))))
  :rule-classes ()
  :expand ((shnfp[?p] x) (shf-normp[?p] x))
  :use (na0-16[?p] na0-23[?p])))

(local (defrule na0-25[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (implies (and (= i j) (equal (norm-add[?p] p r) 0))
		           (equal r (norm-neg[?p] p)))
		  (implies (and (= i j) (equal (norm-add[?p] q s) 0))
		           (equal s (norm-neg[?p] q)))
		  (implies (and (> i j) (equal (norm-add[?p] (list 'pow (- i j) p 0) r) 0))
		           (equal r (norm-neg[?p] (list 'pow (- i j) p 0))))
		  (implies (and (< i j) (equal (norm-add[?p] (list 'pow (- j i) r 0) p) 0))
		           (equal p (norm-neg[?p] (list 'pow (- j i) r 0)))))
	     (equal (norm-neg[?p] x) y)))
  :rule-classes ()
  :use (na0-18[?p] na0-21[?p] na0-24[?p])
  :enable shnfp-new[?p]))

(local (defruled na0-26[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0))
	     (and (shnfp[?p] p)
	          (shnfp[?p] q)
	          (shnfp[?p] r)
	          (shnfp[?p] s)
		  (implies (> i j) (shnfp[?p] (list 'pow (- i j) p 0)))
		  (implies (< i j) (shnfp[?p] (list 'pow (- j i) r 0))))))
  :use na0-16[?p]
  :expand ((:free (x) (shnfp[?p] x)) (shf-normp[?p] x) (shf-normp[?p] y)
           (:free (i p q) (shnfp[?p] (list 'pow i p q)))
           (:free (i p q) (shf-normp[?p] (list 'pow i p q))))
  :prep-lemmas
  ((defrule lemma
     (and (shf-normp[?p] 0)
          (shfp[?p] 0))
     :enable shf-normp[?p]
     :disable ((shf-normp[?p]) (shfp[?p]))))))

(local (defruled na0-27[?p]
  (let ((i (cadr x))
        (p (caddr x))
        (q (cadddr x))
	(j (cadr y))
	(r (caddr y))
	(s (cadddr y)))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
                  (eq (car x) 'pow)
		  (equal (norm-add[?p] x y) 0)
		  (implies (and (= i j)
		                (shnfp[?p] p)
				(shnfp[?p] r)
				(equal (norm-add[?p] p r) 0))
		           (equal r (norm-neg[?p] p)))
		  (implies (and (= i j)
		                (shnfp[?p] q)
				(shnfp[?p] s)
				(equal (norm-add[?p] q s) 0))
		           (equal s (norm-neg[?p] q)))
		  (implies (and (> i j)
		                (shnfp[?p] (list 'pow (- i j) p 0))
				(shnfp[?p] r)
				(equal (norm-add[?p] (list 'pow (- i j) p 0) r) 0))
		           (equal r (norm-neg[?p] (list 'pow (- i j) p 0))))
		  (implies (and (< i j)
		                (shnfp[?p] (list 'pow (- j i) r 0))
				(shnfp[?p] p)
				(equal (norm-add[?p] (list 'pow (- j i) r 0) p) 0))
		           (equal p (norm-neg[?p] (list 'pow (- j i) r 0)))))
	     (equal (norm-neg[?p] x) y)))
  :use (na0-26[?p] na0-25[?p])
  :disable norm-neg[?p]))

(in-theory (enable norm-add[?p]))

(local (defrule norm-add-0[?p]
  (implies (and (shnfp[?p] x)
                (shnfp[?p] y)
		(equal (norm-add[?p] x y) 0))
           (equal (norm-neg[?p] x) y))
  :rule-classes ()
  :induct (norm-add[?p] x y)
  :expand (norm-add[?p] x y)
  :hints (
          ("Subgoal *1/13" :use (na0-27[?p]))
          ("Subgoal *1/12" :use (na0-27[?p]))
          ("Subgoal *1/11" :use (na0-27[?p]))
          ("Subgoal *1/10" :use (na0-16[?p]))
          ("Subgoal *1/9" :use (na0-16[?p]))
          ("Subgoal *1/5" :use (na0-15[?p]))
          ("Subgoal *1/4" :use (na0-15[?p]))
          ("Subgoal *1/3" :use (na0-15[?p]))
          ("Subgoal *1/2" :use (na0-4[?p] na0-16[?p]))
          ("Subgoal *1/1" :use (na0-3[?p])))
  :enable shnfp-new[?p]))

(defruled evalh-not-equal[?p]
  (let ((n (evalh-witness[?p] (norm-add[?p] (norm-neg[?p] y) x))))
    (implies (and (shnfp[?p] x)
                  (shnfp[?p] y)
		  (not (equal x y)))
	     (not (equal (evalh[?p] x n) (evalh[?p] y n)))))
  :enable evalh-norm-add[?p]
  :use ((:instance norm-neg-norm-neg[?p] (x y))
        (:instance norm-add-0[?p] (x (norm-neg[?p] y)) (y x))
        (:instance evalh-not-zero[?p] (x (norm-add[?p] (norm-neg[?p] y) x)))))

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

(local-in-theory (enable evalh[?p]))

(local-in-theory (disable acl2::reduce-additive-constant-<))

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

(local (defrule evalh-append0p[?p]
  (implies (and (shnfp[?p] x) (append0p n n0))
           (equal (evalh[?p] x n)
                  (evalh[?p] x n0)))
  :induct (induct-evalh-2 x n n0)
  :enable shnfp-new[?p]
  :disable (expt all-integers)))

(defun list0 (k)
  (if (zp k)
      ()
    (cons 0 (list0 (1- k)))))

(local (defrule append0p-list0
  (append0p n (append n (list0 k)))))

(local (defruled evalh-append-0[?p]
  (implies (shnfp[?p] x)
           (equal (evalh[?p] x (append n (list0 k)))
	          (evalh[?p] x n)))
  :use ((:instance evalh-append0p[?p] (n0 (append n (list0 k)))))))

(defund evalp-witness[?p] (x y vars)
   (let ((n (evalh-witness[?p] (norm-add[?p] (norm-neg[?p] (norm[?p] y vars)) (norm[?p] x vars)))))
     (append n (list0 (- (len vars) (len n))))))

(local (defrule all-ints-list0
  (all-integers (list0 k))))

(local (defrule all-ints-append
  (implies (and (all-integers a)
                (all-integers b))
           (all-integers (append a b)))))

(defruled all-ints-evalp-witness[?p]
  (all-integers (evalp-witness[?p] x y vars))
  :expand (evalp-witness[?p] x y vars))

(local (defrule len-list0
  (equal (len (list0 k))
         (nfix k))))

(local (defrule len-append
  (equal (len (append a b))
         (+ (len a) (len b)))))

(local (defruled len-evalp-witness[?p]
  (>= (len (evalp-witness[?p] x y vars))
      (len vars))
  :expand (evalp-witness[?p] x y vars)))

(defrule evalp-not-equal[?p]
  (let ((a (pairlis$ vars (evalp-witness[?p] x y vars))))
    (implies (and (distinct-symbols vars)
                  (polyp[?p] x vars)
  		  (polyp[?p] y vars)
		  (equal (evalp[?p] x a) (evalp[?p] y a)))
	     (equal (norm[?p] x vars)
	            (norm[?p] y vars))))
  :rule-classes ()
  :expand (evalp-witness[?p] x y vars)
  :enable evalh-append-0[?p]
  :disable (norm-add[?p] evalh-witness[?p])
  :use (len-evalp-witness[?p]
        all-ints-evalp-witness[?p]
        (:instance evalh-not-equal[?p] (x (norm[?p] x vars)) (y (norm[?p] y vars)))
        (:instance evalh-norm[?p] (vals (evalp-witness[?p] x y vars)))
        (:instance evalh-norm[?p] (x y) (vals (evalp-witness[?p] x y vars)))))

;;*********************************************************************************
;;                            Instantiation Macro
;;*********************************************************************************

;; Instantiate generic functions above for paritular subring of comples
;; Arguments of this macro specify names of function and theorem instantiates
(acl2::defmacro defshnf
 (p    ; ?p subring predicate
  &key
  list
  polyp
  evalp closure-evalp
  shfp
  evalh closure-evalh
  shf-normp
  shnfp shnfp-shfp shnfp-pow-q shnfp-pow-p shfp-pop-pow-atom shnfp-num
  norm-pop norm-pop-shnfp norm-pop-normp norm-pop-shfp norm-pop-evalh
  norm-pow norm-pow-shnfp norm-pow-normp norm-pow-shfp norm-pow-evalh
  norm-var shnfp-norm-var evalh-norm-var
  add-num normp-add-num shnfp-add-num evalh-add-num
  add-pop-pop add-pop-pow add-pow-pow
  norm-add evalh-norm-add-num shnfp-norm-add normp-norm-add evalh-norm-add
  norm-neg shnfp-norm-neg evalh-norm-neg norm-neg-norm-neg
  mul-num shnfp-mul-num evalh-mul-num
  mul-pop-pop mul-pop-pow mul-pow-pow norm-mul shnfp-norm-mul evalh-norm-mul
  norm-expt shnfp-norm-expt evalh-norm-expt
  norm shnfp-norm evalh-norm
  evalh-witness evalh-not-zero evalh-not-equal
  evalp-witness all-ints-evalp-witness evalp-not-equal)
 `(progn
; ?p
; list[?p]

(defn ,list (vals)
  (if (consp vals)
      (and (,list (cdr vals))
           (,p (car vals)))
    (null vals)))

; polyp[?p]
(defun ,polyp (x vars)
  (declare (xargs :guard (distinct-symbols vars)))
  (if (atom x)
      (or (,p x) (member x vars))
    (and (true-listp x)
         (case (len x)
           (2 (let ((y (cadr x)))
                (case (car x)
                  (- (,polyp y vars)))))
           (3 (let ((y (cadr x)) (z (caddr x)))
                (case (car x)
                  (+ (and (,polyp y vars) (,polyp z vars)))
                  (- (and (,polyp y vars) (,polyp z vars)))
                  (* (and (,polyp y vars) (,polyp z vars)))
                  (expt (and (,polyp y vars) (natp z))))))))))

; evalp[?p]
(defun ,evalp (x alist)
  (if (,p x)
      x
    (if (atom x)
        (cdr (assoc x alist))
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (+ (,evalp y alist) (,evalp z alist)))
          (- (if (cddr x) (- (,evalp y alist) (,evalp z alist)) (- (,evalp y alist))))
          (* (* (,evalp y alist) (,evalp z alist)))
          (expt (expt (,evalp y alist) (,evalp z alist))))))))

(acl2::def-functional-instance ,closure-evalp
  closure-evalp[?p] ((?p ,p)
                     (list[?p] ,list)
                     (polyp[?p] ,polyp)
                     (evalp[?p] ,evalp)))

; shfp[?p]
(defn ,shfp (x)
  (if (atom x)
      (,p x)
    (case (car x)
      (pop (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (,shfp (caddr x))
                (null (cdddr x))))
      (pow (and (consp (cdr x))   (natp (cadr x))
                (consp (cddr x))  (,shfp (caddr x))
                (consp (cdddr x)) (,shfp (cadddr x))
                (null (cddddr x)))))))

; evalh[?p]
(defun ,evalh (x vals)
  (declare (xargs :guard (and (,shfp x)
                              (,list vals))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem evalh[?p])
                                              (?p ,p)
                                              (list[?p] ,list)
                                              (shfp[?p] ,shfp)
                                              (evalh[?p] ,evalh))))))
  (if (atom x)
      x
    (case (car x)
      (pop (,evalh (caddr x) (nthcdr (cadr x) vals)))
      (pow (+ (* (expt (if (consp vals) (car vals) 0) (cadr x))
                 (,evalh (caddr x) vals))
             (,evalh (cadddr x) (cdr vals)))))))

(acl2::def-functional-instance ,closure-evalh
  closure-evalh[?p] ((?p ,p)
                     (list[?p] ,list)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)))

; shf-normp[?p]
(defund ,shf-normp (x)
  (declare (xargs :guard (,shfp x)))
  (if (atom x)
      t
    (let ((i (cadr x)) (p (caddr x)) (q (cadddr x)))
      (case (car x)
        (pop (and (not (= i 0))
                  (consp p)
                  (eql (car p) 'pow)
                  (,shf-normp p)))
        (pow (and (not (= i 0))
                  (,shf-normp p)
                  (,shf-normp q)
                  (if (atom p)
                      (not (= p 0))
                    (not (and (eql (car p) 'pow)
                              (equal (cadddr p) 0))))))))))

; shnfp[?p]
(defnd ,shnfp (x)
  (and (,shfp x) (,shf-normp x)))

(acl2::def-functional-instance ,shnfp-shfp
  shnfp-shfp[?p] ((?p ,p)
                  (shfp[?p] ,shfp)
                  (shnfp[?p] ,shnfp)))

(acl2::def-functional-instance ,shnfp-pow-q
  shnfp-pow-q[?p] ((?p ,p)
                   (shfp[?p] ,shfp)
                   (shf-normp[?p] ,shf-normp)
                   (shnfp[?p] ,shnfp))
  :hints (("subgoal 2" :in-theory (enable ,shnfp))
          ("subgoal 1" :in-theory (enable ,shf-normp))))

(acl2::def-functional-instance ,shnfp-pow-p
  shnfp-pow-p[?p] ((?p ,p)
                   (shfp[?p] ,shfp)
                   (shf-normp[?p] ,shf-normp)
                   (shnfp[?p] ,shnfp)))

(acl2::def-functional-instance ,shfp-pop-pow-atom
  shfp-pop-pow-atom[?p] ((?p ,p)
                         (shfp[?p] ,shfp)))

(acl2::def-functional-instance ,shnfp-num
  shnfp-num[?p] ((?p ,p)
                 (shfp[?p] ,shfp)
                 (shf-normp[?p] ,shf-normp)
                 (shnfp[?p] ,shnfp)))

; norm-pop[?p]
(defun ,norm-pop (i p)
  (declare (xargs :guard (and (natp i)
                              (,shnfp p))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-pop[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop))))))
  (if (or (= i 0) (atom p))
      p
    (if (eql (car p) 'pop)
        (list 'pop (+ i (cadr p)) (caddr p))
      (list 'pop i p))))

(acl2::def-functional-instance ,norm-pop-shnfp
  norm-pop-shnfp[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pop[?p] ,norm-pop)))

(in-theory (disable ,norm-pop))

(acl2::def-functional-instance ,norm-pop-normp
  norm-pop-normp[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pop[?p] ,norm-pop)))

(acl2::def-functional-instance ,norm-pop-shfp
  norm-pop-shfp[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)))

(acl2::def-functional-instance ,norm-pop-evalh
  norm-pop-evalh[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)))

; norm-pow[?p]
(defun ,norm-pow (i p q)
  (declare (xargs :guard (and (natp i)
                              (,shnfp p)
                              (,shnfp q))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-pow[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop)
                                              (norm-pow[?p] ,norm-pow))))))
  (if (equal p 0)
      (,norm-pop 1 q)
    (if (and (consp p) (eql (car p) 'pow) (equal (cadddr p) 0))
        (list 'pow (+ i (cadr p)) (caddr p) q)
      (list 'pow i p q))))

(acl2::def-functional-instance ,norm-pow-shnfp
  norm-pow-shnfp[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pop[?p] ,norm-pop)
                      (norm-pow[?p] ,norm-pow)))

(in-theory (disable ,norm-pow))

(acl2::def-functional-instance ,norm-pow-normp
  norm-pow-normp[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pop[?p] ,norm-pop)
                      (norm-pow[?p] ,norm-pow)))

(acl2::def-functional-instance ,norm-pow-shfp
  norm-pow-shfp[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)))

(acl2::def-functional-instance ,norm-pow-evalh
  norm-pow-evalh[?p] ((?p ,p)
                      (list[?p] ,list)
                      (shfp[?p] ,shfp)
                      (evalh[?p] ,evalh)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pop[?p] ,norm-pop)
                      (norm-pow[?p] ,norm-pow)))

; shnfp-norm-var[?p]
(defun ,norm-var (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (member x vars))))
  (,norm-pop (var-index x vars) '(pow 1 1 0)))

(defrule ,shnfp-norm-var
  (implies (member x vars)
           (,shnfp (,norm-var x vars))))

(defrule ,evalh-norm-var
  (implies (and (distinct-symbols vars)
                (,list vals)
                (<= (len vars) (len vals))
                (member x vars))
           (equal (,evalh (,norm-var x vars) vals)
                  (,evalp x (pairlis$ vars vals))))
  :use lemma
  :prep-lemmas
  ((acl2::def-functional-instance lemma
     evalh-norm-var[?p] ((?p ,p)
                         (list[?p] ,list)
                         (evalp[?p] ,evalp)
                         (shfp[?p] ,shfp)
                         (evalh[?p] ,evalh)
                         (shf-normp[?p] ,shf-normp)
                         (shnfp[?p] ,shnfp)
                         (norm-pop[?p] ,norm-pop)
                         (norm-var[?p] ,norm-var)))))

(in-theory (disable ,norm-var))

; add-int[?p]
(defun ,add-num (x y)
  (declare (xargs :guard (and (,p x)
                              (,shnfp y))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem add-num[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (add-num[?p] ,add-num))))))
  (if (atom y)
      (+ x y)
    (case (car y)
      (pow (list 'pow (cadr y) (caddr y) (,add-num x (cadddr y))))
      (pop (list 'pop (cadr y) (,add-num x (caddr y)))))))

(acl2::def-functional-instance ,normp-add-num
  normp-add-num[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (add-num[?p] ,add-num)))
(in-theory (disable ,add-num))

(acl2::def-functional-instance ,shnfp-add-num
  shnfp-add-num[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (add-num[?p] ,add-num)))

(acl2::def-functional-instance ,evalh-add-num
  evalh-add-num[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (add-num[?p] ,add-num)))

(defmacro ,add-pop-pop (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (,',norm-pop i (,',norm-add p q))
          (if (> i j)
              (,',norm-pop j (,',norm-add (list 'pop (- i j) p) q))
            (,',norm-pop i (,',norm-add (list 'pop (- j i) q) p))))))

(defmacro ,add-pop-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (list 'pow j q (,',norm-add r p))
       (list 'pow j q (,',norm-add r (list 'pop (1- i) p))))))

(defmacro ,add-pow-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))
     (if (= i j)
         (,',norm-pow i (,',norm-add p r) (,',norm-add q s))
       (if (> i j)
           (,',norm-pow j (,',norm-add (list 'pow (- i j) p 0) r) (,',norm-add q s))
         (,',norm-pow i (,',norm-add (list 'pow (- j i) r 0) p) (,',norm-add s q))))))

; norm-add[?p]
(defun ,norm-add (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (,shnfp x)
                              (,shnfp y))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-add[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pow[?p] ,norm-pow)
                                              (norm-pop[?p] ,norm-pop)
                                              (add-num[?p] ,add-num)
                                              (norm-add[?p] ,norm-add))))))
  (if (atom x)
      (,add-num x y)
    (if (atom y)
        (,add-num y x)
      (case (car x)
        (pop (case (car y)
               (pop (,add-pop-pop x y))
               (pow (,add-pop-pow x y))))
        (pow (case (car y)
               (pop (,add-pop-pow y x))
               (pow (,add-pow-pow x y))))))))

(acl2::def-functional-instance ,evalh-norm-add-num
  evalh-norm-add-num[?p] ((?p ,p)
                          (shfp[?p] ,shfp)
                          (evalh[?p] ,evalh)
                          (shf-normp[?p] ,shf-normp)
                          (shnfp[?p] ,shnfp)
                          (norm-pow[?p] ,norm-pow)
                          (norm-pop[?p] ,norm-pop)
                          (add-num[?p] ,add-num)
                          (norm-add[?p] ,norm-add)))

(acl2::def-functional-instance ,shnfp-norm-add
  shnfp-norm-add[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pow[?p] ,norm-pow)
                      (norm-pop[?p] ,norm-pop)
                      (add-num[?p] ,add-num)
                      (norm-add[?p] ,norm-add)))

(acl2::def-functional-instance ,normp-norm-add
  normp-norm-add[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pow[?p] ,norm-pow)
                      (norm-pop[?p] ,norm-pop)
                      (add-num[?p] ,add-num)
                      (norm-add[?p] ,norm-add)))

(acl2::def-functional-instance ,evalh-norm-add
  evalh-norm-add[?p] ((?p ,p)
                      (list[?p] ,list)
                      (shfp[?p] ,shfp)
                      (evalh[?p] ,evalh)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-pow[?p] ,norm-pow)
                      (norm-pop[?p] ,norm-pop)
                      (add-num[?p] ,add-num)
                      (norm-add[?p] ,norm-add)))

(defun ,norm-neg (x)
  (declare (xargs :guard (,shnfp x)
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-neg[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-neg[?p] ,norm-neg))))))
  (if (atom x)
      (- x)
    (case (car x)
      (pop (list 'pop (cadr x) (,norm-neg (caddr x))))
      (pow (list 'pow (cadr x) (,norm-neg (caddr x)) (,norm-neg (cadddr x)))))))

(acl2::def-functional-instance ,shnfp-norm-neg
  shnfp-norm-neg[?p] ((?p ,p)
                      (shfp[?p] ,shfp)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-neg[?p] ,norm-neg)))

(acl2::def-functional-instance ,evalh-norm-neg
  evalh-norm-neg[?p] ((?p ,p)
                      (list[?p] ,list)
                      (shfp[?p] ,shfp)
                      (evalh[?p] evalh)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (norm-neg[?p] ,norm-neg)))

(acl2::def-functional-instance ,norm-neg-norm-neg
  norm-neg-norm-neg[?p] ((?p ,p)
                         (shfp[?p] ,shfp)
                         (shf-normp[?p] ,shf-normp)
                         (shnfp[?p] ,shnfp)
                         (norm-neg[?p] ,norm-neg)))

; mul-num[?p]
(defund ,mul-num (x y)
  (declare (xargs :guard (and (,p x)
                              (,shnfp y))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem mul-num[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop)
                                              (norm-pow[?p] ,norm-pow)
                                              (mul-num[?p] ,mul-num))))))
  (if (= x 0)
      0
    (if (atom y)
        (* x y)
      (case (car y)
        (pop (,norm-pop (cadr y) (,mul-num x (caddr y))))
        (pow (,norm-pow (cadr y) (,mul-num x (caddr y)) (,mul-num x (cadddr y))))))))

(acl2::def-functional-instance ,shnfp-mul-num
  shnfp-mul-num[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (mul-num[?p] ,mul-num)))

(acl2::def-functional-instance ,evalh-mul-num
  evalh-mul-num[?p] ((?p ,p)
                     (list[?p] ,list)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (mul-num[?p] ,mul-num)))
(defmacro ,mul-pop-pop (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)))
     (if (= i j)
         (,',norm-pop i (,',norm-mul p q))
       (if (> i j)
           (,',norm-pop j (,',norm-mul (list 'pop (- i j) p) q))
         (,',norm-pop i (,',norm-mul (list 'pop (- j i) q) p))))))

(defmacro ,mul-pop-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x))
         (j (cadr ,y)) (q (caddr ,y)) (r (cadddr ,y)))
     (if (= i 1)
         (,',norm-pow j (,',norm-mul ,x q) (,',norm-mul p r))
       (,',norm-pow j (,',norm-mul ,x q) (,',norm-mul (list 'pop (1- i) p) r)))))

(defmacro ,mul-pow-pow (x y)
  `(let ((i (cadr ,x)) (p (caddr ,x)) (q (cadddr ,x))   ;x = p * z^i + q
         (j (cadr ,y)) (r (caddr ,y)) (s (cadddr ,y)))  ;y = r * z^j + s
     (,',norm-add (,',norm-add (,',norm-pow (+ i j) (,',norm-mul p r) (,',norm-mul q s))  ;p * r * z^(i+j) + q * s
                         (,',norm-pow i (,',norm-mul p (,',norm-pop 1 s)) 0))       ;p * s * z^i
               (,',norm-pow j (,',norm-mul r (,',norm-pop 1 q)) 0))))               ;r * q * z^j

(defun ,norm-mul (x y)
  (declare (xargs :measure (+ (shf-count x) (shf-count y))
                  :guard (and (,shnfp x)
                              (,shnfp y))
                  :hints (("goal" :use (:functional-instance
                                        (:termination-theorem norm-mul[?p])
                                        (?p ,p)
                                        (shfp[?p] ,shfp)
                                        (shf-normp[?p] ,shf-normp)
                                        (shnfp[?p] ,shnfp)
                                        (norm-pop[?p] ,norm-pop)
                                        (norm-pow[?p] ,norm-pow)
                                        (add-num[?p] ,add-num)
                                        (norm-add[?p] ,norm-add)
                                        (mul-num[?p] ,mul-num)
                                        (norm-mul[?p] ,norm-mul))))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-mul[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop)
                                              (norm-pow[?p] ,norm-pow)
                                              (add-num[?p] ,add-num)
                                              (norm-add[?p] ,norm-add)
                                              (mul-num[?p] ,mul-num)
                                              (norm-mul[?p] ,norm-mul))))))
  (if (atom x)
      (,mul-num x y)
    (if (atom y)
        (,mul-num y x)
      (case (car x)
        (pop (case (car y)
               (pop (,mul-pop-pop x y))
               (pow (,mul-pop-pow x y))))
        (pow (case (car y)
               (pop (,mul-pop-pow y x))
               (pow (,mul-pow-pow x y))))))))

(acl2::def-functional-instance ,shnfp-norm-mul
  shnfp-norm-mul[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (add-num[?p] ,add-num)
                     (norm-add[?p] ,norm-add)
                     (mul-num[?p] ,mul-num)
                     (norm-mul[?p] ,norm-mul)))


(acl2::def-functional-instance ,evalh-norm-mul
  evalh-norm-mul[?p] ((?p ,p)
                     (list[?p] ,list)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (add-num[?p] ,add-num)
                     (norm-add[?p] ,norm-add)
                     (mul-num[?p] ,mul-num)
                     (norm-mul[?p] ,norm-mul)))

; norm-expt[?p]
(defun ,norm-expt (x k)
  (declare (xargs :guard (and (,shnfp x)
                              (natp k))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm-expt[?p])
                                              (?p ,p)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop)
                                              (norm-pow[?p] ,norm-pow)
                                              (add-num[?p] ,add-num)
                                              (norm-add[?p] ,norm-add)
                                              (mul-num[?p] ,mul-num)
                                              (norm-mul[?p] ,norm-mul)
                                              (norm-expt[?p] ,norm-expt))))))
  (if (zp k)
      1
    (,norm-mul x (,norm-expt x (1- k)))))

(acl2::def-functional-instance ,shnfp-norm-expt
  shnfp-norm-expt[?p] ((?p ,p)
                     (shfp[?p] ,shfp)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (add-num[?p] ,add-num)
                     (norm-add[?p] ,norm-add)
                     (mul-num[?p] ,mul-num)
                     (norm-mul[?p] ,norm-mul)
                     (norm-expt[?p] ,norm-expt)))
(in-theory (disable ,norm-expt))

(acl2::def-functional-instance ,evalh-norm-expt
  evalh-norm-expt[?p] ((?p ,p)
                     (list[?p] ,list)
                     (shfp[?p] ,shfp)
                     (evalh[?p] ,evalh)
                     (shf-normp[?p] ,shf-normp)
                     (shnfp[?p] ,shnfp)
                     (norm-pop[?p] ,norm-pop)
                     (norm-pow[?p] ,norm-pow)
                     (add-num[?p] ,add-num)
                     (norm-add[?p] ,norm-add)
                     (mul-num[?p] ,mul-num)
                     (norm-mul[?p] ,norm-mul)
                     (norm-expt[?p] ,norm-expt)))

; norm[?p]
(defun ,norm (x vars)
  (declare (xargs :guard (and (distinct-symbols vars)
                              (,polyp x vars))
                  :guard-hints (("goal" :use (:functional-instance
                                              (:guard-theorem norm[?p])
                                              (?p ,p)
                                              (polyp[?p] ,polyp)
                                              (shfp[?p] ,shfp)
                                              (shf-normp[?p] ,shf-normp)
                                              (shnfp[?p] ,shnfp)
                                              (norm-pop[?p] ,norm-pop)
                                              (norm-pow[?p] ,norm-pow)
                                              (norm-var[?p] ,norm-var)
                                              (add-num[?p] ,add-num)
                                              (norm-add[?p] ,norm-add)
                                              (norm-neg[?p] ,norm-neg)
                                              (mul-num[?p] ,mul-num)
                                              (norm-mul[?p] ,norm-mul)
                                              (norm-expt[?p] ,norm-expt)
                                              (norm[?p] ,norm))))))
  (if (,p x)
      x
    (if (atom x)
        (,norm-var x vars)
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (,norm-add (,norm y vars) (,norm z vars)))
          (- (if (cddr x) (,norm-add (,norm y vars) (,norm-neg (,norm z vars))) (,norm-neg (,norm y vars))))
          (* (,norm-mul (,norm y vars) (,norm z vars)))
          (expt (,norm-expt (,norm y vars) (,norm z vars))))))))

(acl2::def-functional-instance ,shnfp-norm
  shnfp-norm[?p] ((?p ,p)
                  (polyp[?p] ,polyp)
                  (shfp[?p] ,shfp)
                  (shf-normp[?p] ,shf-normp)
                  (shnfp[?p] ,shnfp)
                  (norm-pop[?p] ,norm-pop)
                  (norm-pow[?p] ,norm-pow)
                  (norm-var[?p] ,norm-var)
                  (add-num[?p] ,add-num)
                  (norm-add[?p] ,norm-add)
                  (norm-neg[?p] ,norm-neg)
                  (mul-num[?p] ,mul-num)
                  (norm-mul[?p] ,norm-mul)
                  (norm-expt[?p] ,norm-expt)
                  (norm[?p] ,norm)))
(in-theory (disable ,norm))

(acl2::def-functional-instance ,evalh-norm
  evalh-norm[?p] ((?p ,p)
                  (polyp[?p] ,polyp)
                  (list[?p] ,list)
                  (evalp[?p] ,evalp)
                  (shfp[?p] ,shfp)
                  (evalh[?p] ,evalh)
                  (shf-normp[?p] ,shf-normp)
                  (shnfp[?p] ,shnfp)
                  (norm-pop[?p] ,norm-pop)
                  (norm-pow[?p] ,norm-pow)
                  (norm-var[?p] ,norm-var)
                  (add-num[?p] ,add-num)
                  (norm-add[?p] ,norm-add)
                  (norm-neg[?p] ,norm-neg)
                  (mul-num[?p] ,mul-num)
                  (norm-mul[?p] ,norm-mul)
                  (norm-expt[?p] ,norm-expt)
                  (norm[?p] ,norm)))

; (evalh-witness[?p] evalh-witness)
(defun ,evalh-witness (x)
  (declare (xargs :guard (,shnfp x)
                  :guard-hints (("goal" :in-theory (e/d (,evalh-witness) (max abs))
                                 :use (:functional-instance
                                       (:guard-theorem evalh-witness[?p])
                                       (?p ,p)
                                       (list[?p] ,list)
                                       (shfp[?p] ,shfp)
                                       (shf-normp[?p] ,shf-normp)
                                       (shnfp[?p] ,shnfp)
                                       (evalh[?p] ,evalh)
                                       (evalh-witness[?p] ,evalh-witness))))))
  (if (atom x)
      ()
    (case (car x)
      (pop (let ((i (cadr x))
                 (p (caddr x)))
             (pad0 i (,evalh-witness p))))
      (pow (let* ((p (caddr x))
                  (q (cadddr x))
                  (n (,evalh-witness p))
                  (vq (,evalh q (cdr n)))
                  (normq (+ (abs (realpart vq)) (abs (imagpart vq)))))
             (if (atom p)
                 (let ((normp (+ (abs (realpart p)) (abs (imagpart p)))))
                   (list (max 1 (cg (/ (1+ normq) normp)))))
               (cons (max (car n) (1+ (cg normq))) (cdr n))))))))

(acl2::def-functional-instance ,evalh-not-zero
  evalh-not-zero[?p] ((?p ,p)
                      (list[?p] ,list)
                      (shfp[?p] ,shfp)
                      (evalh[?p] ,evalh)
                      (shf-normp[?p] ,shf-normp)
                      (shnfp[?p] ,shnfp)
                      (evalh-witness[?p] ,evalh-witness)))

(acl2::def-functional-instance ,evalh-not-equal
  evalh-not-equal[?p] ((?p ,p)
                       (list[?p] ,list)
                       (shfp[?p] ,shfp)
                       (evalh[?p] ,evalh)
                       (shf-normp[?p] ,shf-normp)
                       (shnfp[?p] ,shnfp)
                       (norm-pop[?p] ,norm-pop)
                       (norm-pow[?p] ,norm-pow)
                       (norm-var[?p] ,norm-var)
                       (add-num[?p] ,add-num)
                       (norm-add[?p] ,norm-add)
                       (norm-neg[?p] ,norm-neg)
                       (evalh-witness[?p] ,evalh-witness)))

(defun ,evalp-witness (x y vars)
   (let ((n (,evalh-witness (,norm-add (,norm-neg (,norm y vars)) (,norm x vars)))))
     (append n (list0 (- (len vars) (len n))))))

(acl2::def-functional-instance ,all-ints-evalp-witness
  all-ints-evalp-witness[?p] ((?p ,p)
                              (evalp[?p] ,evalp)
                              (shfp[?p] ,shfp)
                              (evalh[?p] ,evalh)
                              (shf-normp[?p] ,shf-normp)
                              (shnfp[?p] ,shnfp)
                              (norm-pop[?p] ,norm-pop)
                              (norm-pow[?p] ,norm-pow)
                              (norm-var[?p] ,norm-var)
                              (add-num[?p] ,add-num)
                              (norm-add[?p] ,norm-add)
                              (norm-neg[?p] ,norm-neg)
                              (mul-num[?p] ,mul-num)
                              (norm-mul[?p] ,norm-mul)
                              (norm-expt[?p] ,norm-expt)
                              (norm[?p] ,norm)
                              (evalh-witness[?p] ,evalh-witness)
                              (evalp-witness[?p] ,evalp-witness)))

(acl2::def-functional-instance ,evalp-not-equal
  evalp-not-equal[?p] ((?p ,p)
                       (polyp[?p] ,polyp)
                       (evalp[?p] ,evalp)
                       (shfp[?p] ,shfp)
                       (evalh[?p] ,evalh)
                       (shf-normp[?p] ,shf-normp)
                       (shnfp[?p] ,shnfp)
                       (norm-pop[?p] ,norm-pop)
                       (norm-pow[?p] ,norm-pow)
                       (norm-var[?p] ,norm-var)
                       (add-num[?p] ,add-num)
                       (norm-add[?p] ,norm-add)
                       (norm-neg[?p] ,norm-neg)
                       (mul-num[?p] ,mul-num)
                       (norm-mul[?p] ,norm-mul)
                       (norm-expt[?p] ,norm-expt)
                       (norm[?p] ,norm)
                       (evalh-witness[?p] ,evalh-witness)
                       (evalp-witness[?p] ,evalp-witness)))))

;;*********************************************************************************
;;                            Instantiations
;;*********************************************************************************

(defshnf integerp
  :list                   all-integers
  :polyp                  polyp
  :evalp                  evalp
  :closure-evalp          integerp-evalp
  :shfp                   shfp
  :evalh                  evalh
  :closure-evalh          integerp-evalh
  :shf-normp              shf-normp
  :shnfp                  shnfp
  :shnfp-shfp             shnfp-shfp
  :shnfp-pow-q            shnfp-pow-q
  :shnfp-pow-p            shnfp-pow-p
  :shfp-pop-pow-atom      shfp-pop-pow-atom
  :shnfp-num              shnfp-int
  :norm-pop               norm-pop
  :norm-pop-shnfp         norm-pop-shnfp
  :norm-pop-normp         norm-pop-normp
  :norm-pop-shfp          norm-pop-shfp
  :norm-pop-evalh         norm-pop-evalh
  :norm-pow               norm-pow
  :norm-pow-shnfp         norm-pow-shnfp
  :norm-pow-normp         norm-pow-normp
  :norm-pow-shfp          norm-pow-shfp
  :norm-pow-evalh         norm-pow-evalh
  :norm-var               norm-var
  :shnfp-norm-var         shnfp-norm-var
  :evalh-norm-var         evalh-norm-var
  :add-num                add-int
  :normp-add-num          normp-add-int
  :shnfp-add-num          shnfp-add-int
  :evalh-add-num          evalh-add-int
  :add-pop-pop            add-pop-pop
  :add-pop-pow            add-pop-pow
  :add-pow-pow            add-pow-pow
  :norm-add               norm-add
  :evalh-norm-add-num     evalh-norm-add-int
  :shnfp-norm-add         shnfp-norm-add
  :normp-norm-add         normp-norm-add
  :evalh-norm-add         evalh-norm-add
  :norm-neg               norm-neg
  :shnfp-norm-neg         shnfp-norm-neg
  :evalh-norm-neg         evalh-norm-neg
  :norm-neg-norm-neg      norm-neg-norm-neg
  :mul-num                mul-int
  :shnfp-mul-num          shnfp-mul-int
  :evalh-mul-num          evalh-mul-int
  :mul-pop-pop            mul-pop-pop
  :mul-pop-pow            mul-pop-pow
  :mul-pow-pow            mul-pow-pow
  :norm-mul               norm-mul
  :shnfp-norm-mul         shnfp-norm-mul
  :evalh-norm-mul         evalh-norm-mul
  :norm-expt              norm-expt
  :shnfp-norm-expt        shnfp-norm-expt
  :evalh-norm-expt        evalh-norm-expt
  :norm                   norm
  :shnfp-norm             shnfp-norm
  :evalh-norm             evalh-norm
  :evalh-witness          evalh-witness
  :evalh-not-zero         evalh-not-zero
  :evalh-not-equal        evalh-not-equal
  :evalp-witness          evalp-witness
  :all-ints-evalp-witness all-ints-evalp-witness
  :evalp-not-equal        evalp-not-equal)

(defshnf real/rationalp
  :list                   all-real/rationals
  :polyp                  real-polyp
  :evalp                  real-evalp
  :closure-evalp          realp-evalp
  :shfp                   real-rshfp
  :evalh                  real-evalh
  :closure-evalh          realp-evalh
  :shf-normp              real-shf-normp
  :shnfp                  real-shnfp
  :shnfp-shfp             real-shnfp-shfp
  :shnfp-pow-q            real-shnfp-pow-q
  :shnfp-pow-p            real-shnfp-pow-p
  :shfp-pop-pow-atom      real-shfp-pop-pow-atom
  :shnfp-num              shnfp-real
  :norm-pop               real-norm-pop
  :norm-pop-shnfp         real-norm-pop-shnfp
  :norm-pop-normp         real-norm-pop-normp
  :norm-pop-shfp          real-norm-pop-shfp
  :norm-pop-evalh         real-norm-pop-evalh
  :norm-pow               real-norm-pow
  :norm-pow-shnfp         real-norm-pow-shnfp
  :norm-pow-normp         real-norm-pow-normp
  :norm-pow-shfp          real-norm-pow-shfp
  :norm-pow-evalh         real-norm-pow-evalh
  :norm-var               real-norm-var
  :shnfp-norm-var         real-shnfp-norm-var
  :evalh-norm-var         real-evalh-norm-var
  :add-num                add-real
  :normp-add-num          normp-add-real
  :shnfp-add-num          shnfp-add-real
  :evalh-add-num          evalh-add-real
  :add-pop-pop            real-add-pop-pop
  :add-pop-pow            real-add-pop-pow
  :add-pow-pow            real-add-pow-pow
  :norm-add               real-norm-add
  :evalh-norm-add-num     evalh-norm-add-real
  :shnfp-norm-add         real-shnfp-norm-add
  :normp-norm-add         real-normp-norm-add
  :evalh-norm-add         real-evalh-norm-add
  :norm-neg               real-norm-neg
  :shnfp-norm-neg         real-shnfp-norm-neg
  :evalh-norm-neg         real-evalh-norm-neg
  :norm-neg-norm-neg      real-norm-neg-norm-neg
  :mul-num                mul-real
  :shnfp-mul-num          shnfp-mul-real
  :evalh-mul-num          evalh-mul-real
  :mul-pop-pop            real-mul-pop-pop
  :mul-pop-pow            real-mul-pop-pow
  :mul-pow-pow            real-mul-pow-pow
  :norm-mul               real-norm-mul
  :shnfp-norm-mul         real-shnfp-norm-mul
  :evalh-norm-mul         real-evalh-norm-mul
  :norm-expt              real-norm-expt
  :shnfp-norm-expt        real-shnfp-norm-expt
  :evalh-norm-expt        real-evalh-norm-expt
  :norm                   real-norm
  :shnfp-norm             real-shnfp-norm
  :evalh-norm             real-evalh-norm
  :evalh-witness          real-evalh-witness
  :evalh-not-zero         real-evalh-not-zero
  :evalh-not-equal        real-evalh-not-equal
  :evalp-witness          real-evalp-witness
  :all-ints-evalp-witness areal-ll-ints-evalp-witness
  :evalp-not-equal        real-evalp-not-equal)

(defshnf acl2-numberp
  :list                   all-numbers
  :polyp                  num-polyp
  :evalp                  num-evalp
  :closure-evalp          acl2-numberp-evalp
  :shfp                   num-rshfp
  :evalh                  num-evalh
  :closure-evalh          acl2-numberp-evalh
  :shf-normp              num-shf-normp
  :shnfp                  num-shnfp
  :shnfp-shfp             num-shnfp-shfp
  :shnfp-pow-q            num-shnfp-pow-q
  :shnfp-pow-p            num-shnfp-pow-p
  :shfp-pop-pow-atom      num-shfp-pop-pow-atom
  :shnfp-num              shnfp-num
  :norm-pop               num-norm-pop
  :norm-pop-shnfp         num-norm-pop-shnfp
  :norm-pop-normp         num-norm-pop-normp
  :norm-pop-shfp          num-norm-pop-shfp
  :norm-pop-evalh         num-norm-pop-evalh
  :norm-pow               num-norm-pow
  :norm-pow-shnfp         num-norm-pow-shnfp
  :norm-pow-normp         num-norm-pow-normp
  :norm-pow-shfp          num-norm-pow-shfp
  :norm-pow-evalh         num-norm-pow-evalh
  :norm-var               num-norm-var
  :shnfp-norm-var         num-shnfp-norm-var
  :evalh-norm-var         num-evalh-norm-var
  :add-num                add-num
  :normp-add-num          normp-add-num
  :shnfp-add-num          shnfp-add-num
  :evalh-add-num          evalh-add-num
  :add-pop-pop            num-add-pop-pop
  :add-pop-pow            num-add-pop-pow
  :add-pow-pow            num-add-pow-pow
  :norm-add               num-norm-add
  :evalh-norm-add-num     evalh-norm-add-num
  :shnfp-norm-add         num-shnfp-norm-add
  :normp-norm-add         num-normp-norm-add
  :evalh-norm-add         num-evalh-norm-add
  :norm-neg               num-norm-neg
  :shnfp-norm-neg         num-shnfp-norm-neg
  :evalh-norm-neg         num-evalh-norm-neg
  :norm-neg-norm-neg      num-norm-neg-norm-neg
  :mul-num                mul-num
  :shnfp-mul-num          shnfp-mul-num
  :evalh-mul-num          evalh-mul-num
  :mul-pop-pop            num-mul-pop-pop
  :mul-pop-pow            num-mul-pop-pow
  :mul-pow-pow            num-mul-pow-pow
  :norm-mul               num-norm-mul
  :shnfp-norm-mul         num-shnfp-norm-mul
  :evalh-norm-mul         num-evalh-norm-mul
  :norm-expt              num-norm-expt
  :shnfp-norm-expt        num-shnfp-norm-expt
  :evalh-norm-expt        num-evalh-norm-expt
  :norm                   num-norm
  :shnfp-norm             num-shnfp-norm
  :evalh-norm             num-evalh-norm
  :evalh-witness          num-evalh-witness
  :evalh-not-zero         num-evalh-not-zero
  :evalh-not-equal        num-evalh-not-equal
  :evalp-witness          num-evalp-witness
  :all-ints-evalp-witness num-all-ints-evalp-witness
  :evalp-not-equal        num-evalp-not-equal)


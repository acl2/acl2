;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")
(include-book "rtl/rel11/lib/top" :dir :system)
(include-book "projects/groups/groups" :dir :system)
(include-book "projects/linear/field" :dir :system)
(include-book "projects/numbers/fermat" :dir :system)
(local (include-book "support/extensions"))

;; A field may be represented in ACL2 as a set of 7 functions that satisfy the usual field axioms: a predicate
;; that recognizes field elements, 2 binary operations, 2 nullary identity elements, and 2 unary inverse
;; operators.  An example of a field is the generic field specified by the encapsulation in the file
;; "../linear/field.lisp".

;; We would like to be able to say "Let f be a field" in the ACL2 logic.  That is, we would like to define an
;; ACL2 predicate fieldp that recognizes fields, but in general, fields are not ACL2 objects.  We can, however,
;; define as ACL2 objects a certain class of fields that is sufficiently general to allow us to do some
;; interesting things.

;; We are interested in field extensions: algebraic number fields, which are finite extensions of the rationals, 
;; and finite fields, which are finite extensions of prime fields.  We shall also consider finite extensions of
;; the generic field mentioned above, because any results pertaining to such an extension may be applied, by
;; functional instantiation, to an extension of any field.  We shall informally refer to the rational field as Q
;; and to the prime field of order p as Fp.  We have previously referred to the generic field as F, but
;; henceforth we shall refer to it as F0 so that we may refer to an arbitrary field as F.  All of these fields
;; are called "base fields" and are encoded as follows:

(defund fbasep (f)
  (or (zerop f)       ;the rational field is encoded as 0
      (primep f)      ;the prime field of order p is encoded as p
      (equal f 'f0))) ;the generic field is encoded as the symbol f0

;; Recognizer of base field elements:

(defund beltp (x f)
  (cond ((zerop f) (rationalp x))
        ((primep f) (member x (ninit f)))
	(t (fp x))))

;; Base field operations:

(defund badd (x y f)
  (cond ((zerop f) (+ x y))
        ((primep f) (mod (+ x y) f))
	(t (f+ x y))))

(defund bmul (x y f)
  (cond ((zerop f) (* x y))
        ((primep f) (mod (* x y) f))
	(t (f* x y))))

;; Additive and multiplicative identities:

(defund bzero (f)
  (if (integerp f) 0 (f0)))

(defund bone (f)
  (if (integerp f) 1 (f1)))

;; Additive and multiplicative inverses:

(defund bneg (x f)
  (cond ((zerop f) (- x))
        ((primep f) (mod (- x) f))
	(t (f- x))))

(defund brecip (x f)
  (cond ((zerop f) (/ x))
	;the following is inspired by Fermat's Theorem (see "../numbers/fermat.lisp"):
        ((primep f) (mod (expt x (- f 2)) f))
	(t (f/ x))))

(in-theory (disable (fbasep) (beltp) (badd) (bmul) (bzero) (bone) (bneg) (brecip)))

;; A simple extension of a field is constructed by the usual process of adjoining a root of an irreducible monic
;; polynomial; a finite extension is a tower of simple extensions.  More precisely,  let F[X] denote the polynomial
;; ring over a field F.  If p(X) an irreducible element of F[X] of degree at least 2, then the simple extension of
;; F determined by p(X) is the quotient ring F[X]/p(X), which may be shown to satisfy the field axioms.  Each
;; element of this field is represented by a unique polynomial in F[X] of degree less than that of p(X).  Note that
;; multiplication of these polynomials is performed modulo p(X).

;; We shall recursively define an extension field, or more simply, a "field", to be either a base field or a simple 
;; extension of a field, where the latter is represented as a cons of which the cdr is the field F being extended 
;; and the car is an irreducible monic polynomial in F[X].  A polynomial in F[X] is represented by a non-null proper 
;; list of elements of F, which are to be thought of as its coefficients.  The degree of a polynomial is 1 less than 
;; its length.  If the degree of a polynomial is non-zero, then its car (i.e., its leading coefficient) is required
;; to be non-zero.

;; Thus, a field is an object of the form (p_n ... p_2 p_1 . b), where b is a base field and each p_k is a
;; polynomial over the field (p_(k-1) ... p_1 . b).

;; Base field of a field:

(defun fbase (f)
  (if (consp f)
      (fbase (cdr f))
    f))

;; Corresponding to each of the functions constrained by the F0 encapsulation, we shall define a function
;; pertaining to extension fields, as listed below.  Note that the final argument of each of the functions
;; to be defined is a field f:

;;   (fp x)      (feltp x f)
;;   (fp+ x y)   (fadd x y f)
;;   (fp* x y)   (fmul x y f)
;;   (f0)        (fzero f)
;;   (f1)        (fone f)
;;   (f- x)      (fneg x f)
;;   (f/ x)      (frecip x f)

;; The above definitions are mutually recursive with functions pertaining to the ring of polynomials over
;; f, which correspond to the functions constrained by the encapsulation of "../linear/ring.lisp", as
;; follows:

;;   (rp x)      (polyp x f)
;;   (rp+ x y)   (padd x y f)
;;   (rp* x y)   (pmul x y f)
;;   (r0)        (pzero f)
;;   (r1)        (pone f)
;;   (r- x)      (neg x f)

;; Along with these, we shall define the polynomial division operator, (pdivide x y f), which returns 2 
;; values: a quotient (pquot x y f) and a remainder (prem x y f) with (degree (prem x y f)) < (degree y).

;; Once these functions are defined, we shall define the predicate (fieldp f).  Our primary objective is
;; to prove by induction that every field satisfies each of the field axioms, e.g.,

;; (defthm fadd-closed
;;   (implies (and (fieldp f) (feltp x f) (feltp y f))
;;            (feltp (fadd x y f) f)))

;; and that the polynomials over a field satisfy each of the ring axioms, e.g.,

;; (defthm padd-closed
;;   (implies (and (fieldp f) (polyp x f) (polyp y f))
;;            (polyp (padd x y f) f)))

;; In the process, we shall derive a variety of other properties of polynomials that are necessary to
;; establish the field axioms.

;; Of course, the raison d'etre of a simple extension of a field f for a polynomial p is the creation of 
;; a field that includes f and contains a root of p.  The notion of a root of a polynomial is beyond the
;; scope of this book but will be addressed in the sequel "galois".


;;----------------------------------------------------------------------------------------------------------
;;                                            Definitions
;;----------------------------------------------------------------------------------------------------------

;; The mutual recursion connecting the functions listed above is quite complex.  For example, the field
;; multiplication operation (fmul x y f) is defined as the remainder (prem (pmul x y f) p (cdr f)), where
;; p = (car f) is the generating polynomial of f.  The division operation pdivide depends on the reciprocal,
;; frecip, which is based on the greatest common divisor of polynomials x and y as follows: The gcd may be
;; expressed as a linear combination of polynomials r * x + s * y.  Since an element x of f is a polynomial
;; of degree less than that of p, the gcd of x and p is 1 and we have r * x + s * p = 1.  Thus, we define 
;; (frecip x f) to be the remainder (prem x p (cdr f)).

;; Note that our informal commentary employs some natural abbreviations, e.g., r * s for (pmul r s f) and
;; 1 for (pone f).

;; A few of the definitions do not require mutual recursion; we list them first.

;; Additive and multiplicative identities of f:

(defund fzero (f)
  (if (consp f)
      (list (fzero (cdr f)))
    (bzero f)))

(defund fone (f)
  (if (consp f)
      (list (fone (cdr f)))
    (bone f)))

;; Additive and multiplicative identities of the polynomial ring over f:

(defund pzero (f)
  (list (fzero f)))

(defund pone (f)
  (list (fone f)))

;; Monic polynomial:

(defund monicp (p f)
  (equal (car p) (fone f)))

;; Constant polynomial:

(defun pconstp (p)
  (not (consp (cdr p))))

;; Degree of a polynomial:

(defun degree (p)
  (1- (len p)))

;; The following function strips leading zeroes of a list of field elements, i.e., converts it to a
;; polynomial, except that it does not alter the zero polynomial (pzero f):
    
(defun pstrip (l f)
  (if (and (consp l) (consp (cdr l)) (equal (car l) (fzero f)))
      (pstrip (cdr l) f)
    l))

;; Append k zeroes to a list of field elements, i.e., multiply a polynomial by X^k:

(defun pshift (p k f)
  (if (zp k)
      p
    (pshift (append p (list (fzero f))) (1- k) f)))

;; The monomial c * X^k:

(defun monomial (c k f)
  (pshift (list c) k f))

;; The remaining functions to be defined form a mutually recursive clique.  Note that the final argument of
;; each of these functions is a field f, and whenever a function calls another function that appears below it,
;; f is replaced by (cdr f).  This observation is critical for the admissibility of the clique.

;; In our treatment of the greatest common divisor, in order to avoid name conflicts (with functions
;; pertaining to the gcd of integers, defined in "../numbers/euclid.lisp"), we use the names pgcd, r$, and s$
;; for the functions described earlier. The recursive Euclidean algorithm produces a polynomial of maximal 
;; degree that divides both of two given polynomials.  It is convenient to define the greatest common divisor 
;; to be monic.  Thus, we first define polynomials (pgcd-aux p q f), (r$-aux p q f), and (s$-aux p q f), 
;; which execute the recursive algorithm, and then divide each of these by the leading coefficient of 
;; (pgcd-aux p q f) to produce (pgcd p q f), (r$ p q f), and (s$ p q f).

;; The reader will notice that several definitions contain "nuisance terms" that are required for
;; admissibility but do not affect the value of the function in any case of interest.  For example, the
;; following term occurs in the definition of pgcd-aux:

;;              (let* ((c (fneg (fmul (car p) (frecip (car q) f) f) f))
;;	               (a (monomial c (- (degree p) (degree q)) f))
;;	               (pnew (padd (pmul a q f) p f)))
;;                (and (< (len pnew) (len p))
;;	               (pgcd-aux pnew q f)))

;; The condition (< (len pnew) (len p)) ensures that the declared measure for this function decreases in
;; the recursive call (pgcd-aux pnew q f).  We shall eventually prove that under suitable constraints on the
;; arguments, the inequality is necessarily satisfied and therefore may be ignored.

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  ;; Recognizer of an element of f, which is a polynomial over (cdr f):
  
  (defund feltp (x f)
    (declare (xargs :measure (list (len f) 0 0)))
    (if (consp f)
        (and (polyp x (cdr f))
             (< (degree x) (degree (car f))))
      (beltp x f)))

  ;; A generalized polynomial is a proper list of field elements:

  (defun feltsp (l f)
    (declare (xargs :measure (list (len f) 1 (len l))))
    (if (consp l)
        (and (feltp (car l) f)
             (feltsp (cdr l) f))
      (null l)))

  ;; A polynomial is a non-nil generalized polynomial with either degree 0 or a non-zero leading coefficient:

  (defund polyp (p f)
    (declare (xargs :measure (list (len f) 2 0)))
    (and (feltsp p f)
         (consp p)
         (or (null (cdr p))
             (not (equal (car p) (fzero f))))))

  ;; Addition of field elements:

  (defund fadd (x y f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (padd x y (cdr f))
      (badd x y f)))

  ;; Additive inverse of a field element:

  (defund fneg (x f)
    (declare (xargs :measure (list (len f) 2 0)))
    (if (consp f)
        (pneg x (cdr f))
      (bneg x f)))

  ;; Additive inverse of a polynomial::

  (defun pneg (x f)
    (declare (xargs :measure (list (len f) 3 (len x))))
    (if (consp x)
        (cons (fneg (car x) f)
              (pneg (cdr x) f))
      ()))

  ;; Addition of generalized polynomials:

  (defun faddl (x y f)
    (declare (xargs :measure (list (len f) 3 (+ (len x) (len y)))))
    (if (> (len x) (len y))
        (cons (car x) (faddl (cdr x) y f))
      (if (> (len y) (len x))
          (cons (car y) (faddl x (cdr y) f))
	(if (consp x)
            (cons (fadd (car x) (car y) f)
                  (faddl (cdr x) (cdr y) f))
          ()))))

   ;; Addition of polynomials:

  (defund padd (p q f)
    (declare (xargs :measure (list (len f) 4 0)))
    (pstrip (faddl p q f) f))

  ;; Multiplication of field elements:

  (defun fmul (x y f)
    (declare (xargs :measure (list (len f) 4 0)))
    (if (consp f)
        (prem (pmul x y (cdr f)) (car f) (cdr f))
      (bmul x y f)))

  ;; Multiplication of a polynomial by a field element:

  (defun cmul (x p f)
    (declare (xargs :measure (list (len f) 5 (len p))))
    (if (equal x (fzero f))
        (list (fzero f))
      (if (consp p)
          (cons (fmul x (car p) f)
	        (cmul x (cdr p) f))
        ())))

  ;; Multiplication of polynomials:

  (defun pmul (p q f)
    (declare (xargs :measure (list (len f) 6 (len p))))
    (if (or (equal p (pzero f)) (equal q (pzero f)))
        (pzero f)
      (if (consp p)
          (if (consp (cdr p))
              (padd (pshift (cmul (car p) q f) (degree p) f)
                    (pmul (pstrip (cdr p) f) q f)
	            f)
	    (cmul (car p) q f))
        ())))

  ;; Reciprocal:

  (defund frecip (x f)
    (declare (xargs :measure (list (len f) 6 0)))
    (if (consp f)
        (prem (r$ x (car f) (cdr f)) (car f) (cdr f))
      (brecip x f)))

  ;; Greatest common divisor:

  (defun pgcd-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        q
      (if (or (equal q (pzero f)) (pconstp p))
          p
        (if (pconstp q)
            q
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (pgcd-aux pnew q f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (pgcd-aux p qnew f))))))))

  (defun r$-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        (pzero f)
      (if (or (equal q (pzero f)) (pconstp p))
          (pone f)
        (if (pconstp q)
            (pzero f)
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (r$-aux pnew q f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (padd (r$-aux p qnew f)
	                 (pneg (pmul a (s$-aux p qnew f) f) f)
		         f))))))))
	            
  (defun s$-aux (p q f)
    (declare (xargs :measure (list (len f) 7 (+ (len p) (len q)))))
    (if (equal p (pzero f))
        (pone f)
      (if (or (equal q (pzero f)) (pconstp p))
          (pzero f)
        (if (pconstp q)
            (pone f)
          (if (>= (degree p) (degree q))
              (let* ((c (fmul (car p) (frecip (car q) f) f))
	             (a (monomial c (- (degree p) (degree q)) f))
	             (pnew (padd p (pneg (pmul a q f) f) f)))
                (and (< (len pnew) (len p))
	             (padd (s$-aux pnew q f)
	                   (pneg (pmul a (r$-aux pnew q f) f) f)
		           f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (s$-aux p qnew f))))))))

  (defund pgcd (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f)))
      (cmul (frecip (car g) f) g f)))

  (defund r$ (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (r (r$-aux p q f)))
      (cmul (frecip (car g) f) r f)))

  (defund s$ (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (s (s$-aux p q f)))
      (cmul (frecip (car g) f) s f)))

  ;; Division of polynomials:

  (defun pdivide (x y f)
    (declare (xargs :measure (list (len f) 7 (len x))))
    (if (pconstp y)
        (mv (cmul (frecip (car y) f) x f) (pzero f))
      (if (< (degree x) (degree y))
          (mv (pzero f) x)
        (let* ((c (fmul (car x) (frecip (car y) f) f))
               (m (monomial c (- (degree x) (degree y)) f))
	       (x1 (padd x (pneg (pmul m y f) f) f)))
	  (if (< (len x1) (len x))
              (mv-let (q r) (pdivide x1 y f)
	        (mv (padd q m f) r))
            (mv () ()))))))

  (defund pquot (x y f)
    (declare (xargs :measure (list (len f) 8 0)))
    (mv-nth 0 (mv-list 2 (pdivide x y f))))

  (defund prem (x y f)
    (declare (xargs :measure (list (len f) 8 0)))
    (mv-nth 1 (mv-list 2 (pdivide x y f))))

))

;; Our formal definition of a field extension depends on the notion of an irreducible polynomial.  We are 
;; unable to formulate an algorithmic definition of irreducibility and therefore resort to defchoose.  First
;; we define polynomial divisibility:

(defund pdivides (q p f)
  (equal (prem p q f) (pzero f)))

;; If p has a non-constant divisor of lesser degree, then it has a monic divisor q of the same lesser degree.  
;; In this case, such a divisor is returned by the following function and p is said to be reducible:

(defchoose pfactor q (p f)
  (and (polyp q f)
       (monicp q f)
       (> (degree q) 0)
       (< (degree q) (degree p))
       (pdivides q p f)))

(defund reduciblep (p f)
  (let ((q (pfactor p f)))
    (and (polyp q f)
         (monicp q f)
         (> (degree q) 0)
         (< (degree q) (degree p))
         (pdivides q p f))))
       
(defund irreduciblep (p f)
  (not (reduciblep p f)))

;; We can now formally define our notion of a field extension:

(defund fieldp (f)
  (if (consp f)
      (and (fieldp (cdr f))
           (polyp (car f) (cdr f))
           (monicp (car f) (cdr f))
	   (irreduciblep (car f) (cdr f))
	   (>= (degree (car f)) 2))
    (fbasep f)))


;;----------------------------------------------------------------------------------------------------------
;;                                            Proof Outline
;;----------------------------------------------------------------------------------------------------------

;; Naturally, the inductive proofs of the axioms are similarly complex.  We shall proceed as follows:

;; (1) In order to enable the induction, we begin by defining a predicate corresponding to each field axiom
;;     that holds iff the field f satisfies the axiom.  These predicates are defined with defun-sk, e.g.,

;;     (defun-sk fadd-closed-p (f)
;;       (forall (x y)
;;         (implies (and (feltp x f) (feltp y f))
;;                  (feltp (fadd x y f) f))))

;;     We define the predicate (field-axioms-p f) to be the conjunction of these predicates.  For each of
;;     the field axioms, we prove a trivial lemma stating, in effect, that the axiom follows from 
;;     (field-axioms-p f), e.g., 

;;     (defthm fadd-closed-*
;;       (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
;;                (feltp (fadd x y f) f))

;;     We also derive some simple consequences of these lemmas, e.g.,

;;     (defthm field-integral-domain-*
;;       (implies (and (field-axioms-p f) (feltp x f) (feltp y f)
;;   		       (equal (fmul x y f) (fzero f)))
;;   	          (or (equal x (fzero f))
;;   	              (equal y (fzero f)))))

;;     These lemmas will form the basis of the proofs in Step 3.

;;     (*) The asterisk suffix is intended to reflect the hypothesis (field-axioms-p f), which will be 
;;     removed in Step 7.

;; (2) We prove that the base fields satisfy the axioms:

;;     (defthmd field-axioms-p-fbasep
;;       (implies (fbasep f) (field-axioms-p f)))

;; (3) We derive the properties of the polynomial ring as consequences of the field axioms.  These 
;;     include the ring axioms, e.g.,

;;     (defthm padd-closed-*
;;       (implies (and (fieldp f) (field-axioms-p f) (polyp x f) (polyp y f))
;;                (polyp (padd x y f))))

;;     along with additional properties that are required for the proofs of Step 4, e.g.,

;;     (defthmd degree-prem-*
;;       (implies (and (fieldp f) (field-axioms-p f)
;;                     (polyp x f) (polyp y f) (>= (degree y) 1))
;;                (and (polyp (prem x y f) f)
;;                     (< (degree (prem x y f))
;;                        (degree y)))))

;;     Again, the hypothesis (field-axioms-p f) will be removed in Step 7.

;; (4) As a consequence of the results of Step 3, we prove that each of the field axioms holds
;;     for an extension field.  These include the ring axioms, e.g.,

;;     (defthmd fadd-closed-**
;;       (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
;;                     (feltp x f) (feltp y f))
;;                (feltp (fadd x y f))))

;;     as well as the 2 axioms pertaining to the reciprocal, e.g.,

;;     (defthmd frecip-closed-**
;;       (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
;;                     (feltp x f))
;;                (feltp (frecip x f) f))

;;     (**) The suffix is intended to reflect the dependence on (field-axioms-p (cdr f)).

;; (5) For each field axiom, we derive a lemma like the following as a trivial consequence of the
;;     corresponding result of Step 4:

;;     (defthmd fadd-closed-step
;;       (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
;;                (fadd-closed-p f)))

;;     Combine these lemmas:

;;     (defthmd field-axioms-p-step
;;       (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
;;                (field-axioms-p f)))

;; (6) We derive the following from the results of Steps 2 and 5 by induction:

;;     (defthmd field-axioms-p-fieldp
;;       (implies (fieldp f) (field-axioms-p f)))

;; (7) We remove the field-axioms-p hypothesis from the "*" lemmas of Steps 1 and 3:

;;     (defthm fadd-closed
;;       (implies (and (feltp x f) (feltp y f))
;;                (feltp (fadd x y f) f))

;;     (defthm padd-closed
;;       (implies (and (fieldp f) (polyp x f) (polyp y f))
;;                (polyp (padd x y f))))

;;     (defthmd degree-prem
;;       (implies (and (fieldp f)
;;                     (polyp x f) (polyp y f) (>= (degree y) 1))
;;                (and (polyp (prem x y f) f)
;;                     (< (degree (prem x y f))
;;                        (degree y)))))


;;----------------------------------------------------------------------------------------------------------
;;                                             Step 1
;;----------------------------------------------------------------------------------------------------------

;; We begin by defining a predicate corresponding to each field axiom that holds iff the field f satisfies
;; the axiom:

;; Closure:

(defun-sk fadd-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fadd x y f) f))))

(defun-sk fmul-closed-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (feltp (fmul x y f) f))))

;; Commutativity:

(defun-sk fadd-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fadd x y f) (fadd y x f)))))

(defun-sk fmul-comm-p (f)
  (forall (x y)
    (implies (and (feltp x f) (feltp y f))
             (equal (fmul x y f) (fmul y x f)))))

;; Associativity:

(defun-sk fadd-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fadd (fadd x y f) z f)
                    (fadd x (fadd y z f) f)))))

(defun-sk fmul-assoc-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul (fmul x y f) z f)
                    (fmul x (fmul y z f) f)))))

;; Identities

(defun feltp-fzero-p (f)
  (feltp (fzero f) f))

(defun feltp-fone-p (f)
  (feltp (fone f) f))

(defun fone-fzero-p (f)
  (not (equal (fzero f) (fone f))))

(defun-sk fzero-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd (fzero f) x f)
                    x))))

(defun-sk fone-id-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fmul (fone f) x f)
                    x))))

;; Inverses:

(defun-sk feltp-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (feltp (fneg x f) f))))

(defun-sk fadd-fneg-p (f)
  (forall (x)
    (implies (feltp x f)
             (equal (fadd x (fneg x f) f)
                    (fzero f)))))

(defun-sk feltp-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (feltp (frecip x f) f))))

(defun-sk fmul-frecip-p (f)
  (forall (x)
    (implies (and (feltp x f) (not (equal x (fzero f))))
             (equal (fmul x (frecip x f) f)
                    (fone f)))))

;; Distributivity:

(defun-sk fdistrib-p (f)
  (forall (x y z)
    (implies (and (feltp x f) (feltp y f) (feltp z f))
             (equal (fmul x (fadd y z f) f)
                    (fadd (fmul x y f) (fmul x z f) f)))))

;; The following lemmas, which are immediate consequences of the above definitions, are used in
;; Steps 2 and 5:

(defthmd fadd-closed-p-witness-lemma
  (mv-let (x y) (fadd-closed-p-witness f)
     (implies (implies (and (feltp x f) (feltp y f))
                       (feltp (fadd x y f) f))
              (fadd-closed-p f))))

(defthmd fmul-closed-p-witness-lemma
  (mv-let (x y) (fmul-closed-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f))
                      (feltp (fmul x y f) f))
             (fmul-closed-p f))))

(defthmd fadd-comm-p-witness-lemma
  (mv-let (x y) (fadd-comm-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f))
                      (equal (fadd x y f) (fadd y x f)))
             (fadd-comm-p f))))

(defthmd fmul-comm-p-witness-lemma
  (mv-let (x y) (fmul-comm-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f))
                      (equal (fmul x y f) (fmul y x f)))
             (fmul-comm-p f))))

(defthmd fadd-assoc-p-witness-lemma
  (mv-let (x y z) (fadd-assoc-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f) (feltp z f))
                      (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f)))
             (fadd-assoc-p f))))

(defthmd fmul-assoc-p-witness-lemma
  (mv-let (x y z) (fmul-assoc-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f) (feltp z f))
                      (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f)))
             (fmul-assoc-p f))))

(defthmd feltp-fzero-p-witness-lemma
  (implies (feltp (fzero f) f)
           (feltp-fzero-p f)))

(defthmd feltp-fone-p-witness-lemma
  (implies (feltp (fone f) f)
           (feltp-fone-p f)))

(defthmd fone-fzero-p-witness-lemma
  (implies (not (equal (fone f) (fzero f)))
           (fone-fzero-p f)))

(defthmd fzero-id-p-witness-lemma
  (let ((x (fzero-id-p-witness f)))
    (implies (implies (feltp x f) (equal (fadd (fzero f) x f) x))
             (fzero-id-p f))))

(defthmd fone-id-p-witness-lemma
  (let ((x (fone-id-p-witness f)))
    (implies (implies (feltp x f) (equal (fmul (fone f) x f) x))
             (fone-id-p f))))

(defthmd feltp-fneg-p-witness-lemma
  (let ((x (feltp-fneg-p-witness f)))
    (implies (implies (feltp x f) (feltp (fneg x f) f))
             (feltp-fneg-p f))))

(defthmd fadd-fneg-p-witness-lemma
  (let ((x (fadd-fneg-p-witness f)))
    (implies (implies (feltp x f) (equal (fadd x (fneg x f) f) (fzero f)))
             (fadd-fneg-p f))))

(defthmd feltp-frecip-p-witness-lemma
  (let ((x (feltp-frecip-p-witness f)))
    (implies (implies (and (feltp x f) (not (equal x (fzero f))))
                      (feltp (frecip x f) f))
             (feltp-frecip-p f))))

(defthmd fmul-frecip-p-witness-lemma
  (let ((x (fmul-frecip-p-witness f)))
    (implies (implies (and (feltp x f) (not (equal x (fzero f))))
                      (equal (fmul x (frecip x f) f) (fone f)))
            (fmul-frecip-p f))))

(defthmd fdistrib-p-witness-lemma
  (mv-let (x y z) (fdistrib-p-witness f)
    (implies (implies (and (feltp x f) (feltp y f) (feltp z f))
                      (equal (fmul x (fadd y z f) f) (fadd (fmul x y f) (fmul x z f) f)))
             (fdistrib-p f))))
                     
;; The conjunction of the above predicates:

(defund field-axioms-p (f)
  (and (fadd-closed-p f)
       (fmul-closed-p f)
       (fadd-comm-p f)
       (fmul-comm-p f)
       (fadd-assoc-p f)
       (fmul-assoc-p f)
       (feltp-fzero-p f)
       (feltp-fone-p f)
       (fone-fzero-p f)
       (fzero-id-p f)
       (fone-id-p f)
       (feltp-fneg-p f)
       (fadd-fneg-p f)
       (feltp-frecip-p f)
       (fmul-frecip-p f)
       (fdistrib-p f)))

;; The following lemmas are immediate consequences of (field-axioms-p f):

(defthm fadd-closed-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (feltp (fadd x y f) f)))

(defthm fmul-closed-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (feltp (fmul x y f) f)))

(defthm fadd-comm-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (equal (fadd x y f) (fadd y x f))))

(defthm fmul-comm-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (equal (fmul x y f) (fmul y x f))))

(defthm fadd-assoc-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f))))

(defthm fmul-assoc-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f))))

(defthm feltp-fzero-*
  (implies (field-axioms-p f)
           (feltp (fzero f) f)))

(defthm feltp-fone-*
  (implies (field-axioms-p f)
           (feltp (fone f) f)))

(defthm fzero-id-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fadd (fzero f) x f) x)))

(defthm fone-id-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fmul (fone f) x f) x)))

(defthm fone-fzero-*
  (implies (field-axioms-p f)
           (not (equal (fzero f) (fone f)))))

(defthm feltp-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (feltp (fneg x f) f)))

(defthm fadd-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fadd x (fneg x f) f)
	          (fzero f))))

(defthm feltp-frecip-*
  (implies (and (field-axioms-p f) (feltp x f) (not (equal x (fzero f))))
           (feltp (frecip x f) f)))

(defthm fmul-frecip-*
  (implies (and (field-axioms-p f) (feltp x f)  (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f)
	          (fone f))))

(defthm fmul-frecip-2-*
  (implies (and (field-axioms-p f) (feltp x f)  (not (equal x (fzero f))))
           (equal (fmul (frecip x f) x f)
	          (fone f))))

(defthm fdistrib-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
                (equal (fmul x (fadd y z f) f)
		       (fadd (fmul x y f) (fmul x z f) f))))

(in-theory (disable fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p fone-fzero-p
                    feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-fneg-p fmul-frecip-p fdistrib-p))

;; Some consequences of the above lemmas:

(defthmd fneg-fzero-*
  (implies (and (field-axioms-p f) (feltp x f))
           (iff (equal (fneg x f) (fzero f))
                (equal x (fzero f)))))

(defthm fzero-id-2-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fadd x (fzero f) f) x)))

(defthmd fneg-unique-*
  (implies (and (field-axioms-p f)
                (feltp x f) (feltp y f) (equal (fadd x y f) (fzero f)))
	   (equal (fneg y f) x)))

(defthm fneg-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fneg (fneg x f) f)
	          x)))

(defthm fone-id-2-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fmul x (fone f) f) x)))

(defthm fmul-fzero-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fmul x (fzero f) f)
	          (fzero f))))

(defthm fmul-fzero-2-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fmul (fzero f) x f)
	          (fzero f))))

(defthm fneg-fmul-*
  (implies (and (field-axioms-p f)
                (feltp x f) (feltp y f))
	   (equal (fneg (fmul x y f) f)
	          (fmul x (fneg y f) f))))

(defthm field-integral-domain-*
  (implies (and (field-axioms-p f)
                (feltp x f)
		(feltp y f)
		(equal (fmul x y f) (fzero f)))
	   (or (equal x (fzero f))
	       (equal y (fzero f))))
  :rule-classes ())

(defthmd frecip-not-fzero-*
  (implies (and (field-axioms-p f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (frecip x f) (fzero f)))))


;;----------------------------------------------------------------------------------------------------------
;;                                                  Step 2
;;----------------------------------------------------------------------------------------------------------

;; We shall prove that the field axioms hold for each base field f.  If f is F0, the required theorems are the 
;; encapsulated theorems in ../linear/field.lisp"; if f is Q, they are built-in properties of rational 
;; arithmetic; and if f is Fp, they all reduce to trivial properties of the function mod, with the exception
;; of the following property of the reciprocal:

;;   (fmul x (recip x f) f) = (fone f).

;; But by Fermat's Theorem (see "../numbers/fermat.lisp"),

;;   (fmul x (recip x f) f) = (mod (* x (mod (expt 2 (- p 2)) p)) p)
;;                          = (mod (expt x (1- p)) p)
;;			    = 1
;;			    = (fone f).

;; Thus, all of the required theorems are easily proved:

;; Closure:

(defthm badd-closed
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (beltp (badd x y f) f)))

(defthm bmul-closed
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (beltp (bmul x y f) f)))


;; Commutativity

(defthmd badd-comm
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (equal (badd x y f) (badd y x f))))

(defthmd bmul-comm
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (equal (bmul x y f) (bmul y x f))))

;; Associativity:

(defthmd badd-assoc
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (badd x (badd y z f) f)
	          (badd (badd x y f) z f))))

(defthmd bmul-assoc
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (bmul x (bmul y z f) f)
	          (bmul (bmul x y f) z f))))

;; Identities:

(defthm beltp-bzero
  (implies (fbasep f)
           (beltp (bzero f) f)))

(defthm beltp-bone
  (implies (fbasep f)
           (beltp (bone f) f)))

(defthm bone-bzero
  (implies (fbasep f)
           (not (equal (bone f) (bzero f)))))

(defthm bzero-id
  (implies (and (fbasep f) (beltp x f))
           (equal (badd (bzero f) x f) x)))

(defthm bzero-id2
  (implies (and (fbasep f) (beltp x f))
           (equal (badd x (bzero f) f) x)))

(defthm bone-id
  (implies (and (fbasep f) (beltp x f))
           (equal (bmul (bone f) x f) x)))

;; Inverses:

(defthm beltp-bneg
  (implies (and (fbasep f) (beltp x f))
           (beltp (bneg x f) f)))

(defthm bneg-bzero
  (implies (fbasep f)
           (equal (bneg (bzero f) f)
	          (bzero f))))

(defthm badd-bneg
  (implies (and (fbasep f) (beltp x f))
           (equal (badd x (bneg x f) f)
	          (bzero f))))

(defthm beltp-brecip
  (implies (and (fbasep f) (beltp x f) (not (equal x (bzero f))))
           (beltp (brecip x f) f)))

(defthm bmul-brecip
  (implies (and (fbasep f) (beltp x f) (not (equal x (bzero f))))
           (equal (bmul x (brecip x f) f)
	          (bone f))))

(defthm bdistrib
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (bmul x (badd y z f) f)
	          (badd (bmul x y f) (bmul x z f) f))))

;; The following are immediate consequences of the above results and the witness lemmas
;; of Step 1:

(defthm badd-closed-step
  (implies (fbasep f)
           (fadd-closed-p f)))

(defthm bmul-closed-step
  (implies (fbasep f)
           (fmul-closed-p f)))

(defthm badd-comm-step
  (implies (fbasep f)
           (fadd-comm-p f)))

(defthm bmul-comm-step
  (implies (fbasep f)
           (fmul-comm-p f)))

(defthm badd-assoc-step
  (implies (fbasep f)
           (fadd-assoc-p f)))

(defthm bmul-assoc-step
  (implies (fbasep f)
           (fmul-assoc-p f)))

(in-theory (disable (fzero) (fone)))

(defthm feltp-bzero-step
  (implies (fbasep f)
           (feltp-fzero-p f)))

(defthm feltp-bone-step
  (implies (fbasep f)
           (feltp-fone-p f)))

(defthm bone-bzero-step
  (implies (fbasep f)
           (fone-fzero-p f)))

(defthm bzero-id-step
  (implies (fbasep f)
           (fzero-id-p f)))

(defthm bone-id-step
  (implies (fbasep f)
           (fone-id-p f)))

(defthm feltp-bneg-step
  (implies (fbasep f)
           (feltp-fneg-p f)))

(defthm feltp-brecip-step
  (implies (fbasep f)
           (feltp-frecip-p f)))

(defthm fadd-bneg-step
  (implies (fbasep f)
           (fadd-fneg-p f)))

(defthm fmul-brecip-step
  (implies (fbasep f)
           (fmul-frecip-p f)))

(defthm bdistrib-step
  (implies (fbasep f)
           (fdistrib-p f)))

;;  Combining these results, we have the desired theorem:

(defthmd field-axioms-p-fbasep
  (implies (fbasep f)
           (field-axioms-p f)))


;;----------------------------------------------------------------------------------------------------------
;;                                           Step 3: Addition
;;----------------------------------------------------------------------------------------------------------

;; In this section, we prove the lemmas of Step 3 pertaining to addition.

;;----------------------
;; Identity
;;----------------------

(defthm feltp-fzero
  (implies (fieldp f)
           (feltp (fzero f) f)))

(defthm polyp-pzero
  (implies (fieldp f)
           (polyp (pzero f) f)))

(defthm pzero-id-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (padd (pzero f) x f)
	          x)))


;;----------------------
;; Inverse
;;----------------------

(defthm len-pneg
  (equal (len (pneg x f))
         (len x)))

(defthm len-fneg
  (implies (consp f)
           (equal (len (fneg x f))
                  (len x))))

(defthm car-pneg
  (implies (consp x)
           (equal (car (pneg x f))
	          (fneg (car x) f))))

(defthm polyp-pneg-*
  (implies (and (fieldp f) (field-axioms-p f) (polyp x f))
           (polyp (pneg x f) f)))

(defthmd padd-pneg-*
  (implies (and (fieldp f) (field-axioms-p f) (polyp x f))
           (equal (padd x (pneg x f) f)
	          (pzero f))))

(defthmd pneg-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pneg (padd x y f) f)
	          (padd (pneg x f) (pneg y f) f))))

(defthmd pneg-unique-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (equal (padd x y f) (pzero f)))
	   (equal (pneg y f) x)))

(defthmd pneg-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pneg (pneg x f) f)
	          x)))

(defthm pneg-pzero-*
  (implies (and (fieldp f) (field-axioms-p f))
           (equal (pneg (pzero f) f) (pzero f))))  

(defthmd pneg-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f)
	        (equal (pneg x f) (pzero f)))
	   (equal (pzero f) x)))

		  
;;----------------------
;; Closure
;;----------------------

(defthm padd-closed-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
           (polyp (padd x y f) f)))


;;----------------------
;; Commutativity
;;----------------------

(defthmd faddl-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (feltsp x f) (feltsp y f))
           (equal (faddl x y f) (faddl y x f))))

(defthmd padd-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
           (equal (padd x y f) (padd y x f))))

;; The following variant of pzero-id is a consequence of padd-comm-*:

(defthm pzero-id-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (padd x (pzero f) f)
	          x)))


;;----------------------
;; Associativity
;;----------------------

;; First we show that if f satisfies the field axioms, then

;;   (pstrip (faddl (pstrip x f) y f) f) = (pstrip (faddl x y f) f).

;; We nmay assume (car x) = (fzero f).  We consider 2 cases:

;; If (len x) <= (len y), then we can prove the stronger result (faddl (pstrip x f) y f) = (fadd x y f):

;; If (len x) < (len y), then

;;    (faddl (pstrip x f) y f) = (cons (car y) (faddl (pstrip x f) (cdr y) f)
;;                             = (cons (car y) (faddl x (cdr y) f)
;;                             = (faddl x y f),

;; and if (len x) = (len y), then

;;    (faddl (pstrip x f) y f) = (cons (car y) (faddl (pstrip x f) (cdr y) f))
;;                             = (cons (car y) (faddl (pstrip (cdr x) f) (cdr y) f))
;;                             = (cons (car y) (faddl (cdr x) (cdr y) f))
;;                             = (cons (fadd (car x) (car y) f) (faddl (cdr x) (cdr y) f))
;;                             = (faddl x y f)

;; Now suppose (len x) > (len y).  Then by induction,

;;    (pstrip (faddl (pstrip x f) y f) f) = (pstrip (faddl (pstrip (cdr x) f) y f) f)
;;                                        = (pstrip (faddl (cdr x) y f) f)
;;                                        = (pstrip (cons (car y) (faddl (cdr x) (cdr y) f)) f)
;;                                        = (pstrip (faddl x y f) f)

(defthmd pstrip-faddl-pstrip
  (implies (and (fieldp f) (field-axioms-p f)
                (feltsp x f) (feltsp y f))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f))))

;; Consequently,

;;   (padd (padd x y f) z f) = (pstrip (faddl (pstrip (faddl x y f) f) z f) f)
;;                           = (pstrip (faddl (faddl x y f) x f) f)

;; and by padd-comm-* and faddl-comm, 

;;   (padd x (padd y z f) f) = (padd (padd y z f) x f)
;;                           = (pstrip (faddl (faddl y z f) x f) f)
;;                           = (pstrip (faddl x (faddl y z f) f) f).

;; Substituting (cdr f) for f, we have

(defthmd fadd-faddl-assoc
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f) (feltp z f)
		(equal (faddl (faddl x y (cdr f)) z (cdr f))
		       (faddl x (faddl y z (cdr f)) (cdr f))))
	   (equal (fadd (fadd x y f) z f)
	          (fadd x (fadd y z f) f))))

;; Thus, it suffices to prove associativity of faddl.  This is easily proved by induction, but the proof
;; involves an inductive hypothisis for every possible ordering of (len x), len y), and (len z):

(defthmd faddl-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (feltsp x f) (feltsp y f) (feltsp z f))
           (equal (faddl (faddl x y f) z f)
                  (faddl x (faddl y z f) f))))

;; Finally, we combine fadd-faddl-assoc and padd-faddl-assoc with faddl-assoc:

(defthmd padd-assoc-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y z f) f)
	          (padd (padd x y f) z f))))


;;-----------------------------------------
;; Degree and Leading Coefficient of a Sum
;;-----------------------------------------

(defthmd degree-padd-bound-*
  (<= (degree (padd x y f))
      (max (degree x) (degree y))))

(defthmd degree-padd-diff-*
  (implies (and (polyp x f) (polyp y f) (not (= (degree x) (degree y))))
           (equal (degree (padd x y f))
	          (max (degree x) (degree y)))))

(defthmd degree-padd-less-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(= (degree x) (degree y)) (posp (degree x))
		(equal (car y) (fneg (car x) f)))
	   (< (degree (padd x y f)) (degree x))))

(defthm car-padd
  (implies (and (fieldp f) (polyp x f) (polyp y f) (< (degree y) (degree x)))
           (equal (car (padd x y f))
	          (car x))))

;;----------------------------------------------------------------------------------------------------------
;;                                          Step 3: Multiplication
;;----------------------------------------------------------------------------------------------------------

;; In this section, we prove the lemmas of Step 3 pertaining to multiplication.

;;----------------------
;; Identity
;;----------------------

(defthm feltp-fone
  (implies (fieldp f)
           (feltp (fone f) f)))

(defthm polyp-pone
  (implies (fieldp f)
           (polyp (pone f) f)))

(defthm pone-pzero
  (implies (fieldp f)
           (not (equal (pone f) (pzero f)))))

(defthm fone-fzero
  (implies (fieldp f)
           (not (equal (fone f) (fzero f)))))

(defthm pone-id-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pmul (pone f) x f)
	          x)))

(defthmd fone-id-1
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
	   (and (< (degree x) (degree (car f)))
	        (equal (fmul (fone f) x f)
	               (prem x (car f) (cdr f))))))


;;-------------------------------------------
;; Multiplication by Constants and Monomials
;;-------------------------------------------

(defthm len-cmul
  (implies (not (equal c (fzero f)))
           (equal (len (cmul c x f))
                  (len x))))

(defthmd cmul-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (not (equal x (pzero f))))
	   (not (equal (cmul c x f) (pzero f)))))

(defthmd polyp-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (let ((p (cmul c x f)))
	     (and (polyp p f)
	          (equal (degree p) (degree x))
		  (equal (car p) (fmul c (car x) f))))))

(defthmd cmul-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f)))
                (polyp x f))
	   (equal (cmul c (cmul d x f) f)
	          (cmul (fmul c d f) x f))))

(defthmd pmul-constant
  (implies (and (polyp x f) (not (consp (cdr x)))
		(polyp y f) (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pmul x y f)
	          (cmul (car x) y f))))

;; A constant polynomial has a reciprocal:

(defund precip (x f)
  (list (frecip (car x) f)))

(defthmd pmul-precip-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (pconstp x) (not (equal x (pzero f))))
           (let ((r (precip x f)))
	     (and (polyp r f)
	          (pconstp r)
		  (not (equal r (pzero f)))
		  (equal (pmul x r f) (pone f))))))

(defthmd cmul-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (polyp y f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (padd x y f) f)
	          (padd (cmul c x f) (cmul c y f) f))))

(defthmd pneg-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (cmul c x f) f)
	          (cmul c (pneg x f) f))))

(defthm degree-monomial
  (implies (natp k)
           (equal (degree (monomial c k f))
	          k)))

(defthm car-monomial
  (equal (car (monomial c k f))
         c))

(defthm polyp-pshift
  (implies (and (fieldp f) (natp k) (polyp x f) (not (equal x (pzero f))))
           (let ((p (pshift x k f)))
             (and (polyp p f)
	          (equal (degree p) (+ k (degree x)))
		  (equal (car p) (car x))))))

(defthmd pshift-nonzero
  (implies (and (polyp x f) (not (equal x (pzero f))) (natp k))
           (not (equal (pshift x k f) (pzero f)))))

(defthm polyp-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (natp k))
           (polyp (monomial c k f) f)))

(defun fzero-list (k f)
  (if (zp k)
      ()
    (cons (fzero f) (fzero-list (1- k) f))))

(defthm cmul-fzero-list
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(natp k))
	   (equal (cmul c (fzero-list k f) f)
	          (fzero-list k f))))

(defthmd cmul-append
  (implies (not (equal c (fzero f)))
           (equal (cmul c (append l m) f)
                  (append (cmul c l f) (cmul c m f)))))

(defthm len-fzero-list
  (implies (natp k)
           (equal (len (fzero-list k f))
	          k)))

(defthm append-fzero-list
  (implies (and (natp k) (natp l))
           (equal (append (fzero-list k f) (fzero-list l f))
	          (fzero-list (+ k l) f))))

(defthm pneg-fzero-list-*
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (equal (pneg (fzero-list k f) f)
	          (fzero-list k f))))

(defthmd pshift-rewrite
  (implies (and (polyp x f) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f)))))

(defthmd pshift-pshift
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (natp k) (natp l))
           (equal (pshift (pshift x k f) l f)
	          (pshift x (+ k l) f))))
		  
(defthmd pstrip-pshift-pstrip
  (implies (and (fieldp f) (feltsp x f) (natp k))
           (equal (pstrip (pshift (pstrip x f) k f) f)
	          (pstrip (pshift x k f) f))))
		  
(defthmd pneg-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (pshift (cmul c x f) k f) f)
	          (pshift (cmul c (pneg x f) f) k f))))

(defthmd padd-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (polyp y f) (natp k))		
	   (equal (padd (pshift x k f) (pshift y k f) f)
	          (if (equal (padd x y f) (pzero f))
		      (pzero f)
		    (pshift (padd x y f) k f)))))

(defthmd cmul-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (natp k)
                (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pshift x k f) f)
	          (pshift (cmul c x f) k f))))

(defthmd monomial-rewrite
  (implies (natp k)
           (equal (monomial c k f)
	          (cons c (fzero-list k f)))))

;; If k > 0, then by monomial-rewrite, the definition of pmul, and pstrip-fzero-list,

;;   (monomial c k f) * y = (cons c (fzero-list k f)) * y
;;                        = (pshift (cmul c y f) k f) + (pstrip (fzero-list k f) f) * y
;;                        = (pshift (cmul c y f) k f) + (pzero f) * y
;;                        = (pshift (cmul c y f) k f).

(defthmd pmul-monomial-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (feltp c f) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c k f) y f)
	          (pshift (cmul c y f) k f))))


;;---------
;; Closure
;;---------

(defthm pmul-closed-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (polyp (pmul x y f) f)))


;;---------------------
;; Degree of Remainder
;;---------------------

;; To prove that (degree (prem x y f)) < (degree y), we must show that the polynomial x1
;; in the definition of pdivision is a polynomial of lesser degree than y.  These lemmas
;; are also used later in deriving the properties of division as well as the greatest common 
;; divisor, which is based on the same construction:

(defthmd polyp-x1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (>= (degree y) 1)
		(polyp x f) (>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (m (monomial c (- (degree x) (degree y)) f))
	          (x1 (padd x (pneg (pmul m y f) f) f)))
	     (and (polyp m f) (polyp x1 f)))))

(defthmd degree-decreasing
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (m (monomial c (- (degree x) (degree y)) f))
                  (x1 (padd x (pneg (pmul m y f) f) f)))
             (< (len x1) (len x)))))

(defthmd degree-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (and (polyp (prem x y f) f)
	        (< (degree (prem x y f))
		   (degree y)))))
	   

;;---------------------------------------------
;; Degree and Leading Coefficient of a Product
;;---------------------------------------------

(defthm pmul-pzero
  (equal (pmul (pzero f) x f)
         (pzero f)))

(defthm pmul-pzero-2
  (equal (pmul x (pzero f) f)
         (pzero f)))

(defthm degree-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
           (equal (degree (pmul x y f))
	          (+ (degree x) (degree y)))))

(defthm pmul-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (not (equal (pmul x y f) (pzero f)))))

(defthmd car-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f))))


;;----------------------
;; Distributivity
;;----------------------

;; Note the following properties of pstrip:

(defthmd len-pstrip
  (<= (len (pstrip x f)) (len x)))

(defthmd polyp-pstrip
  (implies (fieldp f)
           (iff (polyp (pstrip x f) f)
	        (and (feltsp x f) (consp x)))))

(defthmd feltp-pstrip
  (implies (and (fieldp f) (consp f) (feltsp x (cdr f)) (consp x) (< (len x) (len (car f))))
           (feltp (pstrip x (cdr f)) f)))

;; Suppose (consp (cdr x)). Let

;;   x' = (monomial (car x) (degree x) f)

;; and

;; x" = (pstrip (cdr x) f).

(defund head (x f)
  (monomial (car x) (degree x) f))

(defund tail (x f)
  (pstrip (cdr x) f))

(defthm polyp-head
  (implies (and (fieldp f) (polyp x f) (not (equal x (pzero f))))
           (polyp (head x f) f)))

(defthm polyp-tail
  (implies (and (fieldp f) (polyp x f) (consp (cdr x)))
           (polyp (tail x f) f)))

(defthmd len-tail
  (implies (consp x)
           (< (len (tail x f)) (len x))))  

;; We have an alternative expression for x':

(defthmd head-rewrite
  (implies (polyp x f)
           (equal (head x f)
	          (cons (car x) (fzero-list (degree x) f)))))

;; x = x' + x":

(defthmd pdecomp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x)))
	   (equal (padd (head x f) (tail x f) f)
		  x)))

;; By head-rewrite, the definition of pmul, and pstrip-fzero-list,

;;   x' * y = (cons (car x) (fzero-list (degree x) f)) * y
;;          = (pshift (cmul (car x) y f) (degree x) f) + (pstrip (fzero-list (degree x) f) f) * y
;;          = (pshift (cmul (car x) y f) (degree x) f) + (pzero f) * y
;;          = (pshift (cmul (car x) y f) (degree x) f).

(defthmd pmul-head
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (head x f) y f)
	          (pshift (cmul (car x) y f) (degree x) f))))

;; By the definition of pmul,

;;    x * y = x' * y + x" * y:

(defthmd pdistrib-pdecomp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f))
	   (equal (pmul x y f)
	          (padd (pmul (head x f) y f)
			(pmul (tail x f) y f)
			f))))

;; x' * (y + z) = x' * y + x' * z:

(defthmd pmul-head-rewrite
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (head x f) y f)
	          (append (cmul (car x) y f) (fzero-list (degree x) f)))))

(defthmd pdistrib-head
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pmul (head x f) (padd y z f) f))))

;; Thus,

;;     x * (y + z) = x' * (y + z) + x" * (y + z)
;;                 = (x' * y + x' * z) + (x" * y + x" * z)
;; 	 	   = (x' * y + x" * y) + (x' * z + x" * z)
;; 		   = x * y + x * z.

(defthmd pdistrib-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f))))


;;----------------------
;; Commutativity
;;----------------------

;; If x and y are constants, then by pmul-constant,

;;    x * y = (cmul (car x) y f) = (list (fmul (car x) (car y) f)):

(defthmd pmul-constants
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))) (not (consp (cdr y))))
	   (equal (pmul x y f) (list (fmul (car x) (car y) f)))))

(defthmd pmul-constants-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))) (not (consp (cdr y))))
	   (equal (pmul x y f) (pmul y x f))))

;;    (monomial c k f) * x = (pshift (cmul c x f) k) = (append (cmul c x f) (fzero-list k f))

;;    (monomial c k f) * (monomial d l f) = (append (cmul c (monomial d l f) f) (zero-list k f))
;;                                        = (append (cmul c (cons d (zero-list l f)) f) (zero-list k f))
;;                                        = (append (cons (fmul c d f) (cmul c (zero-list l f) f)) (zero-list k f))
;;                                        = (append (cons (fmul c d f) (zero-list l f)) (zero-list k f))
;;                                        = (cons (fmul c d f) (append (zero-list l f) (zero-list k f)))
;;                                        = (cons (fmul c d f) (zero-list (+ l k) f))
;;                                        = (cons (fmul d c f) (zero-list (+ k l) f))
;;                                        = (monomial d l f) * (monomial c k f)

(defthmd pmul-monomials
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (feltp d f) (not (equal d (fzero f)))
		(natp k) (natp l))
	   (equal (pmul (monomial c k f) (monomial d l f) f)
	          (cons (fmul c d f) (fzero-list (+ k l) f)))))

(defthmd pmul-monomials-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (feltp d f) (not (equal d (fzero f)))
		(natp k) (natp l))
	   (equal (pmul (monomial c k f) (monomial d l f) f)
	          (pmul (monomial d l f) (monomial c k f) f))))

;; If x is a constant, then

;;    (monomial c k f) * x = (pshift (cmul c x f) k f)
;;                         = (append (cmul c x f) (fzero-list k f))
;;                         = (append (list (fmul c (car x) f)) (fzero-list k f))
;;                         = (cons (fmul c (car x) f) (fzero-list k f))

;; and

;;    x * (monomial c k f) = (cmul (car x) (monomial c k f) f)
;;                         = (cmul (car x) (cons c (fzero-list k f)) f)
;;                         = (cons (fmul (car x) c f) (cmul c (fzero-list k f) f))
;;                         = (cons (fmul (car x) c f) (fzero-list k f))
;;                         = (pmul (monomial c k f) x f)

(defthmd pmul-constant-monomial-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(feltp c f) (not (equal c (fzero f)))
		(natp k))
	   (equal (pmul x (monomial c k f) f)
	          (pmul (monomial c k f) x f))))

;; We shall repeatedly use the following induction scheme:

(defun tail-induct (x f)
  (declare (xargs :measure (len x) :hints (("Goal" :use (len-tail)))))
  (if (and (consp x) (consp (cdr x)))
      (tail-induct (tail x f) f)
    ()))

;; If x is a constant, then

;;    x * y = x * (y' + y")      [pdecomp]
;;          = x * y' + x * y"    [pdistrib-*]
;;          = y' * x + y" * x    [pmul-constant-monomial-comm, induction]
;;          = y * x              [pdistrib-pdecomp]

(defthmd pmul-constant-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))))
	   (equal (pmul x y f) (pmul y x f))))

;;   x' * y = x' * (y' + y")         [pdecomp]
;;          = x' * y' + x' * y"      [pdistrib]
;;          = y' * x' + y" * x'      [pmul-monomials-comm, induction]
;;          = y * x'                 [pdistrib-pdecomp]

(defthmd pmul-head-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(consp (cdr x)))
	   (equal (pmul (head x f) y f) (pmul y (head x f) f))))

;;   x * y = x * (y' + y")     [pdecomp]
;;         = x * y' + x * y"   [pdistrib]
;;         = y' * x + y" * x   [pmul-head-comm, induction]
;;         = y * x             [pdistrib-pdecomp]

(defthmd pmul-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pmul x y f)
	          (pmul y x f))))

;; Simple consequences of commutatibity:

(defthmd pdistrib-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul (padd y z f) x f)
	          (padd (pmul y x f) (pmul z x f) f))))

(defthm pone-id-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pmul x (pone f) f)
	          x)))


;;----------------------
;; Associativity
;;----------------------

;; First we prove that if c != (fzero f), then

;;    (cmul c (x * y) f) = (pmul (cmul c x f) y f).

;; We may assume y != (pzero f).  If (not (consp (cdr x))), the claim is trivial if x = (pzero f),
;; and otherwise

;;    (cmul c (x * y) f) = (cmul c (cmul (car x) y f) f)
;;                       = (cmul (fmul c (car x) f) y f)
;;			 = (cmul (car (cmul c x f)) y f)
;;			 = (pmul (cmul c x f) y f).

;; We proceed by induction.  If (consp (car x)) and the claim holds with x <- (pstrip (cdr x) f), then

;;    (cmul c (x * y) f) = (cmul c (padd (pshift (cmul (car x) y f) (degree x) f)
;;                                       (pmul (pstrip (cdr x) f) y f))
;;                                       f)
;;                       = (padd (cmul c (pshift (cmul (car x) y f) (degree x) f) f)
;;                               (cmul c (pmul (pstrip (cdr x) f) y f) f)
;;                               f)
;;                       = (padd (pshift (cmul c (cmul (car x) y f) f) (degree x) f)
;;                               (pmul (cmul c (pstrip (cdr x) f) f) y f)
;;                       = (padd (pshift (cmul (fmul c (car x) f) y f) (degree x) f)
;;                               (pmul (cmul c (pstrip (cdr x) f) f) y f)
;;                       = (padd (pshift (cmul (car (cmul c x f)) y f) (degree (cmul c x f)) f)
;;                               (pmul (pstrip (cdr (cmul c x f)) f) y f))
;;                       = (pmul (cmul c x f) y f)

(defthmd cmul-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f))))

;; A special case of cmul-pmul:

(defthmd pmul-const
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f))
	   (equal (pmul (list c) x f)
	          (cmul c x f))))

(defthmd pmul-const-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (pmul (list c) (pmul x y f) f)
	          (pmul (pmul (list c) x f) y f))))

;; Next, we prove that if x != (pzero f) and y != (pzero f), then

;;    (pshift (pmul x y f) k f) = (pmul x (pshift y k f) f).

;; If (not (consp (cdr x))), then

;;    (pshift (pmul x y f) k f) = (pshift (cmul (car x) y f) k f)
;;                              = (cmul (car x) (pshift y k f) f)
;;                              = (pmul x (pshift x y f) f)

;; We proceed by induction.  If (consp (car x)), then

;;    (pmul x y f) = (padd (pshift (cmul (car x) y f) (degree x) f)
;;                         (pmul (pstrip (cdr x) f) y f)
;;                         f)

;; and

;;    (pshift (pshift (cmul (car x) y f) (degree x) f) k f)
;;      = (pshift (cmul (car x) y f) (+ (degree x) k) f)
;;      = (cmul (car x) (pshift y (+ (degree x) k) f) f)
;;      = (cmul (car x) (pshift (pshift y k f) (degree x) f) f)
;;      = (pshift (cmul (car x) (pshift y k f) f) (degree x) f).

;; If (pstrip (cdr x) f) = (pzero f), then

;;    (pshift (pmul x y f) k f) = (pshift (pshift (cmul (car x) y f) (degree x) f) k f)
;;                              = (pshift (cmul (car x) (pshift y k f) f) (degree x) f)
;;				= (pmul x (pshift y k f) f),

;; and if (pstrip (cdr x) f) != (pzero f) and the claim holds with x <- (pstrip (cdr x) f), then

;;    (pshift (pmul x y f) k f) = (pshift (padd (pshift (cmul (car x) y f) (degree x) f)
;;                                              (pmul (pstrip (cdr x) f) y f)
;;                                              f)
;;                                        k f)
;;                              = (padd (pshift (pshift (cmul (car x) y f) (degree x) f) k f)
;;                                      (pshift (pmul (pstrip (cdr x) f) y f) k f)
;;                                      f)
;;                              = (padd (pshift (cmul (car x) (pshift y k f) f) (degree x) f)
;;                                      (pmul (pstrip (cdr x) f) (pshift y k f) f))
;;                              = (pmul x (pshift y k f) f)

(defthmd pshift-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f))))

;; Combine pshift-pmul with pmul-comm-*:

(defthmd pshift-pmul-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul (pshift x k f) y f))))

;; Let c != (fzero f) and m = (monomial c k f) = (pshift (list c) k f).

;;    (pmul (pmul m x f) y f) = (pmul (pmul (pshift (list c) k f) x f) y f)
;;                            = (pmul (pshift (pmul (list c) x f) k f) y f)   [pshift-pmul-comm]
;;                            = (pshift (pmul (pmul (list c) x f) y f) k f)   [pshift-pmul-comm]
;;                            = (pshift (pmul (list c) (pmul x y f) f) k f)   [pmul-const-assoc]
;;                            = (pmul (pshift (list c) k f) (pmul x y f) f)   [pshift-pmul-comm]
;;                            = (pmul m (pmul x y f) f)

(defthmd pmul-monomial-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (let ((m (monomial c k f)))
	     (equal (pmul (pmul m x f) y f)
	            (pmul m (pmul x y f) f)))))

;; If z is a constant, then

;;    (x * y) * z = z * (x * y) = z * (y * x) = (z * y) * x = x * (z * y) = x * (y * z).

;; Assume z is not constant and (x * y) * z" = x * (y * z").  Then

;;    (x * y) * z = (x * y) * (z' + z")
;;                = (x * y) * z' + (x * y) * z"
;;                = x * (y * z') + x * (y * z")
;;                = x * (y * z' + y * z")
;;                = x * (y * (z' + z"))
;;                = x * (y * z)

(defthmd pmul-assoc-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
           (equal (pmul x (pmul y z f) f)
	          (pmul (pmul x y f) z f))))


;;-------------------------------------------------
;; Multiplication by the Negative of a Polynomial
;;------------------------------------------------

(defthmd pmul-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pmul (pneg x f) y f)
	          (pneg (pmul x y f) f))))
  

;;---------------------
;; Polynomial Division
;;---------------------

;; We shall show that values q = (pquot x y f) and r = (prem x y f) computed by (pdivide x y f)
;; satisfy x = y * q + r.  The case of constant y is relatively straightforward:

(defthm pdivision-pconstp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (equal r (pzero f)))))
  :rule-classes ())

;; The non-constant case requires induction and uses the lemma polyp-x1 that was derived in the
;; proof of degree-prem:

(defthm pdivision-not-pconstp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (< (degree r) (degree y)))))
  :rule-classes ())

;; Combine the above result:

(defthm pdivision-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y))))))
  :rule-classes ())

(defthm pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (let ((q (pquot x y f)) (r (prem x y f)))
	     (and (polyp q f) (polyp r f)
	          (equal (padd (pmul y q f) r f) x)
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y)))))))

(defthm pconstp-prem-pzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
           (equal (prem x y f) (pzero f))))

(defthm polyp-pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (and (polyp (pquot x y f) f)
	        (polyp (prem x y f) f))))

;; Let Q and R denote (pquot x y f) and (prem x y f).  Then x = Q * y + R and (degree R) < (degree y).  Suppose we are
;; given polynomials q and R such that x = q * y + r and (degree r) < (degree y).  Since Q * y + R = q * y + r, y * (Q - q)
;; = r - R and the degree of y * (Q - q) is less than (degree y), which implies Q - q = 0, q = Q, and r = R. 

(defthmd pquot-prem-unique-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f))
		(if (pconstp y)
		    (equal r (pzero f))
		  (< (degree r) (degree y))))
           (and (equal (pquot x y f) q)
	        (equal (prem x y f) r))))


;; Some consequences of pquot-prem-unique:

(defthmd prem-padd-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd x (prem y z f) f) z f)
                  (prem (padd x y f) z f))))

(defthmd prem-padd-prem-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd (prem x z f) y f) z f)
                  (prem (padd x y f) z f))))

(defthmd prem-equal-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(< (degree x) (degree y)))
	   (equal (prem x y f)
	          x)))

(defthmd prem+mult-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp a f))
	   (equal (prem (padd (pmul y a f) x f) y f)
	          (prem x y f))))
	          
(defthmd prem-pmul-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul x (prem y z f) f) z f)
	          (prem (pmul x y f) z f))))
			
(defthmd prem-pmul-prem-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul (prem x z f) y f) z f)
	          (prem (pmul x y f) z f))))
			
(defthmd prem-padd-prem-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	  (equal (prem (padd (prem x z f) (prem y z f) f) z f)
	         (padd (prem x z f) (prem y z f) f))))
  
(defthmd prem-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (prem (pneg x f) y f)
	          (pneg (prem x y f) f))))
			
(defthmd pquot-prem-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot (cmul c x f) y f)
	               (cmul c (pquot x y f) f))
		(equal (prem (cmul c x f) y f)
	               (cmul c (prem x y f) f)))))

(defthmd cmul-pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot x (cmul c y f) f)
	               (cmul (frecip c f) (pquot x y f) f))
		(equal (prem x (cmul c y f) f)
		       (prem x y f)))))


;;--------------
;; Divisibility
;;--------------

;; Recall the definition of divisibility:

(defund pdivides (q p f)
  (equal (prem p q f) (pzero f)))

;; Its properties are derived from those of the remainder.

(defthmd cmul-pdivides-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
           (iff (pdivides (cmul c y f) x f)
	        (pdivides y x f))))

(defthmd pconstp-pdivides-*
  (implies (pconstp y)
	   (pdivides y x f)))

(defthm pzero-pdivides-*
  (pdivides (pzero f) x f))

(defthmd pdivides-pzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (pdivides x (pzero f) f)))
	   
(defthmd pdivides-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (iff (pdivides y x f)
	        (pdivides y (cmul c x f) f))))

(defthmd pdivides-pquot-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal x (pzero f)))
		(pdivides x y f))
	   (equal (pmul x (pquot y x f) f)
	          y)))

(defthmd pdivides-self-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (pdivides x x f)))

(defthmd pdivides-multiple-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (pdivides x (pmul x y f) f)))

(defthmd pdivides-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f) (pdivides x z f))
	   (pdivides x (padd y z f) f)))

(defthmd pdivides-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f))
	   (pdivides x (pmul y z f) f)))

(defthmd pdivides-transitive-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal y (pzero f)))
		(pdivides x y f) (pdivides y z f))
	   (pdivides x z f)))

(defthmd pdivides-prem-equal-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (iff (pdivides x (padd y (pneg z f) f) f)
		(equal (prem y x f) (prem z x f)))))
			
(defthmd pdivides-degree-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pdivides x y f) (not (equal y (pzero f))))
	   (<= (degree x) (degree y))))

(defthmd pdivides-equal-degree-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (equal (degree x) (degree y))
		(pdivides x y f))
	   (pdivides y x f)))

(defund make-monic (x f)
  (cmul (frecip (car x) f) x f))

(defthmd monicp-make-monic-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (equal x (pzero f))))
	   (let ((m (make-monic x f)))
	     (and (polyp m f)
	          (monicp m f)
	          (pdivides m x f)
		  (pdivides x m f)
		  (= (degree m) (degree x))))))

(defthmd pdivides-make-monic-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (equal x (pzero f)))
		(polyp y f))
	   (let ((m (make-monic x f)))
	     (and (iff (pdivides m y f) (pdivides x y f))
	          (iff (pdivides y m f) (pdivides y x f))))))

		  
;;-------------------------
;; Greatest Common Divisor
;;-------------------------

;; The essential computation of pgcd and the related functions r$ and s$ is performed by pgcd-aux,
;; r$-aux, and s$-aux, which execute the Euclidean algorithm.  The properties of pgcd are inherited
;; from the auxiliary functions.

(defthmd polyp-pgcd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (polyp (pgcd x y f) f)))

(defthmd pgcd-monic-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (monicp (pgcd x y f) f)))

(defthmd pgcd-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (not (equal (pgcd x y f) (pzero f)))))

(defthmd pgcd-divides-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (pdivides (pgcd x y f) x f)
	        (pdivides (pgcd x y f) y f))))
			
(defthmd divides-pgcd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
                (not (and (equal x (pzero f)) (equal y (pzero f))))
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (pgcd x y f) f)))

(defthmd pgcd-linear-combination-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (let ((r (r$ x y f))
	         (s (s$ x y f)))
	     (and (polyp r f)
	          (polyp s f)
	  	  (equal (padd (pmul r x f) (pmul s y f) f)
		         (pgcd x y f))))))

(defthmd pgcd-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (equal (pgcd x y f) (pgcd y x f))))

;; We can now establish the following properties of irreducuble polynomials:

(defthmd irreduciblep-no-factor-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f)
		(irreduciblep p f)
		(< (degree x) (degree p))
		(pdivides x p f))
	   (pconstp x)))

(defthmd pgcd-irreduciblep-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f)
		(irreduciblep p f) (not (pdivides p x f)))
	   (equal (pgcd p x f) (pone f))))

(defthmd peuclid-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f) (polyp y f)
		(irreduciblep p f) (pdivides p (pmul x y f) f))
	   (or (pdivides p x f) (pdivides p y f))))


;;----------------------------------------------------------------------------------------------------------
;;                                                Step 4
;;----------------------------------------------------------------------------------------------------------

;; Most of the required properties of the field operations follow easily from the corresponding properties 
;; of  polynomials.  The exceptions are the final 2 lemmas below pertaining to the reciprocal, which depend
;; on the properties of the greatest common divisor and irreducibility.

(defthm fzero-id-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
           (equal (fadd (fzero f) x f)
	          x)))

(defthm fone-id-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
           (equal (fmul (fone f) x f) x)))

(defthm fadd-closed-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (feltp (fadd x y f) f)))

(defthm feltp-fneg-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)) (feltp x f))
           (feltp (fneg x f) f)))

(defthm fadd-fneg-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)) (feltp x f))
           (equal (fadd x (fneg x f) f)
	          (fzero f))))

(defthmd fadd-comm-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (equal (fadd x y f) (fadd y x f))))

(defthmd fadd-assoc-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd x (fadd y z f) f)
	          (fadd (fadd x y f) z f))))

(defthm fmul-closed-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (feltp (fmul x y f) f)))

(defthmd fdistrib-**
   (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                 (feltp x f) (feltp y f) (feltp z f))
            (equal (fmul x (fadd y z f) f)
                   (fadd (fmul x y f) (fmul x z f) f))))

 (defthmd fmul-comm-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
           (feltp x f) (feltp y f))
           (equal (fmul x y f) (fmul y x f))))

(defthmd fmul-assoc-**
   (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                 (feltp x f) (feltp y f) (feltp z f))
            (equal (fmul x (fmul y z f) f)
                   (fmul (fmul x y f) z f))))

(defthmd feltp-frecip-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (feltp (frecip x f) f)))

(defthmd fmul-frecip-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f)
	          (fone f))))


;;----------------------------------------------------------------------------------------------------------
;;                                               Step 5
;;----------------------------------------------------------------------------------------------------------

;; Each of these is a trivial consequence of the corresponding result of Step 4:

(defthm fadd-closed-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
           (fadd-closed-p f)))

(defthm fmul-closed-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-closed-p f)))

(defthm fadd-comm-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-comm-p f)))

(defthm fmul-comm-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-comm-p f)))

(defthm fadd-assoc-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-assoc-p f)))

(defthm fmul-assoc-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-assoc-p f)))

(defthm feltp-fzero-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fzero-p f)))

(defthm feltp-fone-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fone-p f)))

(defthm fzero-id-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fzero-id-p f)))

(defthm fone-id-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fone-id-p f)))

(defthm fone-fzero-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fone-fzero-p f)))

(defthm feltp-fneg-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fneg-p f)))

(defthm fadd-fneg-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-fneg-p f)))

(defthm feltp-frecip-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-frecip-p f)))

(defthm fmul-frecip-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-frecip-p f)))

(defthm fdistrib-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fdistrib-p f)))

;; Combine the above results:
						  
(defthmd field-axioms-p-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
           (field-axioms-p f)))


;;----------------------------------------------------------------------------------------------------------
;;                                               Step 6
;;----------------------------------------------------------------------------------------------------------

;; An immediate consequence of Steps 2 and 5 by induction:

(defthm field-axioms-p-fieldp
  (implies (fieldp f) (field-axioms-p f)))
                  

;;----------------------------------------------------------------------------------------------------------
;;                                               Step 7
;;----------------------------------------------------------------------------------------------------------

;; The desired results follow immediately from Step 6 and the starred lemmas of Steps 1 and 3.

;;--------------
;; Field axioms
;;--------------

(defthm fadd-closed
  (implies (and (fieldp f) (feltp x f) (feltp y f))
           (feltp (fadd x y f) f)))

(defthm fmul-closed
  (implies (and (fieldp f) (feltp x f) (feltp y f))
	   (feltp (fmul x y f) f)))

(defthm fadd-comm
  (implies (and (fieldp f) (feltp x f) (feltp y f))
	   (equal (fadd x y f) (fadd y x f))))

(defthm fmul-comm
  (implies (and (fieldp f) (feltp x f) (feltp y f))
	   (equal (fmul x y f) (fmul y x f))))

(defthmd fadd-assoc
  (implies (and (fieldp f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f))))

(defthmd fmul-assoc
  (implies (and (fieldp f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f))))

(defthm feltp-fzero
  (implies (fieldp f)
           (feltp (fzero f) f)))

(defthm feltp-fone
  (implies (fieldp f)
           (feltp (fone f) f)))

(defthm fzero-id
  (implies (and (fieldp f) (feltp x f))
	   (equal (fadd (fzero f) x f) x)))

(defthm fone-id
  (implies (and (fieldp f) (feltp x f))
	   (equal (fmul (fone f) x f) x)))

(defthmd fone-fzero
  (implies (fieldp f)
           (not (equal (fone f) (fzero f)))))

(defthm feltp-fneg
  (implies (and (fieldp f) (feltp x f))
           (feltp (fneg x f) f)))

(defthm fadd-fneg
  (implies (and (fieldp f) (feltp x f))
           (equal (fadd x (fneg x f) f)
	          (fzero f))))

(defthm feltp-frecip
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))))
           (feltp (frecip x f) f)))

(defthm fmul-frecip
  (implies (and (fieldp f) (feltp x f)  (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f)
	          (fone f))))

(defthmd fdistrib
  (implies (and (fieldp f) (feltp x f) (feltp y f) (feltp z f))
                (equal (fmul x (fadd y z f) f)
		       (fadd (fmul x y f) (fmul x z f) f))))

(defthmd fdistrib-comm
  (implies (and (fieldp f) (feltp x f) (feltp y f) (feltp z f))
           (equal (fmul (fadd y z f) x f)
                  (fadd (fmul y x f) (fmul z x f) f))))

;;---------------------------------
;; Additional properties of fields
;;---------------------------------

(defthmd fneg-fzero
  (implies (and (fieldp f) (feltp x f))
           (iff (equal (fneg x f) (fzero f))
                (equal x (fzero f)))))

(defthm fzero-id-2
  (implies (and (fieldp f) (feltp x f))
	   (equal (fadd x (fzero f) f) x)))

(defthmd fneg-unique
  (implies (and (fieldp f)
                (feltp x f) (feltp y f) (equal (fadd x y f) (fzero f)))
	   (equal (fneg y f) x)))

(defthm fneg-fneg
  (implies (and (fieldp f) (feltp x f))
           (equal (fneg (fneg x f) f)
	          x)))

(defthm fone-id-2
  (implies (and (fieldp f) (feltp x f))
	   (equal (fmul x (fone f) f) x)))

(defthm fmul-frecip-2
  (implies (and (fieldp f) (feltp x f)  (not (equal x (fzero f))))
           (equal (fmul (frecip x f) x f)
	          (fone f))))

(defthm fmul-fzero
  (implies (and (fieldp f) (feltp x f))
           (equal (fmul x (fzero f) f)
	          (fzero f))))

(defthm fmul-fzero-2
  (implies (and (fieldp f) (feltp x f))
           (equal (fmul (fzero f) x f)
	          (fzero f))))

(defthmd fneg-fmul
  (implies (and (fieldp f)
                (feltp x f) (feltp y f))
	   (equal (fneg (fmul x y f) f)
	          (fmul x (fneg y f) f))))

(defthm field-integral-domain
  (implies (and (fieldp f)
                (feltp x f)
		(feltp y f)
		(equal (fmul x y f) (fzero f)))
	   (or (equal x (fzero f))
	       (equal y (fzero f))))
  :rule-classes ())

(defthmd frecip-not-fzero
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (frecip x f) (fzero f)))))

(defthmd frecip-unique
  (implies (and (fieldp f) (feltp x f) (feltp y f)
                (equal (fmul x y f) (fone f)))
	   (equal (frecip y f) x)))
	   
;;------------------------
;; Polynomial ring axioms
;;------------------------

(defthm polyp-pzero
  (implies (fieldp f)
           (polyp (pzero f) f)))

(defthm polyp-pone
  (implies (fieldp f)
           (polyp (pone f) f)))

(defthm pzero-id
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (padd (pzero f) x f)
	          x)))

(defthm pone-id
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (pmul (pone f) x f)
	          x)))

(defthm pone-pzero
  (implies (fieldp f)
           (not (equal (pone f) (pzero f)))))

(defthm polyp-pneg
  (implies (and (fieldp f)  (polyp x f))
           (polyp (pneg x f) f)))

(defthmd padd-pneg
  (implies (and (fieldp f)  (polyp x f))
           (equal (padd x (pneg x f) f)
	          (pzero f))))

(defthm padd-closed
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
           (polyp (padd x y f) f)))

(defthmd padd-comm
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
           (equal (padd x y f) (padd y x f))))

(defthmd padd-assoc
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y z f) f)
	          (padd (padd x y f) z f))))

(defthm pmul-closed
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (polyp (pmul x y f) f)))

(defthmd pmul-comm
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (equal (pmul x y f)
	          (pmul y x f)))
  :hints (("Goal" :use (pmul-comm-*))))

(defthmd pmul-assoc
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f))
           (equal (pmul x (pmul y z f) f)
	          (pmul (pmul x y f) z f))))

(defthmd pdistrib
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f))))

;;-------------------------------------------
;; Additional properties of polynomial rings
;;-------------------------------------------

(defthm pzero-id-2
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (padd x (pzero f) f)
	          x)))

(defthm pone-id-2
  (implies (and (fieldp f)
                (polyp x f))
	   (equal (pmul x (pone f) f)
	          x)))

(defthm degree-pone
  (implies (fieldp f)
           (equal (degree (pone f)) 0)))

(defthmd pneg-unique
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (equal (padd x y f) (pzero f)))
	   (equal (pneg y f) x)))

(defthmd pneg-pneg
  (implies (and (fieldp f)
                (polyp x f))
	   (equal (pneg (pneg x f) f)
	          x)))

(defthm car-pneg
  (implies (consp x)
           (equal (car (pneg x f))
	          (fneg (car x) f))))

(defthm pneg-pzero
  (implies (and (fieldp f))
           (equal (pneg (pzero f) f) (pzero f))))

(defthmd pneg-nonzero
  (implies (and (fieldp f)
                (polyp x f)
	        (equal (pneg x f) (pzero f)))
	   (equal (pzero f) x)))

(defthmd pneg-padd
  (implies (and (fieldp f)
                (polyp x f) (polyp y f))
	   (equal (pneg (padd x y f) f)
	          (padd (pneg x f) (pneg y f) f))))

(defthmd pmul-pneg
  (implies (and (fieldp f)
                (polyp x f) (polyp y f))
	   (equal (pmul (pneg x f) y f)
	          (pneg (pmul x y f) f))))

(defthmd pdistrib-2
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul (padd y z f) x f)
	          (padd (pmul y x f) (pmul z x f) f))))

(defthmd degree-padd-bound
  (<= (degree (padd x y f))
      (max (degree x) (degree y))))

(defthmd degree-padd-diff
  (implies (and (polyp x f) (polyp y f) (not (= (degree x) (degree y))))
           (equal (degree (padd x y f))
	          (max (degree x) (degree y)))))

(defthmd degree-padd-less
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
		(= (degree x) (degree y)) (posp (degree x))
		(equal (car y) (fneg (car x) f)))
	   (< (degree (padd x y f)) (degree x))))

(defthm degree-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
           (equal (degree (pmul x y f))
	          (+ (degree x) (degree y)))))

(defthm pmul-nonzero
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (not (equal (pmul x y f) (pzero f)))))

(defthm pmul-cancel
  (implies (and (fieldp f) (polyp x f) (polyp y f) (polyp z f)
                (not (equal x (pzero f)))
		(equal (pmul x y f) (pmul x z f)))
	   (equal y z))
  :rule-classes ())

(defthmd car-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f))))

(defthmd degree-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (and (polyp (prem x y f) f)
	        (< (degree (prem x y f))
		   (degree y)))))

(defund precip (x f)
  (list (frecip (car x) f)))

(defthmd pmul-precip
  (implies (and (fieldp f)
                (polyp x f) (pconstp x) (not (equal x (pzero f))))
           (let ((r (precip x f)))
	     (and (polyp r f)
	          (pconstp r)
		  (not (equal r (pzero f)))
		  (equal (pmul x r f) (pone f))))))

;;-------------------------------------------
;; Multiplication by constants and monomials
;;-------------------------------------------

(defthm len-cmul
  (implies (not (equal c (fzero f)))
           (equal (len (cmul c x f))
                  (len x))))

(defthmd cmul-nonzero
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (not (equal x (pzero f))))
	   (not (equal (cmul c x f) (pzero f)))))

(defthmd polyp-cmul
  (implies (and (fieldp f) 
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (let ((p (cmul c x f)))
	     (and (polyp p f)
	          (equal (degree p) (degree x))
		  (equal (car p) (fmul c (car x) f))))))

(defthmd cmul-pzero
  (implies (and (fieldp f) (feltp c f))
           (equal (cmul c (pzero f) f)
	          (pzero f))))

(defthmd cmul-fzero
  (equal (cmul (fzero f) x f)
         (pzero f)))

(defthmd cmul-fadd
  (implies (and (fieldp f) (feltp c f) (feltp d f) (polyp x f))
           (equal (cmul (fadd c d f) x f)
	          (padd (cmul c x f) (cmul d x f) f))))

(defthmd cmul-cmul
  (implies (and (fieldp f)
                (feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f)))
                (polyp x f))
	   (equal (cmul c (cmul d x f) f)
	          (cmul (fmul c d f) x f))))

(defthmd cmul-append
  (implies (not (equal c (fzero f)))
           (equal (cmul c (append l m) f)
                  (append (cmul c l f) (cmul c m f)))))

(defthmd pneg-cmul
  (implies (and (fieldp f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (cmul c x f) f)
	          (cmul c (pneg x f) f))))

(defthmd cmul-pmul
  (implies (and (fieldp f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f))))

(defthmd pmul-constant
  (implies (and (polyp x f) (not (consp (cdr x)))
		(polyp y f) (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pmul x y f)
	          (cmul (car x) y f))))

(defthmd cmul-padd
  (implies (and (fieldp f)
		(polyp x f) (polyp y f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (padd x y f) f)
	          (padd (cmul c x f) (cmul c y f) f))))

(defun fzero-list (k f)
  (if (zp k)
      ()
    (cons (fzero f) (fzero-list (1- k) f))))

(defthm pneg-fzero-list
  (implies (and (fieldp f) (natp k))
           (equal (pneg (fzero-list k f) f)
	          (fzero-list k f))))

(defthmd pshift-rewrite
  (implies (and (polyp x f) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f)))))

(defthmd pneg-pshift
  (implies (and (fieldp f)
                (natp k) (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (pshift (cmul c x f) k f) f)
	          (pshift (cmul c (pneg x f) f) k f))))

(defthmd cmul-pshift
  (implies (and (fieldp f)
                (polyp x f) (natp k)
                (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pshift x k f) f)
	          (pshift (cmul c x f) k f))))

(defthm polyp-pshift
  (implies (and (fieldp f) (natp k) (polyp x f) (not (equal x (pzero f))))
           (let ((p (pshift x k f)))
             (and (polyp p f)
	          (equal (degree p) (+ k (degree x)))
		  (equal (car p) (car x))))))

(defthmd pshift-pshift
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (natp k) (natp l))
           (equal (pshift (pshift x k f) l f)
	          (pshift x (+ k l) f))))
		  
(defthmd pstrip-pshift-pstrip
  (implies (and (fieldp f) (feltsp x f) (natp k))
           (equal (pstrip (pshift (pstrip x f) k f) f)
	          (pstrip (pshift x k f) f))))

(defthmd padd-pshift
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (polyp y f) (natp k))		
	   (equal (padd (pshift x k f) (pshift y k f) f)
	          (if (equal (padd x y f) (pzero f))
		      (pzero f)
		    (pshift (padd x y f) k f)))))

(defthmd pshift-pmul
  (implies (and (fieldp f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f))))

(defthm polyp-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (natp k))
           (polyp (monomial c k f) f)))

(defthm degree-monomial
  (implies (natp k)
           (equal (degree (monomial c k f))
	          k)))

(defthm car-monomial
  (equal (car (monomial c k f))
         c))

(defthmd monomial-rewrite
  (implies (natp k)
           (equal (monomial c k f)
	          (cons c (fzero-list k f)))))

(defthmd pmul-monomial
  (implies (and (fieldp f) 
                (natp k) (feltp c f) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c k f) y f)
	          (pshift (cmul c y f) k f))))

;;---------------------
;; Polynomial division
;;---------------------

(defthm pdivision
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (< (degree r) (degree y)))))
  :rule-classes ())

(defthm pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (let ((q (pquot x y f)) (r (prem x y f)))
	     (and (polyp q f) (polyp r f)
	          (equal (padd (pmul y q f) r f) x)
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y)))))))

(defthm polyp-pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (and (polyp (pquot x y f) f)
	        (polyp (prem x y f) f))))

(defthm pconstp-prem-pzero
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
           (equal (prem x y f) (pzero f))))

(defthmd prem-padd-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd x (prem y z f) f) z f)
                  (prem (padd x y f) z f))))

(defthmd prem-padd-prem-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd (prem x z f) y f) z f)
                  (prem (padd x y f) z f))))

(defthmd prem-pmul-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul x (prem y z f) f) z f)
	          (prem (pmul x y f) z f))))
			
(defthmd prem-pmul-prem-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul (prem x z f) y f) z f)
	          (prem (pmul x y f) z f))))
			
(defthmd pquot-prem-unique
 (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f))
		(if (pconstp y)
		    (equal r (pzero f))
		  (< (degree r) (degree y))))
           (and (equal (pquot x y f) q)
	        (equal (prem x y f) r))))

(defthmd prem-equal
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(< (degree x) (degree y)))
	   (equal (prem x y f)
	          x)))

(defthmd prem-self
  (implies (and (fieldp f) (polyp x f) (not (equal x (pzero f))))
           (equal (prem x x f) (pzero f))))

(defthmd prem+mult
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp a f))
	   (equal (prem (padd (pmul y a f) x f) y f)
	          (prem x y f))))

(defthmd prem-padd-prem-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	  (equal (prem (padd (prem x z f) (prem y z f) f) z f)
	         (padd (prem x z f) (prem y z f) f))))

(defthmd padd-prem-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	  (equal (padd (prem x z f) (prem y z f) f)
	         (prem (padd x y f) z f))))

(defthmd prem-pneg
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (prem (pneg x f) y f)
	          (pneg (prem x y f) f))))

(defthmd cmul-pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot x (cmul c y f) f)
	               (cmul (frecip c f) (pquot x y f) f))
		(equal (prem x (cmul c y f) f)
		       (prem x y f)))))

(defthmd pquot-prem-cmul
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot (cmul c x f) y f)
	               (cmul c (pquot x y f) f))
		(equal (prem (cmul c x f) y f)
	               (cmul c (prem x y f) f)))))

;;--------------
;; Divisibility
;;--------------

(defthmd pdivides-cmul
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (iff (pdivides y x f)
	        (pdivides y (cmul c x f) f))))

(defthmd cmul-pdivides
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
           (iff (pdivides (cmul c y f) x f)
	        (pdivides y x f))))

(defthmd pconstp-pdivides
  (implies (pconstp y)
	   (pdivides y x f)))

(defthmd pdivides-pzero
  (implies (and (fieldp f) 
                (polyp x f))
	   (pdivides x (pzero f) f)))

(defthmd pdivides-equal-degree
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (equal (degree x) (degree y))
		(pdivides x y f))
	   (pdivides y x f)))

(defthm pzero-pdivides
  (pdivides (pzero f) x f))

(defthmd pdivides-pquot
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (not (equal x (pzero f)))
		(pdivides x y f))
	   (equal (pmul x (pquot y x f) f)
	          y)))

(defthmd pdivides-self
  (implies (and (fieldp f) 
                (polyp x f))
	   (pdivides x x f)))

(defthmd pdivides-multiple
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (pdivides x (pmul x y f) f)))

(defthmd pdivides-padd
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f) (pdivides x z f))
	   (pdivides x (padd y z f) f)))

(defthmd pdivides-padd-converse
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x z f)
	        (pdivides x (padd y z f) f))
	   (pdivides x y f)))

(defthmd pdivides-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f))
	   (pdivides x (pmul y z f) f)))

(defthmd product-pdivides
  (implies (and (fieldp f) (polyp x f) (polyp y f) (polyp z f)
                (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (iff (pdivides (pmul x y f) z f)
	        (and (pdivides x z f)
		     (pdivides y (pquot z x f) f)))))

(defthmd pdivides-transitive
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal y (pzero f)))
		(pdivides x y f) (pdivides y z f))
	   (pdivides x z f)))

(defthmd pdivides-prem-equal
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (iff (pdivides x (padd y (pneg z f) f) f)
		(equal (prem y x f) (prem z x f)))))

(defthmd pdivides-degree
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (pdivides x y f) (not (equal y (pzero f))))
	   (<= (degree x) (degree y))))

(defthm pdivides-monic-equal
  (implies (and (fieldp f)
                (polyp x f) (monicp x f)
                (polyp y f) (monicp y f)
                (pdivides x y f) (pdivides y x f))
	   (equal x y))
  :rule-classes ())

(defund make-monic (x f)
  (cmul (frecip (car x) f) x f))

(defthmd monicp-make-monic
  (implies (and (fieldp f)
                (polyp x f) (not (equal x (pzero f))))
	   (let ((m (make-monic x f)))
	     (and (polyp m f)
	          (monicp m f)
	          (pdivides m x f)
		  (pdivides x m f)
		  (= (degree m) (degree x))))))

(defthmd pdivides-make-monic
  (implies (and (fieldp f)
                (polyp x f) (not (equal x (pzero f)))
		(polyp y f))
	   (let ((m (make-monic x f)))
	     (and (iff (pdivides m y f) (pdivides x y f))
	          (iff (pdivides y m f) (pdivides y x f))))))

;;-------------------------
;; Greatest common divisor
;;-------------------------

(defthmd polyp-pgcd
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (polyp (pgcd x y f) f)))

(defthmd pgcd-monic
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))) (not (equal y (pzero f))))
           (monicp (pgcd x y f) f)))

(defthmd pgcd-pzero
  (equal (pgcd (pzero f) p f)
         (make-monic p f)))

(defthmd pgcd-nonzero
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (not (equal (pgcd x y f) (pzero f)))))

(defthmd pgcd-divides
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (pdivides (pgcd x y f) x f)
	        (pdivides (pgcd x y f) y f))))

(defthmd divides-pgcd
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
                (not (and (equal x (pzero f)) (equal y (pzero f))))
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (pgcd x y f) f)))

(defthmd pgcd-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (equal (pgcd x y f) (pgcd y x f))))

(defthmd pgcd-linear-combination
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (let ((r (r$ x y f))
	         (s (s$ x y f)))
	     (and (polyp r f)
	          (polyp s f)
	  	  (equal (padd (pmul r x f) (pmul s y f) f)
		         (pgcd x y f))))))

;;-------------------------
;; Irreducible polynomials
;;-------------------------

(defthmd irreduciblep-no-factor
  (implies (and (fieldp f)
                (polyp p f) (polyp x f)
		(irreduciblep p f)
		(< (degree x) (degree p))
		(pdivides x p f))
	   (pconstp x)))

(defthm irreduciblep-pdivides-monic-equal
  (implies (and (fieldp f)
                (polyp x f) (monicp x f) (>= (degree x) 1)
                (polyp y f) (monicp y f) (irreduciblep y f)
                (pdivides x y f))
	   (equal x y))
  :rule-classes ())

(defthmd peuclid
  (implies (and (fieldp f) 
                (polyp p f) (polyp x f) (polyp y f)
		(irreduciblep p f))
	   (iff (pdivides p (pmul x y f) f)
	        (or (pdivides p x f) (pdivides p y f)))))

(defthmd pgcd-irreduciblep
  (implies (and (fieldp f) 
                (polyp p f) (polyp x f)
		(irreduciblep p f) (not (pdivides p x f)))
	   (equal (pgcd p x f) (pone f))))

(defthm irreduciblep-car-field
  (implies (and (fieldp f) (consp f))
           (and (polyp (car f) (cdr f))
	        (not (pconstp (car f)))
		(not (equal (car f) (pzero (cdr f))))
		(irreduciblep (car f) (cdr f)))))

(defthmd degree-car-field
  (implies (and (fieldp f) (consp f))
           (>= (degree (car f)) 2)))

;; Every non-constant polynomial has a non-constant irreducible factor, which may be
;; defined as follows:

(defun irred-factor (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :in-theory (enable reduciblep)))))
  (if (and (fieldp f) (polyp p f) (>= (degree p) 1) (reduciblep p f))
      (irred-factor (pfactor p f) f)
    p))

(defthmd irreduciblep-irred-factor
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1))
           (let ((q (irred-factor p f)))
	     (and (polyp q f)
	          (>= (degree q) 1)
	          (irreduciblep q f)
		  (pdivides q p f)))))

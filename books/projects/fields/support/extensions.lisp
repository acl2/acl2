;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")
(include-book "rtl/rel11/lib/top" :dir :system)
(include-book "projects/groups/groups" :dir :system)
(include-book "projects/linear/field" :dir :system)
(include-book "projects/numbers/fermat" :dir :system)

;; A field may be represented in ACL2 as a set of 7 functions that satisfy the field axioms: a predicate
;; that recognizes field elements, 2 binary operations, 2 0-ary identity elements, and 2 unary inverse
;; operators.  An example of a field is the generic field specified by the encapsulation in the file
;; "../linear/field.lisp".

;; We would like to be able to say "Let f be a field" in the ACL2 logic, that is, we would like to
;; define an ACL2 predicate fieldp that recognizes fields, but in general, fields are not ACL2 objects.
;; We can, however, define as ACL2 objects a certain class of fields that is sufficiently general to 
;; allow us to some interesting things

;; We are interested in field extensions: algebraic number fields, which are finite extensions of the 
;; rationals, and finite fields, which are finite extensions of prime fields.  We shall also consider 
;; finite extensions of the generic field mentioned above, because any results pertaining to such an 
;; extension may be applied, by function instantiation, to an extension of any field.  We shall informally 
;; refer to the rational field as Q and to the prime field of order p as Fp.  We have previously referred 
;; to the generic field as F, but henceforth we shall refer to it as F0 so that we may refer to an 
;; arbitrary field as F.  All of these fields are called "base fields" and are encoded as follows:

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

;; A primitive extension of a field is constructed by the usual process of adjoining a root of an
;; irreducible monic polynomial; a finite extension is a tower of primitive extensions.  More precisely,
;; let F[X] denote the polynomial ring over a field F.  If p(X) an irreducible element of F[X] of degree
;; at least 2, then the primitive extension of F determined by p(X) is the quotient ring F[X]/p(X),
;; which may be shown to be a field.  Each element of this field is represented by a unique polynomial
;; in F[X] of degree less than that of p(X); multiplication of these polynomials is performed modulo p(X).

;; We shall recursively define a "field" to be either a base field or a primitive extension of a field,
;; where the latter is represented as a cons of which the cdr is the field F being extended and the car is
;; an irreducible monic polynomial in F[X].  A polynomial in F[X] is represented by a non-null proper list
;; of elements of F, which are to be thought of as its coefficients.  The degree of a polynomial is 1 less
;; than its length.  If the degree of a polynomial is non-zero, then its car (i.e., its leading coefficient)
;; is required to be non-zero.

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

;; The above definitions are mutually recursive with functions pertaining the ring of polynomials over
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

;; Once these functions are defined, we shall define the predicate (fieldp f).  Our ultimate objective is
;; to prove that every field satisfies each of the field axioms, e.g.,

;; (defthm fadd-closed
;;   (implies (and (fieldp f) (feltp x f) (feltp y f))
;;            (feltp (fadd x y f) f)))

;; and that the polynomials over a field satisfy each of the ring axioms, e.g.,

;; (defthm padd-closed
;;   (implies (and (fieldp f) (polyp x f) (polyp y f))
;;            (polyp (padd x y f) f)))

;; as well as other properties.

;; The mutual recursion connecting these functions is quite complex.  For example, the field multiplication
;; operation (fmul x y f) is defined as the remainder (prem (pmul x y f) p (cdr f)), where p = (car f) is
;; the generating polynomial of f.  The division operation pdivide depends on the reciprocal, frecip, which
;; is based on the greatest common divisor of poynomials x and y as follows: The gcd may be expressed as a 
;; linear combination of polynomials rx + sy.  Since an element x of f is a polynomial of degree less than 
;; that of p, the gcd of x and p is 1 and we have rx + sp = 1.  Thus, we define (frecip x f), to be the
;; remainder (prem x p (cdr f)).


;;----------------------------------------------------------------------------------------------------------
;;                                            Definitions
;;----------------------------------------------------------------------------------------------------------

;; A few of the functions listed above do not require mutual recursion.

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
;; pertaining to the gcd of integers, defined in "../numbers/euclid.lisp"), we use the names pgcd, rp, and sp
;; for the functions described earlier. The recursive Euclidean algorithm produces a polynomial of maximal 
;; degree that divides both of two given polynomials.  It is convenient to define the greatest common divisor 
;; to be monic.  Thus, we first define polynomials (pgcd-aux p q f), (rp-aux p q f), and (sp-aux p q f), 
;; which execute the recursive algorithm, and then divide each of these by the leading coefficient of 
;; (pgcd-aux p q f) to produce (pgcd p q f), (rp p q f), and (sp p q f).

;; The reader will notice that several definitions contain "nuisance terms" that are required for
;; admissibility but do not affect the value of the function in any case of interest.  For example, the
;; following term occurs in the definition of pgcd-aux:

;;              (let* ((c (fneg (fmul (car p) (frecip (car q) f) f) f))
;;	               (a (monomial c (- (degree p) (degree q)) f))
;;	               (pnew (padd (pmul a q f) p f)))
;;                (and (< (len pnew) (len p))
;;	               (pgcd-aux pnew q f)))

;; The condition (< (len pnew) (len p)) ensures that the declared measure for this function decreases in
;; the recursive call (pgcd-aux pnew q f).  we shall eventually prove that under suitable constraints on the
;; arguments, the inequality is necessarily satified and therefore may be ignored.

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

  ;; A generalized polynomial is a list of field elements:

  (defun gpolyp (l f)
    (declare (xargs :measure (list (len f) 1 (len l))))
    (if (consp l)
        (and (feltp (car l) f)
             (gpolyp (cdr l) f))
      (null l)))

  ;; A polynomial is a non-nil generalized polynomial with either degree 1 or a non-zero leading coefficient:

  (defund polyp (p f)
    (declare (xargs :measure (list (len f) 2 0)))
    (and (gpolyp p f)
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

  ;; Multiplication  of a polynomial by a field element:

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
        (prem (rp x (car f) (cdr f)) (car f) (cdr f))
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

  (defun rp-aux (p q f)
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
	             (rp-aux pnew q f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (padd (rp-aux p qnew f)
	                 (pneg (pmul a (sp-aux p qnew f) f) f)
		         f))))))))
	            
  (defun sp-aux (p q f)
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
	             (padd (sp-aux pnew q f)
	                   (pneg (pmul a (rp-aux pnew q f) f) f)
		           f)))
 	    (let* ((c (fmul (car q) (frecip (car p) f) f))
	           (a (monomial c (- (degree q) (degree p)) f))
	           (qnew (padd q (pneg (pmul a p f) f) f)))
	      (and (< (len qnew) (len q))
	           (sp-aux p qnew f))))))))

  (defund rp (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (r (rp-aux p q f)))
      (cmul (frecip (car g) f) r f)))

  (defund sp (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f))
          (s (sp-aux p q f)))
      (cmul (frecip (car g) f) s f)))

  (defund pgcd (p q f)
    (declare (xargs :measure (list (len f) 8 0)))
    (let ((g (pgcd-aux p q f)))
      (cmul (frecip (car g) f) g f)))

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

;; Our formal definition of a field extension depends on the notion of an irreducible
;; polynomial.  We are unable to formulate an algorithmic definition of irreducibility and 
;; therefore resort to defchoose.  First we define polynomial divisibility:

(defund pdivides (q p f)
  (equal (prem p q f) (pzero f)))

;; If p has a non-constant divisor of lesser degree, then such a divisor is returned by
;; the following function and p is said to be reducible:

(defchoose pfactor q (p f)
  (and (polyp q f)
       (> (degree q) 0)
       (< (degree q) (degree p))
       (pdivides q p f)))

(defund reduciblep (p f)
  (let ((q (pfactor p f)))
    (and (polyp q f)
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
;;     that holds iff the field f satisfies the axioms, e.g., (fadd-closed-p f), and define the predicate
;;     (field-axioms-p f) to be the conjunction of these predicates.  (These predicates are defined with
;;     defun-sk.)  For each of the field axioms, we prove a trivial lemma stating that the axiom follows 
;;     from (field-axioms-p f), e.g., 

;;     (defthm fadd-closed-*
;;       (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
;;                (feltp (fadd x y f) f))

;;     We also derive some simple consequences of these lemmas, e.g.,

;;     (defthm field-integral-domain-*
;;       (implies (and (field-axioms-p f) (feltp x f) (feltp y f)
;;   		       (equal (fmul x y f) (fzero f)))
;;   	          (or (equal x (fzero f))
;;   	              (equal y (fzero f)))))

;;     These lemmas will form the basis of the proofs in Step 2.

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
	   (feltp (fadd x y f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fadd-closed-p-necc))))

(defthm fmul-closed-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (feltp (fmul x y f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fmul-closed-p-necc))))

(defthm fadd-comm-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (equal (fadd x y f) (fadd y x f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fadd-comm-p-necc))))

(defthm fmul-comm-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f))
	   (equal (fmul x y f) (fmul y x f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fmul-comm-p-necc))))

(defthm fadd-assoc-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fadd-assoc-p-necc))))

(defthm fmul-assoc-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fmul-assoc-p-necc))))

(defthm feltp-fzero-*
  (implies (field-axioms-p f)
           (feltp (fzero f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p))))

(defthm feltp-fone-*
  (implies (field-axioms-p f)
           (feltp (fone f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p))))

(defthm fzero-id-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fadd (fzero f) x f) x))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fzero-id-p-necc))))

(defthm fone-id-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fmul (fone f) x f) x))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fone-id-p-necc))))

(defthm fone-fzero-*
  (implies (field-axioms-p f)
           (not (equal (fzero f) (fone f))))
  :hints (("Goal" :in-theory (enable field-axioms-p fone-fzero-p))))

(defthm feltp-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (feltp (fneg x f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (feltp-fneg-p-necc))))

(defthm fadd-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fadd x (fneg x f) f)
	          (fzero f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fadd-fneg-p-necc))))

(defthm feltp-frecip-*
  (implies (and (field-axioms-p f) (feltp x f) (not (equal x (fzero f))))
           (feltp (frecip x f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (feltp-frecip-p-necc))))

(defthm fmul-frecip-*
  (implies (and (field-axioms-p f) (feltp x f)  (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f)
	          (fone f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fmul-frecip-p-necc))))

(defthm fdistrib-*
  (implies (and (field-axioms-p f) (feltp x f) (feltp y f) (feltp z f))
                (equal (fmul x (fadd y z f) f)
		       (fadd (fmul x y f) (fmul x z f) f)))
  :hints (("Goal" :in-theory (enable field-axioms-p) :use (fdistrib-p-necc))))

(in-theory (disable fadd-closed-p fmul-closed-p fadd-comm-p fmul-comm-p fadd-assoc-p fmul-assoc-p feltp-fone-p fone-fzero-p
                    feltp-fzero-p fzero-id-p fone-id-p fadd-fneg-p feltp-fneg-p feltp-fneg-p fmul-frecip-p fdistrib-p))

;; Some consequences of the above lemmas:

(defthmd fneg-fzero-*
  (implies (and (field-axioms-p f) (feltp x f))
           (iff (equal (fneg x f) (fzero f))
                (equal x (fzero f))))
  :hints (("Goal" :in-theory (disable fzero-id-* fadd-fneg-*)
                  :use (fzero-id-* fadd-fneg-*
		        (:instance fzero-id-* (x (fneg (fzero f) f)))
                        (:instance fadd-comm-* (y (fzero f)))))))

(defthm fzero-id-2-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fadd x (fzero f) f) x))
  :hints (("Goal" :in-theory (disable fzero-id-*)
                  :use (fzero-id-* (:instance fadd-comm-* (y (fzero f)))))))

(defthmd fzero-unique-*
  (implies (and (field-axioms-p f)
                (feltp x f) (feltp y f) (equal (fadd x y f) (fzero f)))
	   (equal (fneg y f) x))
  :hints (("Goal" :use ((:instance fadd-assoc-* (z (fneg y f)))))))

(defthm fneg-fneg-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fneg (fneg x f) f)
	          x))
  :hints (("Goal" :use ((:instance fzero-unique-* (y (fneg x f)))))))

(defthm fone-id-2-*
  (implies (and (field-axioms-p f) (feltp x f))
	   (equal (fmul x (fone f) f) x))
  :hints (("Goal" :in-theory (disable fone-id-*)
                  :use (fone-id-* (:instance fmul-comm-* (y (fone f)))))))

(defthm fmul-fzero-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fmul x (fzero f) f)
	          (fzero f)))
  :hints (("Goal" :in-theory (disable fadd-fneg-* fzero-id-* fzero-id-2-* fadd-assoc-* fone-id-*)
                  :use (fadd-fneg-* fone-id-2-*
			(:instance fzero-id-* (x (fone f)))
			(:instance fdistrib-* (y (fzero f)) (z (fone f)))
		        (:instance fzero-id-2-* (x (fmul x (fzero f) f)))
		        (:instance fadd-assoc-* (x (fmul x (fzero f) f)) (y x) (z (fneg x f)))))))

(defthm fmul-fzero-2-*
  (implies (and (field-axioms-p f) (feltp x f))
           (equal (fmul (fzero f) x f)
	          (fzero f)))
  :hints (("Goal" :in-theory (disable fmul-fzero-*)
                  :use (fmul-fzero-* (:instance fmul-comm-* (y (fzero f)))))))

(defthm fneg-fmul-*
  (implies (and (field-axioms-p f)
                (feltp x f) (feltp y f))
	   (equal (fneg (fmul x y f) f)
	          (fmul x (fneg y f) f)))
  :hints (("Goal" :use ((:instance fzero-unique-* (x (fmul x (fneg y f) f)) (y (fmul x y f)))
                        (:instance fdistrib-* (y (fneg y f)) (z y))
			(:instance fadd-comm-* (x (fneg y f)))))))

(defthm field-integral-domain-*
  (implies (and (field-axioms-p f)
                (feltp x f)
		(feltp y f)
		(equal (fmul x y f) (fzero f)))
	   (or (equal x (fzero f))
	       (equal y (fzero f))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fone-id-2-* fmul-frecip-*)
                  :use (fone-id-2-*
		        (:instance fmul-assoc-* (z (frecip y f)))
		        (:instance fmul-frecip-* (x y))))))

(defthmd frecip-not-fzero-*
  (implies (and (field-axioms-p f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (frecip x f) (fzero f))))
  :hints (("Goal" :in-theory (disable fmul-frecip-* fmul-fzero-*)
                  :use (fmul-frecip-* fmul-fzero-*
		        (:instance fzero-id-* (x (fneg (fzero f) f)))
                        (:instance fadd-comm-* (y (fzero f)))))))


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
           (beltp (badd x y f) f))
  :hints (("Goal" :in-theory (enable beltp badd member-ninit))))

(defthm bmul-closed
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (beltp (bmul x y f) f))
  :hints (("Goal" :in-theory (enable beltp bmul member-ninit))))


;; Commutativity

(defthmd badd-comm
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (equal (badd x y f) (badd y x f)))
  :hints (("Goal" :in-theory (enable beltp badd member-ninit)
                  :use (f+comm))))

(defthmd bmul-comm
  (implies (and (fbasep f) (beltp x f) (beltp y f))
           (equal (bmul x y f) (bmul y x f)))
  :hints (("Goal" :in-theory (enable beltp bmul member-ninit)
                  :use (f*comm))))

;; Associativity:

(defthmd badd-assoc
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (badd x (badd y z f) f)
	          (badd (badd x y f) z f)))
  :hints (("Goal" :in-theory (e/d (fbasep beltp badd member-ninit)
                                   (ACL2::DEFAULT-MOD-RATIO ACL2::DEFAULT-MOD-1 ACL2::DEFAULT-MOD-2
				    ACL2::DEFAULT-PLUS-1 ACL2::DEFAULT-PLUS-2))
                  :use (f+assoc
		        (:instance rtl::mod-sum (rtl::a x) (rtl::b (+ y z)) (rtl::n f))
		        (:instance rtl::mod-sum (rtl::a z) (rtl::b (+ x y)) (rtl::n f))))))

(defthmd bmul-assoc
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (bmul x (bmul y z f) f)
	          (bmul (bmul x y f) z f)))
  :hints (("Goal" :in-theory (e/d (fbasep beltp bmul member-ninit)
                                   (ACL2::DEFAULT-MOD-RATIO ACL2::DEFAULT-MOD-1 ACL2::DEFAULT-MOD-2
				    ACL2::DEFAULT-TIMES-1 ACL2::DEFAULT-TIMES-2))
                  :use (f*assoc
		        (:instance rtl::mod-mod-times (rtl::b x) (rtl::a (* y z)) (rtl::n f))
		        (:instance rtl::mod-mod-times (rtl::b z) (rtl::a (* x y)) (rtl::n f))))))

;; Identities:

(defthm beltp-bzero
  (implies (fbasep f)
           (beltp (bzero f) f))
  :hints (("Goal" :in-theory (enable fbasep beltp bzero member-ninit))))

(defthm beltp-bone
  (implies (fbasep f)
           (beltp (bone f) f))
  :hints (("Goal" :in-theory (enable fbasep beltp bone member-ninit))))

(defthm bone-bzero
  (implies (fbasep f)
           (not (equal (bone f) (bzero f))))
  :hints (("Goal" :in-theory (enable fbasep beltp bzero bone member-ninit))))

(defthm bzero-id
  (implies (and (fbasep f) (beltp x f))
           (equal (badd (bzero f) x f) x))
  :hints (("Goal" :in-theory (enable fbasep beltp badd bzero member-ninit))))

(defthm bzero-id2
  (implies (and (fbasep f) (beltp x f))
           (equal (badd x (bzero f) f) x))
  :hints (("Goal" :in-theory (enable fbasep beltp badd bzero member-ninit))))

(defthm bone-id
  (implies (and (fbasep f) (beltp x f))
           (equal (bmul (bone f) x f) x))
  :hints (("Goal" :in-theory (enable fbasep beltp bmul bone member-ninit))))

;; Inverses:

(defthm beltp-bneg
  (implies (and (fbasep f) (beltp x f))
           (beltp (bneg x f) f))
  :hints (("Goal" :in-theory (enable fbasep beltp bneg member-ninit))))

(defthm bneg-bzero
  (implies (fbasep f)
           (equal (bneg (bzero f) f)
	          (bzero f)))
  :hints (("Goal" :in-theory (enable fbasep bzero bneg member-ninit))))

(defthm badd-bneg
  (implies (and (fbasep f) (beltp x f))
           (equal (badd x (bneg x f) f)
	          (bzero f)))
  :hints (("Goal" :in-theory (enable fbasep beltp bzero badd bneg member-ninit)
                  :use ((:instance rtl::mod-sum (rtl::a x) (rtl::b (- x)) (rtl::n f))))))

(defthm beltp-brecip
  (implies (and (fbasep f) (beltp x f) (not (equal x (bzero f))))
           (beltp (brecip x f) f))
  :hints (("Goal" :in-theory (enable fbasep beltp bzero brecip member-ninit))))

(defthm bmul-brecip
  (implies (and (fbasep f) (beltp x f) (not (equal x (bzero f))))
           (equal (bmul x (brecip x f) f)
	          (bone f)))
  :hints (("Goal" :in-theory (enable fbasep beltp bzero bone bmul brecip)
                  :use ((:instance member-ninit (n f))
		        (:instance rtl::mod-mod-times (rtl::b x) (rtl::a (expt x (- f 2))) (rtl::n f))
			(:instance divides-leq (x f) (y x))
		        (:instance fermat (m x) (p f))))))
;; Distributivity:

(local-defthmd hack-1
  (implies (and (integerp x) (integerp y) (integerp z) (primep f))
           (EQUAL (MOD (* X (MOD (+ Y Z) F)) F)
                  (MOD (+ (MOD (* X Y) F) (MOD (* X Z) F)) F)))
  :hints (("Goal" :use ((:instance rtl::mod-mod-times (rtl::b x) (rtl::a (+ y z)) (rtl::n f))
		        (:instance rtl::mod-sum (rtl::a (mod (* x y) f)) (rtl::b (* x z)) (rtl::n f))
		        (:instance rtl::mod-sum (rtl::a (* x z)) (rtl::b (* x y)) (rtl::n f))))))

(defthm bdistrib
  (implies (and (fbasep f) (beltp x f) (beltp y f) (beltp z f))
           (equal (bmul x (badd y z f) f)
	          (badd (bmul x y f) (bmul x z f) f)))
  :hints (("Goal" :in-theory (enable fbasep beltp badd bmul member-ninit)
                  :use (hack-1))))



(defthm badd-closed-step
  (implies (fbasep f)
           (fadd-closed-p f))
  :hints (("Goal" :in-theory (enable fadd fbasep feltp)
                  :use (fadd-closed-p-witness-lemma
		        (:instance badd-closed (x (mv-nth 0 (fadd-closed-p-witness f)))
			                       (y (mv-nth 1 (fadd-closed-p-witness f))))))))

(defthm bmul-closed-step
  (implies (fbasep f)
           (fmul-closed-p f))
  :hints (("Goal" :in-theory (enable fmul fbasep feltp)
                  :use (fmul-closed-p-witness-lemma
		        (:instance bmul-closed (x (mv-nth 0 (fmul-closed-p-witness f)))
			                       (y (mv-nth 1 (fmul-closed-p-witness f))))))))

(defthm badd-comm-step
  (implies (fbasep f)
           (fadd-comm-p f))
  :hints (("Goal" :in-theory (enable fadd fbasep feltp)
                  :use (fadd-comm-p-witness-lemma
		        (:instance badd-comm (x (mv-nth 0 (fadd-comm-p-witness f)))
			                     (y (mv-nth 1 (fadd-comm-p-witness f))))))))

(defthm bmul-comm-step
  (implies (fbasep f)
           (fmul-comm-p f))
  :hints (("Goal" :in-theory (enable fmul fbasep feltp)
                  :use (fmul-comm-p-witness-lemma
		        (:instance bmul-comm (x (mv-nth 0 (fmul-comm-p-witness f)))
			                     (y (mv-nth 1 (fmul-comm-p-witness f))))))))

(defthm badd-assoc-step
  (implies (fbasep f)
           (fadd-assoc-p f))
  :hints (("Goal" :in-theory (enable fadd fbasep feltp)
                  :use (fadd-assoc-p-witness-lemma
		        (:instance badd-assoc (x (mv-nth 0 (fadd-assoc-p-witness f)))
			                      (y (mv-nth 1 (fadd-assoc-p-witness f)))
					      (z (mv-nth 2 (fadd-assoc-p-witness f))))))))

(defthm bmul-assoc-step
  (implies (fbasep f)
           (fmul-assoc-p f))
  :hints (("Goal" :in-theory (enable fmul fbasep feltp)
                  :use (fmul-assoc-p-witness-lemma
		        (:instance bmul-assoc (x (mv-nth 0 (fmul-assoc-p-witness f)))
			                      (y (mv-nth 1 (fmul-assoc-p-witness f)))
					      (z (mv-nth 2 (fmul-assoc-p-witness f))))))))

(in-theory (disable (fzero) (fone)))

(defthm feltp-bzero-step
  (implies (fbasep f)
           (feltp-fzero-p f))
  :hints (("Goal" :in-theory (enable feltp fzero fbasep)
                  :use (beltp-bzero feltp-fzero-p-witness-lemma))))

(defthm feltp-bone-step
  (implies (fbasep f)
           (feltp-fone-p f))
  :hints (("Goal" :in-theory (enable feltp fone fbasep)
                  :use (beltp-bone feltp-fone-p-witness-lemma))))

(defthm bone-bzero-step
  (implies (fbasep f)
           (fone-fzero-p f))
  :hints (("Goal" :in-theory (enable feltp fzero fone fbasep)
                  :use (bone-bzero fone-fzero-p-witness-lemma))))

(defthm bzero-id-step
  (implies (fbasep f)
           (fzero-id-p f))
  :hints (("Goal" :in-theory (enable feltp fadd fzero fone fbasep)
                  :use (fzero-id-p-witness-lemma
			(:instance bzero-id (x (fzero-id-p-witness f)))))))

(defthm bone-id-step
  (implies (fbasep f)
           (fone-id-p f))
  :hints (("Goal" :in-theory (enable feltp fmul fzero fone fbasep)
                  :use (fone-id-p-witness-lemma
			(:instance bone-id (x (fone-id-p-witness f)))))))

(defthm feltp-bneg-step
  (implies (fbasep f)
           (feltp-fneg-p f))
  :hints (("Goal" :in-theory (enable feltp fadd fneg fzero fone fbasep)
                  :use (feltp-fneg-p-witness-lemma
			(:instance beltp-bneg (x (feltp-fneg-p-witness f)))))))

(defthm feltp-brecip-step
  (implies (fbasep f)
           (feltp-frecip-p f))
  :hints (("Goal" :in-theory (enable feltp fadd frecip fzero fone fbasep)
                  :use (feltp-frecip-p-witness-lemma
			(:instance beltp-brecip (x (feltp-frecip-p-witness f)))))))

(defthm fadd-bneg-step
  (implies (fbasep f)
           (fadd-fneg-p f))
  :hints (("Goal" :in-theory (enable feltp fadd fneg fzero fone fbasep)
                  :use (fadd-fneg-p-witness-lemma
			(:instance badd-bneg (x (fadd-fneg-p-witness f)))))))

(defthm fmul-brecip-step
  (implies (fbasep f)
           (fmul-frecip-p f))
  :hints (("Goal" :in-theory (enable feltp fmul frecip fzero fone fbasep)
                  :use (fmul-frecip-p-witness-lemma
			(:instance bmul-brecip (x (fmul-frecip-p-witness f)))))))

(defthm bdistrib-step
  (implies (fbasep f)
           (fdistrib-p f))
  :hints (("Goal" :in-theory (enable feltp fadd fmul frecip fbasep)
                  :use (fdistrib-p-witness-lemma
			(:instance bdistrib (x (mv-nth 0 (fmul-frecip-p-witness f)))
			                    (y (mv-nth 1 (fmul-frecip-p-witness f)))
					    (z (mv-nth 2 (fmul-frecip-p-witness f))))))))

(defthmd field-axioms-p-fbasep
  (implies (fbasep f)
           (field-axioms-p f))
  :hints (("Goal" :in-theory (enable field-axioms-p))))


;;----------------------------------------------------------------------------------------------------------
;;                                           Step 3: Addition
;;----------------------------------------------------------------------------------------------------------

;; In this section, we prove the lemmas of Step 3 pertaining to addition.

;;----------------------
;; Identity
;;----------------------

(defthm feltp-fzero
  (implies (fieldp f)
           (feltp (fzero f) f))
  :hints (("Goal" :in-theory (enable fieldp fzero feltp polyp))))

(defthm polyp-pzero
  (implies (fieldp f)
           (polyp (pzero f) f))
  :hints (("Goal" :in-theory (enable fieldp pzero polyp))))

(local-defthmd faddl-fzero
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f)
		(consp x))
	   (equal (faddl (list (fzero f)) x f)
	          x))
  :hints (("Goal" :induct (len x))))

(defthm pzero-id-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (padd (pzero f) x f)
	          x))
  :hints (("Goal" :in-theory (enable fzero pzero polyp padd)
                  :use (faddl-fzero))))

(local-defthm fieldp-cdr
  (implies (and (fieldp f) (consp f))
           (fieldp (cdr f)))
  :hints (("Goal" :in-theory (enable fieldp))))


;;----------------------
;; Inverse
;;----------------------

(defthm len-pneg
  (equal (len (pneg x f))
         (len x)))

(defthm len-fneg
  (implies (consp f)
           (equal (len (fneg x f))
                  (len x)))
  :hints (("Goal" :expand ((fneg x f)))))

(local-defthmd gpolyp-pneg
  (implies (and (fieldp f) (field-axioms-p f) (gpolyp x f))
           (gpolyp (pneg x f) f))
  :hints (("Goal" :induct (len x))))

(defthm polyp-pneg-*
  (implies (and (fieldp f) (field-axioms-p f) (polyp x f))
           (polyp (pneg x f) f))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (gpolyp-pneg
		        (:instance fneg-fzero-* (x (car x)))))))

(local-defthmd faddl-pneg
  (implies (and (fieldp f) (field-axioms-p f) (gpolyp x f) (consp x))
           (equal (pstrip (faddl x (pneg x f) f) f)
	          (list (fzero f))))
  :hints (("Goal" :induct (len x))))

(defthmd padd-pneg-*
  (implies (and (fieldp f) (field-axioms-p f) (polyp x f))
           (equal (padd x (pneg x f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable pzero fzero polyp padd)
                  :use (faddl-pneg))))

		  
;;----------------------
;; Closure
;;----------------------

(defun fadd-comm-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (fadd-comm-induct (cdr x) y)
    (if (< (len x) (len y))
        (fadd-comm-induct x (cdr y))
      (if (and (consp x) (consp y))
          (fadd-comm-induct (cdr x) (cdr y))
	()))))

(local-defthmd gpolyp-faddl
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f))
           (gpolyp (faddl x y f) f))
  :hints (("Goal" :induct (fadd-comm-induct x y))  
          ("Subgoal *1/4" :in-theory (enable gpolyp) :expand ((faddl x () f) (faddl y () f)))
          ("Subgoal *1/3" :in-theory (enable gpolyp):expand ((faddl x y f) (faddl y x f))
	                  :use ((:instance fadd-closed-* (x (car x)) (y (car y)))))))

(local-defun faddl-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (faddl-induct (cdr x) y)
    (if (> (len y) (len x))
        (faddl-induct x (cdr y))
      (if (consp x)
          (faddl-induct (cdr x) (cdr y))
        ()))))

(local-defthmd len-faddl
  (equal (len (faddl x y f))
	 (max (len x) (len y)))
  :hints (("Goal" :induct (faddl-induct x y))))

(local-defthmd consp-faddl
  (implies (and (fieldp f) (consp f)
                (feltp x f) (feltp y f))
	   (consp (faddl x y (cdr f))))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :use ((:instance len-faddl (f (cdr f)))))))

(local-defthmd len-pstrip
  (<= (len (pstrip x f)) (len x)))

(local-defthm gpolyp-pstrip
  (implies (fieldp f)
           (iff (gpolyp (pstrip x f) f)
	        (gpolyp x f))))

(defthmd polyp-pstrip
  (implies (fieldp f)
           (iff (polyp (pstrip x f) f)
	        (and (gpolyp x f) (consp x))))
  :hints (("Goal" :in-theory (enable polyp))))

(defthmd feltp-pstrip
  (implies (and (fieldp f) (consp f) (gpolyp x (cdr f)) (consp x) (< (len x) (len (car f))))
           (feltp (pstrip x (cdr f)) f))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :use ((:instance len-pstrip (f (cdr f)))
		        (:instance polyp-pstrip (f (cdr f)))))))

(local-defthmd polyp-pstrip-2
  (implies (and (fieldp f) (gpolyp x f) (consp x))
           (polyp (pstrip x f) f))
  :hints (("Goal" :in-theory (enable fieldp gpolyp polyp feltp)
                  :use (len-pstrip polyp-pstrip))))

(defthm padd-closed-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
           (polyp (padd x y f) f))
  :hints (("Goal" :in-theory (enable padd polyp feltp)
                  :use (gpolyp-faddl len-faddl len-pstrip
		        (:instance polyp-pstrip-2 (x (faddl x y f)))))))


;;----------------------
;; Commutativity
;;----------------------

(defun fadd-comm-induct (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (> (len x) (len y))
      (fadd-comm-induct (cdr x) y)
    (if (< (len x) (len y))
        (fadd-comm-induct x (cdr y))
      (if (and (consp x) (consp y))
          (fadd-comm-induct (cdr x) (cdr y))
	()))))

(local-defthmd faddl-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f))
           (equal (faddl x y f) (faddl y x f)))
  :hints (("Goal" :induct (fadd-comm-induct x y))
          ("Subgoal *1/4" :expand ((faddl x () f) (faddl y () f)))
          ("Subgoal *1/3" :expand ((faddl x y f) (faddl y x f))
	                  :use ((:instance fadd-comm-* (x (car x)) (y (car y)))))))

(defthmd padd-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
           (equal (padd x y f) (padd y x f)))
  :hints (("Goal" :in-theory (enable padd polyp)
                  :use (faddl-comm))))

;; The following variant of pzero-id is a consequence of padd-comm-*:

(defthm pzero-id-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (padd x (pzero f) f)
	          x))
  :hints (("Goal" :use ((:instance padd-comm-* (y (pzero f)))))))


;;----------------------
;; Associativity
;;----------------------

;; First we show that if f satisfies the field axioms, then

;;   (pstrip (faddl (pstrip x f) y f) f) = (pstrip (faddl x y f) f).

;; We nmay assume (car x) = (fzero f).  We consider 2 cases:

;; If (len x) <= (len y), then we can prove the stronger result (faddl (pstrip x f) x f) = (fadd x y f):

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

(defun fadd-assoc-induct (x y)
  (if (consp y)
      (if (< (len x) (len y))
          (fadd-assoc-induct x (cdr y))
	(fadd-assoc-induct (cdr x) (cdr y)))
    ()))

(local-defthmd pstrip-faddl-pstrip-1-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(equal (car x) (fzero f)) (= (len x) (len y))
		(equal (faddl (pstrip (cdr x) f) (cdr y) f)
		       (faddl (cdr x) (cdr y) f)))
	   (equal (faddl (pstrip x f) y f)
	          (faddl x y f)))
  :hints (("Goal" :cases ((consp (cdr x)))
                  :expand ((pstrip x f) (faddl (pstrip (cdr x) f) y f))
	          :use ((:instance len-pstrip (x (cdr x)))
		        (:instance fzero-id-* (x (car y)))))))

(local-defthmd pstrip-faddl-pstrip-1-2
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(< (len x) (len y))
		(equal (faddl (pstrip x f) (cdr y) f)
		       (faddl x (cdr y) f)))
	   (equal (faddl (pstrip x f) y f)
	          (faddl x y f)))
  :hints (("Goal" :cases ((consp (cdr x)))
                  :expand ((faddl x y f) (faddl (pstrip (cdr x) f) y f))
	          :use (len-pstrip))))

(defthmd pstrip-faddl-pstrip-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(equal (car x) (fzero f))
		(<= (len x) (len y)))
	   (equal (faddl (pstrip x f) y f)
	          (faddl x y f)))
  :hints (("Goal" :induct (fadd-assoc-induct x y))
          ("Subgoal *1/2" :use (pstrip-faddl-pstrip-1-1))
          ("Subgoal *1/1" :use (pstrip-faddl-pstrip-1-2))))

;; Now suppose (len x) > (len y).  Then by induction,

;;    (pstrip (faddl (pstrip x f) y f) f) = (pstrip (faddl (pstrip (cdr x) f) y f) f)
;;                                        = (pstrip (faddl (cdr x) y f) f)
;;                                        = (pstrip (cons (car y) (faddl (cdr x) (cdr y) f)) f)
;;                                        = (pstrip (faddl x y f) f)

(local-defthm faddl-nil
  (implies (and (fieldp f) (gpolyp x f) (= (len y) 0))
           (equal (faddl x y f) x))
  :hints (("Goal" :induct (len x))))

(defthm pstrip-pstrip
  (equal (pstrip (pstrip x f) f)
         (pstrip x f)))

(local-defthmd pstrip-faddl-pstrip-2-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(> (len x) (len y))
		(= (len y) 0))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f)))
  :hints (("Goal" :expand ((pstrip x f) (faddl x y f))
		  :use ((:instance len-faddl (x (cdr x)))
		        (:instance pstrip-faddl-pstrip-1 (x (cdr x)))))))

(local-defthmd pstrip-faddl-pstrip-2-2
  (implies (and (fieldp f) (field-axioms-p f) 
                (gpolyp x f) (gpolyp y f)
		(> (len x) (len y))
		(posp (len y))
		(equal (car x) (fzero f))
		(implies (> (len (cdr x)) (len y))
		         (equal (pstrip (faddl (pstrip (cdr x) f) y f) f)
			        (pstrip (faddl (cdr x) y f) f))))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f)))
  :hints (("Goal" :expand ((pstrip x f) (faddl x y f))
		  :use ((:instance len-faddl (x (cdr x)))
		        (:instance pstrip-faddl-pstrip-1 (x (cdr x)))))))

(local-defthmd pstrip-faddl-pstrip-2-3
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(> (len x) (len y))
		(equal (car x) (fzero f))
		(implies (> (len (cdr x)) (len y))
		         (equal (pstrip (faddl (pstrip (cdr x) f) y f) f)
			        (pstrip (faddl (cdr x) y f) f))))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f)))
  :hints (("Goal" :use (pstrip-faddl-pstrip-2-1 pstrip-faddl-pstrip-2-2))))

(local-defthmd pstrip-faddl-pstrip-2
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
		(> (len x) (len y))
		(equal (car x) (fzero f)))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f)))
  :hints (("Goal" :induct (len x))
          ("Subgoal *1/1" :use (pstrip-faddl-pstrip-2-3))))

(defthmd pstrip-faddl-pstrip
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f))
           (equal (pstrip (faddl (pstrip x f) y f) f)
	          (pstrip (faddl x y f) f)))
  :hints (("Goal" :use (pstrip-faddl-pstrip-1 pstrip-faddl-pstrip-2)
                  :expand ((pstrip x f)))))

;; Consequently,

;;   (padd (padd x y f) z f) = (pstrip (faddl (pstrip (faddl x y f) f) z f) f)
;;                           = (pstrip (faddl (faddl x y f) x f) f)

;; and by padd-comm-* and faddl-comm, 

;;   (padd x (padd y z f) f) = (padd (padd y z f) x f)
;;                           = (pstrip (faddl (faddl y z f) x f) f)
;;                           = (pstrip (faddl x (faddl y z f) f) f).

(local-defthmd padd-faddl-assoc-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (padd (padd x y f) z f)
	          (pstrip (faddl (faddl x y f) z f) f)))
  :hints (("Goal" :in-theory (enable polyp padd)
                  :use (gpolyp-faddl
		        (:instance pstrip-faddl-pstrip (x (faddl x y f)) (y z))))))

(local-defthmd padd-faddl-assoc-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (padd x (padd y z f) f)
	          (pstrip (faddl (faddl y z f) x f) f)))
  :hints (("Goal" ;:in-theory (enable polyp)
                  :use (fadd-closed-*
		        (:instance padd-closed-* (x y) (y z))
                        (:instance padd-faddl-assoc-1 (x y) (y z) (z x))
                        (:instance padd-comm-* (y (padd y z f)))))))

(local-defthmd padd-faddl-assoc-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (faddl (faddl y z f) x f)
	          (faddl x (faddl y z f) f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance faddl-comm (y (faddl y z f)))
			(:instance gpolyp-faddl (x y) (y z))))))

(local-defthmd padd-faddl-assoc-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (padd x (padd y z f) f)
	          (pstrip (faddl x (faddl y z f) f) f)))
  :hints (("Goal" :use (padd-faddl-assoc-2 padd-faddl-assoc-3))))

(defthmd padd-faddl-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(equal (faddl (faddl x y f) z f)
		       (faddl x (faddl y z f) f)))
	   (equal (padd (padd x y f) z f)
	          (padd x (padd y z f) f)))	          
  :hints (("Goal" :use (padd-faddl-assoc-1 padd-faddl-assoc-4))))

;; Substituting (cdr f) for f, we have

(defthmd fadd-faddl-assoc
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f) (feltp z f)
		(equal (faddl (faddl x y (cdr f)) z (cdr f))
		       (faddl x (faddl y z (cdr f)) (cdr f))))
	   (equal (fadd (fadd x y f) z f)
	          (fadd x (fadd y z f) f)))	          
  :hints (("Goal" :in-theory (enable feltp fadd)
                  :use ((:instance padd-faddl-assoc (f (cdr f)))))))

;; Thus, it suffices to prove associativity of faddl.  This is easily proved by induction, but the proof
;; involves an inductive hypothisis for every possible ordering of (len x), len y), and (len z):

(defun faddl-assoc-induct (x y z)
  (declare (xargs :measure (+ (len x) (len y) (len z))))
  (if (and (> (len x) (len y)) (> (len x) (len z)))
      (faddl-assoc-induct (cdr x) y z)
    (if (and (= (len x) (len y)) (> (len x) (len z)))
	(faddl-assoc-induct (cdr x) (cdr y) z)
      (if (and (= (len x) (len z)) (> (len x) (len y)))
          (faddl-assoc-induct (cdr x) y (cdr z))
        (if (and (= (len x) (len y)) (= (len x) (len z)) (consp x))
	    (faddl-assoc-induct (cdr x) (cdr y) (cdr z))
	  (if (and (> (len y) (len x)) (> (len y) (len z)))
	      (faddl-assoc-induct x (cdr y) z)
	    (if (and (> (len z) (len y)) (> (len z) (len x)))
	        (faddl-assoc-induct x y (cdr z))
	      (if (and (= (len y) (len z)) (> (len y) (len x)))
	          (faddl-assoc-induct x (cdr y) (cdr z))
	        ()))))))))

(local-defthm faddl-assoc-1
  (implies (and (> (len x) (len y)) (> (len x) (len z))
		(equal (faddl (faddl (cdr x) y f) z f)
		       (faddl (cdr x) (faddl y z f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-2
  (implies (and (= (len x) (len y)) (> (len x) (len z))
		(equal (faddl (faddl (cdr x) (cdr y) f) z f)
		       (faddl (cdr x) (faddl (cdr y) z f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-3
  (implies (and (= (len x) (len z)) (> (len x) (len y))
		(equal (faddl (faddl (cdr x) y f) (cdr z) f)
		       (faddl (cdr x) (faddl y (cdr z) f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-4
  (implies (and (= (len x) (len y)) (= (len x) (len z))
                (equal (fadd (fadd (car x) (car y) f) (car z) f)
		       (fadd (car x) (fadd (car y) (car z) f) f))
		(equal (faddl (faddl (cdr x) (cdr y) f) (cdr z) f)
		       (faddl (cdr x) (faddl (cdr y) (cdr z) f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-5
  (implies (and (> (len y) (len x)) (> (len y) (len z))
                (equal (faddl (faddl x (cdr y) f) z f)
		       (faddl x (faddl (cdr y) z f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-6
  (implies (and (> (len y) (len x)) (= (len y) (len z))
                (equal (faddl (faddl x (cdr y) f) (cdr z) f)
		       (faddl x (faddl (cdr y) (cdr z) f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x y f) (faddl x (faddl y z f) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-assoc-7
  (implies (and (> (len z) (len x)) (> (len z) (len y))
                (equal (faddl (faddl x y f) (cdr z) f)
		       (faddl x (faddl y (cdr z) f) f)))
	   (equal (faddl (faddl x y f) z f)
		  (faddl x (faddl y z f) f)))
  :hints (("Goal" :expand ((faddl x (cons (car z) (faddl y (cdr z) f)) f) (faddl y z f) (faddl (faddl x y f) z f))
                  :use (len-faddl
		        (:instance len-faddl (x y) (y z))))))

(local-defthm faddl-nil-nil
  (implies (and (or (= (len x) 0) (atom x))
                (or (= (len y) 0) (atom y)))
           (equal (faddl x y f) ())))

(defthmd faddl-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f) (gpolyp z f))
           (equal (faddl (faddl x y f) z f)
                  (faddl x (faddl y z f) f)))
  :hints (("Goal" :induct (faddl-assoc-induct x y z))
          ("Subgoal *1/7" :in-theory (disable faddl-assoc-6) :use (faddl-assoc-6))
          ("Subgoal *1/5" :in-theory (disable faddl-assoc-5) :use (faddl-assoc-5))
          ("Subgoal *1/3" :in-theory (disable faddl-assoc-3) :use (faddl-assoc-3))
          ("Subgoal *1/1" :in-theory (disable faddl-assoc-1) :use (faddl-assoc-1))
          ("Subgoal *1/4" :in-theory (disable faddl-assoc-4) :use (faddl-assoc-4 (:instance fadd-assoc-* (x (car x)) (y (car y)) (z (car z)))))))

;; Finally, we combine fadd-faddl-assoc and padd-faddl-assoc with faddl-assoc:

(defthmd padd-assoc-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y z f) f)
	          (padd (padd x y f) z f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (padd-faddl-assoc faddl-assoc))))


;;--------------------------------
;; Degree of a Sum of Polynomials
;;--------------------------------

;; These results will be useful in the next section:

(defthmd degree-padd-bound-*
  (<= (degree (padd x y f))
      (max (degree x) (degree y)))
  :hints (("Goal" :in-theory (enable len-faddl padd)
                  :use ((:instance len-pstrip (x (faddl x y f)))))))

(local-defthm car-faddl
  (equal (car (faddl x y f))
         (if (> (len x) (len y))
             (car x)
	   (if (< (len x) (len y))
	       (car y)
	     (if (consp x)
	         (fadd (car x) (car y) f)
	       ()))))
  :hints (("Goal" :expand (faddl x y f))))

(local-defthm pstrip-noop
  (implies (not (equal (car x) (fzero f)))
           (equal (pstrip x f) x)))

(defthmd degree-padd-diff-*
  (implies (and (polyp x f) (polyp y f) (not (= (degree x) (degree y))))
           (equal (degree (padd x y f))
	          (max (degree x) (degree y))))
  :hints (("Goal" :in-theory (enable len-faddl polyp padd))))

(local-defthmd polyp-def
  (iff (polyp p f)
       (and (gpolyp p f)
            (consp p)
            (or (null (cdr p))
                (not (equal (car p) (fzero f))))))
  :hints (("Goal" :in-theory (enable polyp))))

(defthmd degree-padd-less-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(= (degree x) (degree y)) (posp (degree x))
		(equal (car y) (fneg (car x) f)))
	   (< (degree (padd x y f)) (degree x)))
  :hints (("Goal" :in-theory (e/d (padd len-faddl) (car-faddl))
                  :use (car-faddl
		        (:instance polyp-def (p x))
		        (:instance polyp-def (p y))
			(:instance fadd-fneg-* (x (car x)))
			(:instance len-pstrip (x (faddl (cdr x) (cdr y) f)))))))


;;----------------------------------------------------------------------------------------------------------
;;                                          Step 3: Multiplication
;;----------------------------------------------------------------------------------------------------------

;; In this section, we prove the lemmas of Step 3 pertaining to multiplication.

;;----------------------
;; Identity
;;----------------------

(defthm feltp-fone
  (implies (fieldp f)
           (feltp (fone f) f))
  :hints (("Goal" :in-theory (enable fieldp fone feltp polyp))))

(defthm polyp-pone
  (implies (fieldp f)
           (polyp (pone f) f))
  :hints (("Goal" :in-theory (enable fieldp pone polyp))))

(defthm pone-pzero
  (implies (fieldp f)
           (not (equal (pone f) (pzero f))))
  :hints (("Goal" :in-theory (enable fieldp fzero fone pzero pone polyp))))

(defthm fone-fzero
  (implies (fieldp f)
           (not (equal (fone f) (fzero f))))
  :hints (("Goal" :in-theory (enable fieldp fzero fone feltp polyp))))

(local-defthm cmul-fone
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f))
	   (equal (cmul (fone f) x f)
	          x))
  :hints (("Goal" :induct (len x))))

(defthm pone-id-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pmul (pone f) x f)
	          x))
  :hints (("Goal" :in-theory (enable polyp pzero pone)
		  :use (pzero-id-* (:instance padd-comm-* (y (list (fzero f))))))))

(defthmd fone-id-1
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
	   (and (< (degree x) (degree (car f)))
	        (equal (fmul (fone f) x f)
	               (prem x (car f) (cdr f)))))
  :hints (("Goal" :in-theory (e/d (feltp fone pzero pone fmul) (pone-id-*))
                  :use ((:instance pone-id-* (f (cdr f)))))))


;;-------------------------------------------
;; Multiplication by Constants and Monomials
;;-------------------------------------------

(defthm len-cmul
  (implies (not (equal c (fzero f)))
           (equal (len (cmul c x f))
                  (len x))))

(local-defthm gpolyp-cmul
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (gpolyp x f))
           (gpolyp (cmul c x f) f))
  :hints (("Goal" :induct (len x))))

(defthm car-cmul
  (implies (and (consp x) (not (equal c (fzero f))))
           (equal (car (cmul c x f))
                  (fmul c (car x) f))))

(defthmd cmul-nonzero
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (not (equal x (pzero f))))
	   (not (equal (cmul c x f) (pzero f))))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :expand ((cmul c x f))
		  :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(defthmd car-cmul-nonzero
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f))
           (or (null (cdr x))
	       (not (equal (car (cmul c x f))
	                   (fzero f)))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(defthmd polyp-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (let ((p (cmul c x f)))
	     (and (polyp p f)
	          (equal (degree p) (degree x))
		  (equal (car p) (fmul c (car x) f)))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ( car-cmul-nonzero))))

(local-defthmd cmul-cmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f)))
                (gpolyp x f))
	   (equal (cmul c (cmul d x f) f)
	          (cmul (fmul c d f) x f)))
  :hints (("Goal" :induct (len x))
          ("Subgoal *1/2" :use ((:instance field-integral-domain-* (x c) (y d))))
          ("Subgoal *1/1" :use ((:instance field-integral-domain-* (x c) (y d))
			        (:instance fmul-assoc-* (x c) (y d) (z (car x)))
			        (:instance fmul-comm-* (x (fmul c d f)) (y (car x)))))))

(defthmd cmul-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f)))
                (polyp x f))
	   (equal (cmul c (cmul d x f) f)
	          (cmul (fmul c d f) x f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (cmul-cmul-1))))
		  
(local-defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(local-defthm car-append
  (implies (consp x)
           (equal (car (append x y))
                  (car x))))

(defthm len-pshift
  (implies (natp k)
           (equal (len (pshift x k f))
	          (+ k (len x)))))

(defthm car-pshift
  (implies (consp x)
           (equal (car (pshift x k f))
	          (car x))))

(defthm degree-monomial
  (implies (natp k)
           (equal (degree (monomial c k f))
	          k))
  :hints (("Goal" :in-theory (enable monomial))))

(defthm car-monomial
  (equal (car (monomial c k f))
         c)
  :hints (("Goal" :in-theory (enable monomial))))

(local-defthm pgolyp-append
  (implies (and (gpolyp x f) (gpolyp y f))
           (gpolyp (append x y) f)))

(local-defthm gpolyp-pshift
  (implies (and (fieldp f) (natp k) (gpolyp x f))
           (gpolyp (pshift x k f) f)))

(defthm polyp-pshift
  (implies (and (fieldp f) (natp k) (polyp x f) (not (equal x (pzero f))))
           (let ((p (pshift x k f)))
             (and (polyp p f)
	          (equal (degree p) (+ k (degree x)))
		  (equal (car p) (car x)))))
  :hints (("Goal" :in-theory (enable pzero polyp))))

(defthmd polyp-car-nonzero
  (implies (and (polyp x f) (not (equal x (pzero f))))
           (and (feltp (car x) f)
	        (not (equal (car x) (fzero f)))))
  :hints (("Goal" :in-theory (enable pzero)
                  :use ((:instance polyp-def (p x))))))

(defthmd pshift-nonzero
  (implies (and (polyp x f) (not (equal x (pzero f))) (natp k))
           (not (equal (pshift x k f) (pzero f))))
  :hints (("Goal" :in-theory (e/d (pzero) (car-pshift))
                  :use (car-pshift polyp-car-nonzero (:instance polyp-def (p x))))))

(defthm polyp-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (natp k))
           (polyp (monomial c k f) f))
  :hints (("Goal" :in-theory (enable monomial polyp))))

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

(local-defthm gpolyp-fzero-list
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (gpolyp (fzero-list k f) f)))

(defthm len-fzero-list
  (implies (natp k)
           (equal (len (fzero-list k f))
	          k)))

(defthm append-fzero-list
  (implies (and (natp k) (natp l))
           (equal (append (fzero-list k f) (fzero-list l f))
	          (fzero-list (+ k l) f))))

(defthmd consp-fzero-list
  (implies (posp k)
           (consp (fzero-list k f)))
  :hints (("Subgoal *1/3" :expand ((fzero-list 1 f)))))

(defthm pstrip-fzero-list
  (implies (posp k)
           (equal (pstrip (fzero-list k f) f)
                  (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))
          ("Subgoal *1/3" :expand ((fzero-list 1 f)))))

(defun fzero-list-p (l f)
  (if (consp l)
      (and (equal (car l) (fzero f))
           (fzero-list-p (cdr l) f))
    t))

(local-defthmd pstrip-fzero-list-p
  (implies (and (gpolyp l f) (fzero-list-p l f) (consp l))
           (equal (pstrip l f) (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd pstrip-fzero-list-converse
  (implies (and (gpolyp x f)  (equal (pstrip x f) (pzero f)))
           (fzero-list-p x f))
  :hints (("Goal" :in-theory (enable pzero))))

(defthmd pstrip-append
  (implies (and (fieldp f) (field-axioms-p f)
		(gpolyp x f) (gpolyp y f) (consp x) (consp y))
	   (equal (pstrip (append x y) f)
	          (if (fzero-list-p x f)
		      (pstrip y f)
		    (append (pstrip x f) y)))))

(local-defthmd fzero-list-p-cmul
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (feltp c f) (not (equal c (fzero f))))
	   (iff (fzero-list-p (cmul c x f) f)
	        (fzero-list-p x f)))
  :hints (("Subgoal *1/2" :expand ((CMUL C X F))
                          :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(local-defthm faddl-fzero-list
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (equal (faddl (fzero-list k f) (fzero-list k f) f)
	          (fzero-list k f))))

(local-defthmd pshift-rewrite-1
  (implies (and (true-listp x) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f)))))

(local-defthm true-listp-gpolyp
  (implies (gpolyp x f)
           (true-listp x)))

(defthmd pshift-rewrite
  (implies (and (polyp x f) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f))))
  :hints (("Goal" :in-theory (enable polyp) :use (pshift-rewrite-1))))

(defthmd pshift-pshift
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (natp k) (natp l))
           (equal (pshift (pshift x k f) l f)
	          (pshift x (+ k l) f)))
  :hints (("Goal" :in-theory (enable pzero polyp pshift-rewrite-1))))

(local-defthmd faddl-append
  (implies (and (fieldp f) (field-axioms-p f)
		(gpolyp x f) (gpolyp y f) (gpolyp z f))
	   (equal (faddl (append x z) (append y z) f)
	          (append (faddl x y f) (faddl z z f))))
  :hints (("Goal" :induct (fadd-comm-induct x y))))

(local-defthmd faddl-pshift
  (implies (and (fieldp f) (field-axioms-p f)
		(gpolyp x f) (gpolyp y f) (natp k))
	   (equal (faddl (pshift x k f) (pshift y k f) f)
	          (pshift (faddl x y f) k f)))
  :hints (("Goal" :in-theory (enable pshift-rewrite faddl-append))))

(local-defthmd polyp-fzero-list-p
  (implies (and (polyp x f) (not (equal x (pzero f))))
           (not (fzero-list-p x f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use ((:instance polyp-def (p x))))))

(defthmd pstrip-pshift
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (equal x (pzero f)))
		(natp k))
	   (equal (pstrip (pshift x k f) f)
	          (pshift (pstrip x f) k f)))
  :hints (("Goal" :in-theory (enable pstrip-append)
                  :use (polyp-fzero-list-p consp-fzero-list		  
		        (:instance polyp-def (p x))))))

(local-defthmd pstrip-pshift-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (consp x) (not (fzero-list-p x f))
		(natp k))
	   (equal (pstrip (pshift x k f) f)
	          (pshift (pstrip x f) k f)))
  :hints (("Goal" :in-theory (enable pshift-rewrite-1 pstrip-append)
                  :use (polyp-fzero-list-p consp-fzero-list))))

(local-defthmd consp-faddl-1
  (implies (consp x)
           (consp (faddl x y f)))
  :hints (("Goal" :expand ((FADDL X Y F)))))

(local-defthmd fzero-list-p-faddl
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f) (consp x) (fzero-list-p (faddl x y f) f))
           (equal (padd x y f) (pzero f)))
  :hints (("Goal" :in-theory (enable consp-faddl-1 gpolyp-faddl padd)
                  :use ((:instance pstrip-fzero-list-p (l (faddl x y f)))))))
		  
(defthmd padd-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (polyp y f) (natp k)
		(not (equal (padd x y f) (pzero f))))
	   (equal (padd (pshift x k f) (pshift y k f) f)
	          (pshift (padd x y f) k f)))
  :hints (("Goal" :in-theory (enable pstrip-fzero-list-p consp-faddl-1 pstrip-pshift-1 gpolyp-faddl polyp padd faddl-pshift)
                  :use (fzero-list-p-faddl))))

(defthmd cmul-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (natp k)
                (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pshift x k f) f)
	          (pshift (cmul c x f) k f)))
  :hints (("Goal" :use (pshift-rewrite polyp-cmul-*
                        (:instance pshift-rewrite (x (cmul c x f)))
                        (:instance cmul-append (l x) (m (fzero-list k f)))))))                

(defthmd monomial-rewrite
  (implies (natp k)
           (equal (monomial c k f)
	          (cons c (fzero-list k f))))
  :hints (("Goal" :use ((:instance pshift-rewrite-1 (x (list c)))))))

;; If k > 0, then by monomial-rewrite, the definition of pmul, and pstrip-fzero-list,

;;   (monomial c k f) * y = (cons c (fzero-list k f)) * y
;;                        = (pshift (cmul c y f) k f) + (pstrip (fzero-list k f) f) * y
;;                        = (pshift (cmul c y f) k f) + (pzero f) * y
;;                        = (pshift (cmul c y f) k f).

(local-defthmd hack-2
  (implies (consp x) (posp (len x))))

(in-theory (disable monomial))

(local-defthmd pmul-monomial-1
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (posp k)
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c k f) y f)
	          (padd (pshift (cmul c y f) k f)
		        (pmul (pzero f) y f)
			f)))
  :hints (("Goal" :in-theory (enable pzero monomial-rewrite)  
                  :use (consp-fzero-list))))

(local-defthmd pmul-monomial-2
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (posp k) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (polyp (pshift (cmul c y f) k f) f))
  :hints (("Goal" :in-theory (e/d (pzero polyp) (polyp-cmul-*))
                  :use ((:instance polyp-cmul-* (x y))
		        (:instance polyp-pshift (x (cmul c y f)))
			(:instance field-integral-domain-* (x c) (y (car y)))))))

(local-defthmd pmul-monomial-3
  (implies (and (fieldp f) (field-axioms-p f)
                (posp k) (feltp c f) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c k f) y f)
	          (pshift (cmul c y f) k f)))
  :hints (("Goal" :in-theory (enable pmul-monomial-1)
                  :use (pmul-monomial-2))))

(local-defthmd pmul-monomial-4
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c 0 f) y f)
	          (pshift (cmul c y f) 0 f)))		  
  :hints (("Goal" :in-theory (enable pzero monomial-rewrite))))

(defthmd pmul-monomial-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (feltp c f) (not (equal c (fzero f)))
                (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (monomial c k f) y f)
	          (pshift (cmul c y f) k f)))
  :hints (("Goal" :use (pmul-monomial-3 pmul-monomial-4))))


;;---------
;; Closure
;;---------

(defun pmul-induct (x y f)
  (if (or (equal x (pzero f)) (equal y (pzero f)))
      ()
    (if (and (consp x) (consp (cdr x)))
        (pmul-induct (pstrip (cdr x) f) y f)
      ())))

(local-defthm polyp-pstrip-3
  (implies (and (fieldp f) (polyp x f) (consp (cdr x)))
           (polyp (pstrip (cdr x) f) f))
  :hints (("Goal" :in-theory (enable polyp) :use ((:instance polyp-pstrip (x (cdr x)))))))

(local-defthm pmul-closed-step
  (implies (and (fieldp f) (field-axioms-p f)
                (not (equal y (pzero f)))
                (polyp x f) (polyp y f) (consp (cdr x))
		(polyp (pmul (pstrip (cdr x) f) y f) f))
	   (polyp (pmul x y f) f))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (disable padd-closed-* polyp-pshift polyp-cmul-*)
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (len (cdr x))))
		        (:instance polyp-cmul-* (c (car x)) (x y))
			(:instance cmul-nonzero (c (car x)) (x y))
			(:instance padd-closed-* (x (PSHIFT (CMUL (CAR X) Y F) (LEN (CDR X)) F)) (y (PMUL (PSTRIP (CDR X) F) Y F)))))))

(defthm pmul-closed-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (polyp (pmul x y f) f))
  :hints (("Goal" :induct (pmul-induct x y f))
          ("Subgoal *1/3" :use ((:instance polyp-def (p x))
	                        (:instance polyp-def (p y))
				(:instance polyp-cmul-* (c (car x)) (x y))))))


;;---------------------
;; Degree of Remainder
;;---------------------

(defthmd polyp-x1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (>= (degree y) 1)
		(polyp x f) (>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (m (monomial c (- (degree x) (degree y)) f))
	          (x1 (padd x (pneg (pmul m y f) f) f)))
	     (and (polyp m f) (polyp x1 f))))
  :hints (("Goal" :in-theory (disable frecip-not-fzero-* feltp-frecip-* fmul-closed-* polyp-monomial pmul-closed-* polyp-pneg-* padd-closed-*)
                  :use ((:instance polyp-def (p x))
                        (:instance polyp-def (p y))
			(:instance frecip-not-fzero-* (x (car y)))
			(:instance feltp-frecip-* (x (car y)))
			(:instance field-integral-domain-* (x (car x)) (y (frecip (car y) f)))
			(:instance fmul-closed-* (x (car x)) (y (frecip (car y) f)))
			(:instance polyp-monomial (c (fmul (car x) (frecip (car y) f) f)) (k (- (degree x) (degree y))))
			(:instance pmul-closed-* (x (monomial (fmul (car x) (frecip (car y) f) f) (- (degree x) (degree y)) f)))
			(:instance polyp-pneg-* (x (pmul (monomial (fmul (car x) (frecip (car y) f) f) (- (degree x) (degree y)) f) y f)))
			(:instance padd-closed-* (y (pneg (pmul (monomial (fmul (car x) (frecip (car y) f) f) (- (degree x) (degree y)) f) y f) f)))))))

(local-defthmd degree-prem-2
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (gpolyp y f)
                (= (len x) (len y)) (>= (len x) 2)
		(equal (car y) (fneg (car x) f)))
	   (< (len (pstrip (faddl x y f) f))
	      (len x)))
  :hints (("Goal" :use (len-faddl
                        (:instance len-pstrip (x (CDR (FADDL X Y F)))))
                  :expand ((pstrip (faddl x y f) f)))))

(local-defthmd degree-prem-3
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp x f) (feltp y f) (not (equal y (fzero f))))
	   (equal (fmul (fmul x (frecip y f) f) y f)
	          x))
  :hints (("Goal" :use ((:instance fmul-comm-* (x (frecip y f)))
		        (:instance fmul-assoc-* (y (frecip y f)) (z y))))))

(local-defthm car-pneg
  (implies (consp x)
           (equal (car (pneg x f))
	          (fneg (car x) f))))

(local-defthmd degree-prem-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (p (pshift (cmul c y f) (- (degree x) (degree y)) f)))
             (equal (car (pneg p f)) (fneg (car x) f))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance frecip-not-fzero-* (x (car y)))
			(:instance degree-prem-3 (x (car x)) (y (car y)))
		        (:instance field-integral-domain-* (x (car x)) (y (frecip (car y) f)))))))

(local-defthmd degree-prem-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (p (pshift (cmul c y f) (- (degree x) (degree y)) f))
                  (x1 (padd x (pneg p f) f)))
             (< (len x1) (len x))))
  :hints (("Goal" :in-theory (enable gpolyp-pneg padd polyp)
                  :use (degree-prem-4
		        (:instance frecip-not-fzero-* (x (car y)))
			(:instance field-integral-domain-* (x (car x)) (y (frecip (car y) f)))
			(:instance len-cmul (c (fmul (car x) (frecip (car y) f) f)) (x y))
		        (:instance degree-prem-2 (y (pneg (pshift (cmul (fmul (car x) (frecip (car y) f) f) y f)
			                                          (- (degree x) (degree y))
								  f)
							  f)))))))

(local-defthmd degree-prem-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (>= (degree y) 1)
		(polyp x f) (>= (degree x) (degree y)))
	   (let ((c (fmul (car x) (frecip (car y) f) f)))
	     (and (feltp c f)
	          (not (equal c (fzero f))))))
  :hints (("Goal" :in-theory (disable frecip-not-fzero-* feltp-frecip-* fmul-closed-* polyp-monomial pmul-closed-* polyp-pneg-* padd-closed-*)
                  :use ((:instance polyp-def (p x))
                        (:instance polyp-def (p y))
			(:instance frecip-not-fzero-* (x (car y)))
			(:instance feltp-frecip-* (x (car y)))
			(:instance field-integral-domain-* (x (car x)) (y (frecip (car y) f)))
			(:instance fmul-closed-* (x (car x)) (y (frecip (car y) f)))))))

(defthmd degree-decreasing
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (m (monomial c (- (degree x) (degree y)) f))
                  (x1 (padd x (pneg (pmul m y f) f) f)))
             (< (len x1) (len x))))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (degree-prem-5 degree-prem-6
                        (:instance pmul-monomial-* (k (- (degree x) (degree y))) (c (fmul (car x) (frecip (car y) f) f)))))))

(defun pdivide-induct (x y f)
  (declare (xargs :measure (len x) :hints (("Goal" :use (degree-decreasing)))))
  (if (and (fieldp f) (field-axioms-p f)
           (polyp x f) (polyp y f) (>= (degree y) 1)
           (>= (degree x) (degree y)))
      (let* ((c (fmul (car x) (frecip (car y) f) f))
             (m (monomial c (- (degree x) (degree y)) f))
             (x1 (padd x (pneg (pmul m y f) f) f)))
        (pdivide-induct x1 y f))
    ()))

(defthmd degree-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (and (polyp (prem x y f) f)
	        (< (degree (prem x y f))
		   (degree y))))
  :hints (("Goal" :induct (pdivide-induct x y f)) 
          ("Subgoal *1/1" :in-theory (enable prem) :use (polyp-x1 degree-decreasing pdivide))
          ("Subgoal *1/2" :in-theory (enable prem) :use (polyp-x1 degree-decreasing pdivide))))
	   

;;---------------------------------------------
;; Degree and Leading Coefficient of a Product
;;---------------------------------------------

(local-defthmd degree-pmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (not (equal x (pzero f)))
                (not (equal y (pzero f)))
                (polyp x f) (polyp y f) (consp (cdr x))
		(equal (degree (pmul (pstrip (cdr x) f) y f))
		       (+ (degree (pstrip (cdr x) f))
		          (degree y))))
	   (equal (degree (pmul x y f))
	          (+ (degree x) (degree y))))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (disable polyp-pshift polyp-cmul-*)
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (len (cdr x))))
		        (:instance polyp-cmul-* (c (car x)) (x y))
			(:instance cmul-nonzero (c (car x)) (x y))
		        (:instance degree-padd-diff-* (x (pshift (cmul (car x) y f) (degree x) f)) (y (pmul (pstrip (cdr x) f) y f)))
		        (:instance len-pstrip (x (cdr x)))))))

(local-defthmd degree-pmul-2
  (implies (and (fieldp f) (field-axioms-p f)
                (not (equal x (pzero f)))
                (not (equal y (pzero f)))
                (polyp x f) (polyp y f) (consp (cdr x))
		(equal (pstrip (cdr x) f) (pzero f)))
	   (equal (degree (pmul x y f))
	          (+ (degree x) (degree y))))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (disable polyp-pshift polyp-cmul-*)
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (len (cdr x))))
		        (:instance polyp-cmul-* (c (car x)) (x y))
			(:instance cmul-nonzero (c (car x)) (x y))))))

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
	          (+ (degree x) (degree y))))
  :hints (("Goal" :induct (pmul-induct x y f))  
          ("Subgoal *1/2" :in-theory (enable pzero) :expand ((pmul x y f)) :use ((:instance polyp-def (p x))))
          ("Subgoal *1/1" :use (degree-pmul-1 degree-pmul-2))))

(defthm pmul-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (not (equal (pmul x y f) (pzero f))))
  :hints (("Goal" :cases ((and (pconstp x) (pconstp y)))
                  :in-theory (enable pzero)
		  :expand ((cmul (car x) y f) (len y) (len x) (len (cdr x)) (len (cdr y)))
                  :use (degree-pmul-*
		        (:instance polyp-def (p x))
		        (:instance polyp-def (p y))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))))))

(defthm car-pneg
  (implies (consp x)
           (equal (car (pneg x f))
	          (fneg (car x) f))))

(defthm car-padd
  (implies (and (fieldp f) (polyp x f) (polyp y f) (< (degree y) (degree x)))
           (equal (car (padd x y f))
	          (car x)))
  :hints (("Goal" :in-theory (enable padd)
                  :use ((:instance polyp-def (p x))))))

(local-defthmd car-pmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (equal (degree (pshift (cmul (car x) y f) (degree x) f))
	          (+ (degree x) (degree y))))
  :hints (("Goal" :in-theory (e/d (pzero) (len-cmul len-pshift))
                  :use ((:instance polyp-def (p x))
		        (:instance len-cmul (c (car x)) (x y))
		        (:instance len-pshift (x (cmul (car x) y f)) (k (degree x)))))))

(local-defthmd car-pmul-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (< (degree (pmul (pstrip (cdr x) f) y f))
	      (+ (degree x) (degree y))))
  :hints (("Goal" :in-theory (e/d (pzero) (pmul-pzero))
                  :use ((:instance degree-pmul-* (x (pstrip (cdr x) f)))
                        (:instance pmul-pzero (x y))
			(:instance polyp-def (p y))
                        (:instance len-pstrip (x (cdr x)))))))

(local-defthmd car-pmul-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (polyp (pshift (cmul (car x) y f) (degree x) f) f))
  :hints (("Goal" :in-theory (enable pzero)
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-def (p y))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))
		        (:instance polyp-cmul-* (c (car x)) (x y))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (len (cdr x))))))))

(local-defthmd car-pmul-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (equal (car (pmul x y f))
	          (car (pshift (cmul (car x) y f) (degree x) f))))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (e/d (pzero) (car-padd))
                  :use (car-pmul-1 car-pmul-2 car-pmul-3	  
		        (:instance car-padd (x (pshift (cmul (car x) y f) (degree x) f)) (y (pmul (pstrip (cdr x) f) y f)))))))

(local-defthmd car-pmul-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (equal (car (pshift (cmul (car x) y f) (degree x) f))
	          (fmul (car x) (car y) f)))
  :hints (("Goal" :in-theory (e/d (car-cmul) (car-padd))
                  :use (car-pmul-4
		        (:instance polyp-def (p y))
		        (:instance car-cmul (c (car x)) (x y))))))

(local-defthmd car-pmul-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (equal (car (pmul x y f))
	          (car (pshift (cmul (car x) y f) (degree x) f))))
  :hints (("Goal" :use (car-pmul-1 car-pmul-4 car-pmul-5))))

(local-defthmd car-pmul-7
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (consp (cdr x)))
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f)))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (e/d (pzero) (car-cmul))
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-def (p y))
		        (:instance car-cmul (c (car x)) (x y))))))

(local-defthmd car-pmul-8
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(or (equal x (pzero f))
		    (equal y (pzero f))))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f)))
  :hints (("Goal" :expand ((pmul x y f))
                  :in-theory (enable pzero)		  
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-def (p y))))))

(defthmd car-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f)))
  :hints (("Goal" :use (car-pmul-5 car-pmul-6 car-pmul-7 car-pmul-8))))


;;----------------------
;; Distributivity
;;----------------------

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
           (polyp (head x f) f))
  :hints (("Goal" :in-theory (enable pzero head)
                  :use ((:instance polyp-monomial (c (car x)))
                        (:instance polyp-def (p x))))))

(defthm polyp-tail
  (implies (and (fieldp f) (polyp x f) (consp (cdr x)))
           (polyp (tail x f) f))
  :hints (("Goal" :in-theory (enable tail polyp-pstrip))))

(defthmd len-tail
  (implies (consp x)
           (< (len (tail x f)) (len x)))
  :hints (("Goal" :in-theory (enable tail))))
           
  

;; we have an alternative expression for x':

(defun fzero-list (k f)
  (if (zp k)
      ()
    (cons (fzero f) (fzero-list (1- k) f))))

(local-defthm gpolyp-fzero-list
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (gpolyp (fzero-list k f) f)))

(defthm len-fzero-list
  (implies (natp k)
           (equal (len (fzero-list k f))
	          k)))

(defthmd consp-fzero-list
  (implies (posp k)
           (consp (fzero-list k f)))
  :hints (("Subgoal *1/3" :expand ((fzero-list 1 f)))))

(defthm pstrip-fzero-list
  (implies (posp k)
           (equal (pstrip (fzero-list k f) f)
                  (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))
          ("Subgoal *1/3" :expand ((fzero-list 1 f)))))

(defun fzero-list-p (l f)
  (if (consp l)
      (and (equal (car l) (fzero f))
           (fzero-list-p (cdr l) f))
    t))

(local-defthmd pstrip-fzero-list-p
  (implies (and (gpolyp l f) (fzero-list-p l f) (consp l))
           (equal (pstrip l f) (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd pstrip-fzero-list-converse
  (implies (and (gpolyp x f)  (equal (pstrip x f) (pzero f)))
           (fzero-list-p x f))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd fzero-list-p-cmul
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (feltp c f) (not (equal c (fzero f))))
	   (iff (fzero-list-p (cmul c x f) f)
	        (fzero-list-p x f)))
  :hints (("Subgoal *1/2" :expand ((CMUL C X F))
                          :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(local-defthm faddl-fzero-list
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (equal (faddl (fzero-list k f) (fzero-list k f) f)
	          (fzero-list k f))))

(local-defthmd head-rewrite-1
  (implies (and (true-listp x) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f)))))

(defthm true-listp-gpolyp
  (implies (gpolyp x f)
           (true-listp x)))

(defthmd pshift-rewrite
  (implies (and (polyp x f) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f))))
  :hints (("Goal" :in-theory (enable polyp) :use (head-rewrite-1))))

(defthmd head-rewrite
  (implies (polyp x f)
           (equal (head x f)
	          (cons (car x) (fzero-list (degree x) f))))
  :hints (("Goal" :in-theory (enable monomial polyp head)
                  :use ((:instance head-rewrite-1 (x (list (car x))) (k (degree x)))))))

;; x = x' + x":

(local-defthmd pdecomp-1
  (implies (and (fieldp f) (field-axioms-p f) (gpolyp x f))
           (equal (faddl (fzero-list (len x) f) x f)
	          x)))

(local-defthmd pdecomp-2
  (implies (and (fieldp f) (field-axioms-p f) (gpolyp x f))
           (equal (faddl (fzero-list (len x) f)
	                 (pstrip x f)
			 f)
	          x))
  :hints (("Subgoal *1/3" :use ((:instance pdecomp-1 (x (cdr x)))))
          ("Subgoal *1/2" :in-theory (disable len-fzero-list)
	                  :expand ((FADDL (CONS (CAR X) (FZERO-LIST (LEN (CDR X)) F)) (PSTRIP (CDR X) F) F))
	                  :use ((:instance len-pstrip (x (cdr x)))
	                        (:instance len-fzero-list (k (len (cdr x))))))))

(local-defthmd pdecomp-3
  (implies (and (fieldp f) (field-axioms-p f) (polyp x f) (consp (cdr x)))
           (equal (faddl (head x f) (tail x f) f)
	          x))
  :hints (("Goal" :in-theory (enable tail polyp head-rewrite)
                  :expand ((FADDL (CONS (CAR X) (FZERO-LIST (LEN (CDR X)) F)) (PSTRIP (CDR X) F) F))
                  :use ((:instance len-pstrip (x (cdr x)))
		        (:instance pdecomp-2 (x (cdr x)))))))

(defthmd pdecomp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x)))
	   (equal (padd (head x f) (tail x f) f)
		  x))
  :hints (("Goal" :in-theory (enable padd polyp)
                  :use (pdecomp-3))))

;; By head-rewrite, the definition of pmul, and pstrip-fzero-list,

;;   x' * y = (cons (car x) (fzero-list (degree x) f)) * y
;;          = (pshift (cmul (car x) y f) (degree x) f) + (pstrip (fzero-list (degree x) f) f) * y
;;          = (pshift (cmul (car x) y f) (degree x) f) + (pzero f) * y
;;          = (pshift (cmul (car x) y f) (degree x) f).

(local-defthmd hack-2
  (implies (consp x) (posp (len x))))

(local-defthmd pmul-head-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (head x f) y f)
	          (padd (pshift (cmul (car x) y f) (degree x) f)
		        (pmul (pzero f) y f)
			f)))
  :hints (("Goal" :in-theory (enable pzero head-rewrite)
                  :use ((:instance consp-fzero-list (k (len (cdr x))))
		        (:instance hack-2 (x (cdr x)))))))

(local-defthmd pmul-head-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (polyp (pshift (cmul (car x) y f) (degree x) f) f))
  :hints (("Goal" :in-theory (e/d (pzero polyp) (polyp-cmul-*))
                  :use ((:instance polyp-cmul-* (c (car x)) (x y))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (degree x)))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))))))

(defthmd pmul-head
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (head x f) y f)
	          (pshift (cmul (car x) y f) (degree x) f)))
  :hints (("Goal" :in-theory (enable pmul-head-1)
                  :use (pmul-head-2))))

;; By the definition of pmul,

;;    x * y = x' * y + x" * y:

(local-defthmd pdistrib-pdecomp-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul x y f)
	          (padd (pmul (head x f) y f)
			(pmul (tail x f) y f)
			f)))
  :hints (("Goal" :in-theory (enable pzero tail pmul-head)
                  :expand ((PMUL X Y F)))))

(local-defthmd pdistrib-pdecomp-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x)))
	   (equal (pmul x (pzero f) f)
	          (padd (pmul (head x f) (pzero f) f)
			(pmul (tail x f) (pzero f) f)
			f))))

(defthmd pdistrib-pdecomp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f))
	   (equal (pmul x y f)
	          (padd (pmul (head x f) y f)
			(pmul (tail x f) y f)
			f)))
  :hints (("Goal" :use ( pdistrib-pdecomp-1  pdistrib-pdecomp-2))))

;; Claim: x' * (y + z) = x' * y + x' * z:

(local-defthmd cmul-faddl
  (implies (and (fieldp f) (field-axioms-p f)
		(gpolyp x f) (gpolyp y f) (feltp c f))
	   (equal (cmul c (faddl x y f) f)
	          (faddl (cmul c x f) (cmul c y f) f)))
  :hints (("Goal" :induct (fadd-comm-induct x y))
          ("Subgoal *1/3" :expand ((faddl x y f))
	                  :use ((:instance fdistrib-* (x c) (y (car x)) (z (car y)))))))

(local-defthmd pstrip-cmul
  (implies (and (fieldp f) (field-axioms-p f)
		(gpolyp x f) (feltp c f) (not (equal c (fzero f))))
	   (equal (pstrip (cmul c x f) f)
	          (cmul c (pstrip x f) f)))
  :hints (("Subgoal *1/3" :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(defthmd pmul-head-rewrite
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f))))
	   (equal (pmul (head x f) y f)
	          (append (cmul (car x) y f) (fzero-list (degree x) f))))
  :hints (("Goal" :use (pmul-head
                        (:instance polyp (p x))
                        (:instance polyp-cmul-* (c (car x)) (x y))
                        (:instance pshift-rewrite (x (cmul (car x) y f)) (k (degree x)))))))

(local-defthmd pdistrib-head-1
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pstrip (faddl (append (cmul (car x) y f) (fzero-list (degree x) f))
		                 (append (cmul (car x) z f) (fzero-list (degree x) f))
				 f)
			  f)))
  :hints (("Goal" :in-theory (enable padd)
                  :use (pmul-head-rewrite
		        (:instance polyp-def (p x))
                        (:instance polyp-cmul-* (c (car x)) (x y))
                        (:instance polyp-cmul-* (c (car x)) (x z))
                        (:instance pmul-head-rewrite (y z))
			(:instance polyp (p (cmul (car x) y f)))
			(:instance polyp (p (cmul (car x) z f)))))))

(local-defthmd pdistrib-head-2
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (equal (faddl (append (cmul (car x) y f) (fzero-list (degree x) f))
		         (append (cmul (car x) z f) (fzero-list (degree x) f))
		         f)
	          (append (faddl (cmul (car x) y f) (cmul (car x) z f) f)
		          (fzero-list (degree x) f))))
  :hints (("Goal" ;:in-theory (enable padd)
                  :use ((:instance polyp-cmul-* (c (car x)) (x y))
                        (:instance polyp-cmul-* (c (car x)) (x z))
		        (:instance polyp-def (p x))
			(:instance polyp (p (cmul (car x) y f)))
			(:instance polyp (p (cmul (car x) z f)))
			(:instance faddl-append (x (cmul (car x) y f)) (y (cmul (car x) z f)) (z (fzero-list (degree x) f)))))))

(local-defthmd pdistrib-head-3
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (equal (faddl (cmul (car x) y f) (cmul (car x) z f) f)
	          (cmul (car x) (faddl y z f) f)))
  :hints (("Goal" ;:in-theory (enable polyp)
                  :use ((:instance polyp (p y))
			(:instance polyp (p z))
		        (:instance polyp-def (p x))
			(:instance cmul-faddl (c (car x)) (x y) (y z))))))

(local-defthmd pdistrib-head-4
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pstrip (append (cmul (car x) (faddl y z f) f)
		                  (fzero-list (degree x) f))
			  f)))
  :hints (("Goal" :use (pdistrib-head-1 pdistrib-head-2 pdistrib-head-3))))

(local-defthmd pdistrib-head-5
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (iff (equal (padd y z f) (pzero f))
	        (fzero-list-p (cmul (car x) (faddl y z f) f) f)))
  :hints (("Goal" :in-theory (enable polyp padd)
                  :use ((:instance gpolyp-faddl (x y) (y z))
		        (:instance pstrip-fzero-list-p (l (faddl y z f)))
			(:instance fzero-list-p-cmul (c (car x)) (x (faddl y z f)))
		        (:instance pstrip-fzero-list-converse (x (faddl y z f)))))))

(local-defthmd pdistrib-head-6
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (and (gpolyp (cmul (car x) (faddl y z f) f) f)
	        (gpolyp (fzero-list (degree x) f) f)
		(consp (cmul (car x) (faddl y z f) f))
		(consp (fzero-list (degree x) f))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance polyp-cmul-* (c (car x)) (x (faddl y z f)))
			(:instance consp-fzero-list (k (degree x)))
			(:instance len (x (cdr x)))
			(:instance gpolyp-faddl (x y) (y z))))))

(local-defthmd pdistrib-head-7
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (equal (padd y z f) (pzero f)))
	   (equal (pstrip (append (cmul (car x) (faddl y z f) f)
		                  (fzero-list (degree x) f))
			  f)
	          (pstrip (fzero-list (degree x) f) f)))
  :hints (("Goal" :use (pdistrib-head-5 pdistrib-head-6
                        (:instance pstrip-append (x (cmul (car x) (faddl y z f) f))
                                                 (y (fzero-list (degree x) f)))))))

(local-defthmd pdistrib-head-8
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (equal (padd y z f) (pzero f)))
	   (equal (pstrip (fzero-list (degree x) f) f)
	          (pzero f)))		  
  :hints (("Goal" :use ((:instance len (x (cdr x)))
                        (:instance pstrip-fzero-list (k (degree x)))))))

(local-defthmd pdistrib-head-9
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (equal (padd y z f) (pzero f)))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pmul (head x f) (padd y z f) f)))
  :hints (("Goal" :use (pdistrib-head-4 pdistrib-head-7 pdistrib-head-8))))

(local-defthmd pdistrib-head-10
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (not (equal (padd y z f) (pzero f))))
	   (equal (pstrip (append (cmul (car x) (faddl y z f) f)
		                  (fzero-list (degree x) f))
			  f)
	          (append (pstrip (cmul (car x) (faddl y z f) f) f)
			  (fzero-list (degree x) f))))
  :hints (("Goal" :use (pdistrib-head-5 pdistrib-head-6
                        (:instance pstrip-append (x (cmul (car x) (faddl y z f) f))
                                                 (y (fzero-list (degree x) f)))))))

(local-defthmd pdistrib-head-11
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (not (equal (padd y z f) (pzero f))))
	   (equal (pstrip (cmul (car x) (faddl y z f) f) f)
		  (cmul (car x) (padd y z f) f)))
  :hints (("Goal" :in-theory (enable padd polyp)
		  :use ((:instance gpolyp-faddl (x y) (y z))
                        (:instance pstrip-cmul (c (car x)) (x (faddl y z f)))))))

(local-defthmd pdistrib-head-12
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f)))
	        (not (equal (padd y z f) (pzero f))))
	   (equal (append (cmul (car x) (padd y z f) f)
			  (fzero-list (degree x) f))
		  (pmul (head x f) (padd y z f) f)))
  :hints (("Goal" :use ((:instance pmul-head-rewrite (y (padd y z f)))))))

(local-defthmd pdistrib-head-13
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (not (equal y (pzero f)))
		(polyp z f) (not (equal z (pzero f))))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pmul (head x f) (padd y z f) f)))
  :hints (("Goal" :use (pdistrib-head-4 pdistrib-head-9 pdistrib-head-10 pdistrib-head-11 pdistrib-head-12))))

(local-defthmd pdistrib-head-14
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f)
		(or (equal y (pzero f)) (equal z (pzero f))))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pmul (head x f) (padd y z f) f)))
  :hints (("Goal" :in-theory (disable polyp-head pzero pmul-closed-* pzero-id-*)
                  :expand ((pzero f))
                  :use (polyp-head
		        (:instance pzero-id-* (x (pmul (head x f) y f)))
		        (:instance pzero-id-* (x (pmul (head x f) z f)))
		        (:instance pzero-id-2-* (x (pmul (head x f) y f)))
		        (:instance pzero-id-2-* (x (pmul (head x f) z f)))
		        (:instance pzero-id-* (x y))
		        (:instance pzero-id-* (x z))
		        (:instance pzero-id-2-* (x y))
		        (:instance pzero-id-2-* (x z))
		        (:instance pmul-closed-* (x (head x f)))
		        (:instance pmul-closed-* (x (head x f)) (y z))))))

(defthmd pdistrib-head
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f))
	   (equal (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
	          (pmul (head x f) (padd y z f) f)))
  :hints (("Goal" :use (pdistrib-head-13 pdistrib-head-14))))


;; Thus,

;;     x * (y + z) = x' * (y + z) + x" * (y + z)
;;                 = (x' * y + x' * z) + (x" * y + x" * z)
;; 	 	   = (x' * y + x" * y) + (x' * z + x" * z)
;; 		   = x * y + x * z.

(local-defthmd pdistrib-*-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f)
		(equal (pmul (tail x f) (padd y z f) f)
		       (padd (pmul (tail x f) y f) (pmul (tail x f) z f) f)))
	   (equal (pmul x (padd y z f) f)
	          (padd (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
		        (padd (pmul (tail x f) y f) (pmul (tail x f) z f) f)
			f)))
  :hints (("Goal" :use (pdistrib-head
                        (:instance pdistrib-pdecomp (y (padd y z f)))))))

(local-defthm consp-cdr-not-pzero
  (implies (consp (cdr x))
           (not (equal x (pzero f))))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd pdistrib-*-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x)) (not (equal x (pzero f)))
		(polyp y f) (polyp z f))
	   (equal (padd (padd (pmul (head x f) y f) (pmul (head x f) z f) f)
		        (padd (pmul (tail x f) y f) (pmul (tail x f) z f) f)
			f)
		  (padd (padd (pmul (head x f) y f) (pmul (tail x f) y f) f)
		        (padd (pmul (head x f) z f) (pmul (tail x f) z f) f)
			f)))
  :hints (("Goal" :use ((:instance padd-assoc-* (x (padd (pmul (head x f) y f) (pmul (head x f) z f) f)) (y (pmul (tail x f) y f)) (z (pmul (tail x f) z f)))
                        (:instance padd-assoc-* (x (pmul (head x f) y f)) (y (pmul (head x f) z f)) (z (pmul (tail x f) y f)))
			(:instance padd-comm-* (x (pmul (head x f) z f)) (y (pmul (tail x f) y f)))
			(:instance padd-assoc-* (x (pmul (head x f) y f)) (y (pmul (tail x f) y f)) (z (pmul (head x f) z f)))
			(:instance padd-assoc-* (x (padd (pmul (head x f) y f) (pmul (tail x f) y f) f)) (y (pmul (head x f) z f)) (z (pmul (tail x f) z f)))))))

(local-defthmd pdistrib-*-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f))
	   (equal (padd (padd (pmul (head x f) y f) (pmul (tail x f) y f) f)
		        (padd (pmul (head x f) z f) (pmul (tail x f) z f) f)
			f)
		  (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :use (pdistrib-pdecomp (:instance pdistrib-pdecomp (y z))))))

(local-defthmd pdistrib-induction-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (consp (cdr x))
		(polyp y f) (polyp z f)
		(equal (pmul (tail x f) (padd y z f) f)
		       (padd (pmul (tail x f) y f) (pmul (tail x f) z f) f)))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (pdistrib-*-1 pdistrib-*-2 pdistrib-*-3))))

;;---------------------------------------------------------------------------------------------------------

;; We must prove distributivity in the case (not (consp (cdr x))).

;; First suppose x = 0 or y = 0 or z = 0:

(local-defthmd pdistrib-*-5
  (implies (or (equal x (pzero f)) (equal y (pzero f)))
           (equal (pmul x y f) (pzero f))))

(local-defthmd pdistrib-*-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
                (or (equal x (pzero f)) (equal y (pzero f)) (equal z (pzero f))))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :in-theory (enable pdistrib-*-5))))

;; We may assume x, y, and z are nonzero.

;; Suppose x + y is nonzero:
	   
(defthmd pmul-constant
  (implies (and (polyp x f) (not (consp (cdr x)))
		(polyp y f) (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pmul x y f)
	          (cmul (car x) y f)))		  
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd cmul-pstrip-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pstrip x f) f)
	          (pstrip (cmul c x f) f)))
  :hints (("Subgoal *1/3" :use ((:instance field-integral-domain-* (x c) (y (car x)))))))

(defthmd cmul-pstrip
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pstrip x f) f)
	          (pstrip (cmul c x f) f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (cmul-pstrip-1))))

(defthmd cmul-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
		(polyp x f) (polyp y f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (padd x y f) f)
	          (padd (cmul c x f) (cmul c y f) f)))
  :hints (("Goal" :in-theory (enable cmul-pstrip-1 gpolyp-faddl padd cmul-faddl polyp))))

(local-defthmd pdistrib-*-8
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(polyp y f) (polyp z f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f)))
		(not (equal z (pzero f)))
		(not (equal (padd y z f) (pzero f))))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :in-theory (e/d (pmul-constant cmul-padd-*) (cmul))
                  :use (polyp-car-nonzero))))

;; Finally, assume x + y = 0.  Then x = (pneg y):

(defthmd pneg-unique-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (equal (padd x y f) (pzero f)))
	   (equal (pneg y f) x))
  :hints (("Goal" :in-theory (enable padd-pneg-*)
                  :use ((:instance padd-assoc-* (z (pneg y f)))))))

(local-defthmd pneg-padd-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (padd (padd x y f) (padd (pneg x f) (pneg y f) f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable padd-pneg-*)
                  :use ((:instance padd-assoc-* (x (padd x y f)) (y (pneg x f)) (z (pneg y f)))
                        (:instance padd-assoc-* (z (pneg x f)))
			(:instance padd-comm-* (x (pneg x f)))
			(:instance padd-assoc-* (y (pneg x f)) (z y))))))

(local-defthmd pneg-padd-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (padd (padd (pneg x f) (pneg y f) f) (padd x y f) f)
	          (pzero f)))
  :hints (("Goal" :use (pneg-padd-1
                        (:instance padd-comm-* (x (padd (pneg x f) (pneg y f) f)) (y (padd x y f)))))))

(defthmd pneg-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pneg (padd x y f) f)
	          (padd (pneg x f) (pneg y f) f)))
  :hints (("Goal" :use (pneg-padd-2
                        (:instance pneg-unique-* (x (padd (pneg x f) (pneg y f) f)) (y (padd x y f)))))))

(local-defthmd pneg-cmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (cmul c x f) f)
	          (cmul c (pneg x f) f)))
  :hints (("Goal" :induct (len x))
          ("Subgoal *1/1" :expand ((CMUL C X F) (pneg x f))
	                  :use ((:instance fneg-fmul-* (x c) (y (car x)))))))

(defthmd pneg-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (cmul c x f) f)
	          (cmul c (pneg x f) f)))
  :hints (("Goal" :use (pneg-cmul-1) :in-theory (enable polyp))))

;; I don't think I need pneg-pshift after all:

(local-defthmd pneg-pshift-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pshift (cmul c (pneg x f) f) k f)
	          (pshift (pneg (cmul c x f) f) k f)))
  :hints (("Goal" :use (pneg-cmul-*))))

(local-defthmd pneg-pshift-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pshift (pneg (cmul c x f) f) k f)
	          (append (pneg (cmul c x f) f) (fzero-list k f))))
  :hints (("Goal" :in-theory (enable pshift-rewrite polyp-cmul-*))))

(defthm pneg-fzero-list-*
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (equal (pneg (fzero-list k f) f)
	          (fzero-list k f)))
  :hints (("Subgoal *1/4" :use ((:instance fneg-fzero-* (x (fzero f)))))))

(local-defthmd pneg-pshift-3
  (implies (and (fieldp f) (field-axioms-p f) (natp k))
           (equal (append (pneg x f) (fzero-list k f))
	          (pneg (append x (fzero-list k f)) f)))
  :hints (("Goal" :induct (len x))))

(local-defthmd pneg-pshift-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pshift (cmul c x f) k f)
	          (append (cmul c x f) (fzero-list k f))))
  :hints (("Goal" :in-theory (enable pshift-rewrite polyp-cmul-*))))

(defthmd pneg-pshift-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (pshift (cmul c x f) k f) f)
	          (pshift (cmul c (pneg x f) f) k f)))
  :hints (("Goal" :use (pneg-pshift-1 pneg-pshift-2 pneg-pshift-4
                        (:instance pneg-pshift-3 (x (cmul c x f)))))))

(local-defthmd pneg-pneg-gpoly
  (implies (and (fieldp f) (field-axioms-p f)
                (gpolyp x f))
	   (equal (pneg (pneg x f) f)
	          x))
  :hints (("Goal" :induct (len x))))

(defthmd pneg-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pneg (pneg x f) f)
	          x))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (pneg-pneg-gpoly))))

(defthm pneg-pzero-*
  (implies (and (fieldp f) (field-axioms-p f))
           (equal (pneg (pzero f) f) (pzero f)))
  :hints (("Goal" :use ((:instance pneg-unique-* (x (pzero f)) (y (pzero f)))))))
  

(defthmd pneg-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f)
	        (equal (pneg x f) (pzero f)))
	   (equal (pzero f) x))
  :hints (("Goal" :use (pneg-pneg-*))))



(local-defthmd pneg-pmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (consp (cdr x)))
		(polyp y f) (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pneg (pmul x y f) f)
	          (pmul x (pneg y f) f)))
  :hints (("Goal" :in-theory (disable pmul pneg cmul)
                  :use (pmul-constant polyp-car-nonzero
		        (:instance pmul-constant (y (pneg y f)))
		        (:instance pneg-nonzero-* (x y))
		        (:instance polyp-def (p x))
			(:instance pneg-cmul-* (x y) (c (car x)))))))

(local-defthmd pdistrib-*-9
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(polyp y f) (polyp z f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f)))
		(not (equal z (pzero f)))
		(equal (padd y z f) (pzero f)))
	   (equal (padd (pmul x y f) (pmul x z f) f)
	          (padd (pmul x (pneg z f) f) (pmul x z f) f)))
  :hints (("Goal" :use ((:instance pneg-unique-* (x y) (y z))))))

(local-defthmd pdistrib-*-10
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(polyp y f) (polyp z f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f)))
		(not (equal z (pzero f)))
		(equal (padd y z f) (pzero f)))
	   (equal (padd (pmul x (pneg z f) f) (pmul x z f) f)
	          (padd (pneg (pmul x z f) f) (pmul x z f) f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance pneg-pmul-1 (y z))))))

(local-defthmd pdistrib-*-11
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp z f))
	   (equal (padd (pneg (pmul x z f) f) (pmul x z f) f)
	          (pzero f)))		  
  :hints (("Goal" :in-theory (enable padd-pneg-*) :use ((:instance padd-comm-* (x (pneg (pmul x z f) f)) (y (pmul x z f)))))))

(local-defthmd pdistrib-*-12
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(polyp y f) (polyp z f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f)))
		(not (equal z (pzero f)))
		(equal (padd y z f) (pzero f)))
	   (equal (padd (pmul x y f) (pmul x z f) f)
	          (pmul x (padd y z f) f)))
  :hints (("Goal" :use (pdistrib-*-9 pdistrib-*-10 pdistrib-*-11))))

;; Put it all together:

(defthmd pdistrib-base-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(polyp y f) (polyp z f))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :use (pdistrib-*-6 pdistrib-*-8 pdistrib-*-12))))

;; Induction scheme:

(defun pdistrib-induct (x f)
  (declare (xargs :measure (len x) :hints (("Goal" :in-theory (enable tail) :use ((:instance len-pstrip (x (cdr x))))))))
  (if (consp x)
      (if (consp (cdr x))
          (pdistrib-induct (tail x f) f)
	())
    ()))

(defthmd pdistrib-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :induct (pdistrib-induct x f))
          ("Subgoal *1/3" :use (pdistrib-base-case))
          ("Subgoal *1/2" :use (pdistrib-base-case))
          ("Subgoal *1/1" :use (pdistrib-induction-case))))


;;----------------------
;; Commutativity
;;----------------------

(defthmd pmul-pzero-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(or (equal x (pzero f)) (equal y (pzero f))))
	   (equal (pmul x y f) (pmul y x f))))

;; If x and y are constants, then by pmul-constant,

;;    x * y = (cmul (car x) y f) = (list (fmul (car x) (car y) f)):

(defthmd pmul-constants
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))) (not (consp (cdr y))))
	   (equal (pmul x y f) (list (fmul (car x) (car y) f))))
  :hints (("Goal" :use ((:instance polyp-def (p x))
                        (:instance polyp-def (p y))))))

(defthmd pmul-constants-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))) (not (consp (cdr y))))
	   (equal (pmul x y f) (pmul y x f)))
  :hints (("Goal" :use ((:instance fmul-comm-* (x (car x)) (y (car y)))(:instance polyp-def (p x))
                        (:instance polyp-def (p y))))))

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
	          (cons (fmul c d f) (fzero-list (+ k l) f))))
  :hints (("Goal" :in-theory (enable pzero monomial-rewrite)
                  :use ((:instance pmul-monomial-* (y (monomial d l f)))
		        (:instance polyp-monomial (c d) (k l))
		        (:instance polyp-monomial (c (fmul c d f)) (k l))
			(:instance field-integral-domain-* (x c) (y d))
			(:instance pshift-rewrite (x (CONS (FMUL C D F) (FZERO-LIST L F))))))))

(defthmd pmul-monomials-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (feltp d f) (not (equal d (fzero f)))
		(natp k) (natp l))
	   (equal (pmul (monomial c k f) (monomial d l f) f)
	          (pmul (monomial d l f) (monomial c k f) f)))
  :hints (("Goal" :in-theory (enable pmul-monomials)
                  :use ((:instance fmul-comm-* (x c) (y d))))))

;; If x is a constant, then

;;    (monomial c k f) * x = (pshift (cmul c x f) k f)
;;                         = (append (cmul c x f) (fzero-list k f))
;;                         = (append (list (fmul c (car x) f)) (fzero-list k f))
;;                         = (cons (fmul c (car x) f) (fzero-list k f))

(local-defthmd pmul-constant-monomial-comm-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (not (consp (cdr x)))
		(not (equal x (pzero f)))
		(feltp c f) (not (equal c (fzero f)))
		(natp k))
	   (equal (pmul (monomial c k f) x f)
	          (cons (fmul c (car x) f) (fzero-list k f))))
  :hints (("Goal" :expand ((cmul c x f))
                  :use (polyp-cmul-*
                        (:instance pmul-monomial-* (y x))
			(:instance polyp-def (p x))
                        (:instance pshift-rewrite (x (cmul c x f)))))))
		  
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
	          (pmul (monomial c k f) x f)))
  :hints (("Goal" :in-theory (enable polyp pzero pmul-constant monomial-rewrite)
                  :use (pmul-constant-monomial-comm-1
		        (:instance cmul (x (car x)) (p (cons c (fzero-list k f))))))))

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

(local-defthmd pmul-constant-comm-inductive-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x)))
		(consp (cdr y))
		(equal (pmul x (tail y f) f) (pmul (tail y f) x f)))
	   (equal (pmul x y f) (pmul y x f)))
  :hints (("Goal" :in-theory (enable head)
                  :use ((:instance pdecomp (x y))
		        (:instance polyp-head (x y))
			(:instance polyp-def (p y))
                        (:instance pdistrib-* (y (head y f)) (z (tail y f)))
			(:instance pmul-constant-monomial-comm (c (car y)) (k (degree y)))
			(:instance pdistrib-pdecomp (x y) (y x))))))

(defthmd pmul-constant-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(not (consp (cdr x))))
	   (equal (pmul x y f) (pmul y x f)))
  :hints (("Goal" :induct (tail-induct y f))
          ("Subgoal *1/2" :use (pmul-constants-comm))
	  ("Subgoal *1/1" :use (pmul-constant-comm-inductive-case))))

;;   x' * y = x' * (y' + y")         [pdecomp]
;;          = x' * y' + x' * y"      [pdistrib]
;;          = y' * x' + y" * x'      [pmul-monomials-comm, induction]
;;          = y * x'                 [pdistrib-pdecomp]

(local-defthmd pmul-head-comm-inductive-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(consp (cdr x))
		(consp (cdr y))
		(equal (pmul (head x f) (tail y f) f) (pmul (tail y f) (head x f) f)))
	   (equal (pmul (head x f) y f) (pmul y (head x f) f)))
  :hints (("Goal" :in-theory (enable head)
                  :use ((:instance pdecomp (x y))
		        (:instance polyp-head (x y))
			(:instance polyp-def (p x))
			(:instance polyp-def (p y))
                        (:instance pdistrib-* (x (head x f)) (y (head y f)) (z (tail y f)))
			(:instance pmul-monomials-comm (c (car y)) (k (degree y)) (d (car x)) (l (degree x)))
			(:instance pdistrib-pdecomp (x y) (y (head x f)))))))

(defthmd pmul-head-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(consp (cdr x)))
	   (equal (pmul (head x f) y f) (pmul y (head x f) f)))
  :hints (("Goal" :induct (tail-induct y f))
          ("Subgoal *1/2" :use ((:instance pmul-constant-comm (x y) (y (head x f)))))
	  ("Subgoal *1/1" :use (pmul-head-comm-inductive-case))))

;;   x * y = x * (y' + y")     [pdecomp]
;;         = x * y' + x * y"   [pdistrib]
;;         = y' * x + y" * x   [pmul-head-comm, induction]
;;         = y * x             [pdistrib-pdecomp]

(local-defthmd pmul-comm-inductive-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(consp (cdr y))
		(equal (pmul x (tail y f) f) (pmul (tail y f) x f)))
	   (equal (pmul x y f)
	          (pmul y x f)))
  :hints (("Goal" :in-theory (enable head)
                  :use ((:instance pdecomp (x y))
		        (:instance polyp-head (x y))
			(:instance polyp-def (p x))
			(:instance polyp-def (p y))
                        (:instance pdistrib-* (y (head y f)) (z (tail y f)))
			(:instance pmul-head-comm (x y) (y x))
			(:instance pdistrib-pdecomp (x y) (y x))))))

(defthmd pmul-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pmul x y f)
	          (pmul y x f)))
  :hints (("Goal" :induct (tail-induct y f))
          ("Subgoal *1/2" :use ((:instance pmul-constant-comm (x y) (y x))))
	  ("Subgoal *1/1" :use (pmul-comm-inductive-case))))

(defthmd pdistrib-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul (padd y z f) x f)
	          (padd (pmul y x f) (pmul z x f) f)))
  :hints (("Goal" :use (pdistrib-* pmul-comm-*
                        (:instance pmul-comm-* (y (padd y z f)))
                        (:instance pmul-comm-* (y z))))))

(defthm pone-id-2-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (equal (pmul x (pone f) f)
	          x))
  :hints (("Goal" :use ((:instance pmul-comm-* (y (pone f)))))))


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

(local-defthmd cmul-pmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (polyp (pshift (cmul (car x) y f) (degree x) f) f))
  :hints (("Goal" :in-theory (enable pzero)
                  :expand ((cmul (car x) y f))
                  :use ((:instance polyp-def (p x))
		        (:instance polyp-def (p y))
		        (:instance polyp-cmul-* (c (car x)) (x y))
		        (:instance polyp-cmul-* (c (car x)) (x y))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))
		        (:instance polyp-pshift (x (cmul (car x) y f)) (k (degree x)))))))

(local-defthmd cmul-pmul-2
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f))))
	   (polyp (pmul (pstrip (cdr x) f) y f) f))
  :hints (("Goal" :in-theory (enable pzero polyp-pstrip))))

(local-defthmd cmul-pmul-3
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f)
	          (padd (cmul c (pshift (cmul (car x) y f) (degree x) f) f)
                        (cmul c (pmul (pstrip (cdr x) f) y f) f)
			f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :expand ((pmul x y f))
                  :use (cmul-pmul-1 cmul-pmul-2
		        (:instance cmul-padd-* (x (pshift (cmul (car x) y f) (degree x) f))
                                             (y (pmul (pstrip (cdr x) f) y f)))))))

(local-defthmd cmul-pmul-4
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f)
	          (padd (cmul c (pshift (cmul (car x) y f) (degree x) f) f)
                        (cmul c (pmul (pstrip (cdr x) f) y f) f)
			f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (cmul-pmul-3))))

(local-defthmd cmul-pmul-5
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f))))
	   (equal (cmul c (pshift (cmul (car x) y f) (degree x) f) f)
	          (pshift (cmul (car (cmul c x f)) y f) (degree (cmul c x f)) f)))
  :hints (("Goal" :in-theory (enable cmul-cmul-*)
                  :use ((:instance cmul-pshift-* (x (cmul (car x) y f)) (k (degree x)))
                        (:instance polyp-def (p x))
		        (:instance polyp-cmul-* (c (car x)) (x y))))))

(local-defthmd cmul-pmul-6
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f))))
	   (equal (cmul c (pstrip (cdr x) f) f)
	          (pstrip (cdr (cmul c x f)) f)))
  :hints (("Goal" :in-theory (enable polyp cmul-pstrip-1))))

(local-defthmd cmul-pmul-7
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f)))
		(equal (cmul c (pmul (pstrip (cdr x) f) y f) f)
		       (pmul (cmul c (pstrip (cdr x) f) f) y f)))
	   (equal (cmul c (pmul x y f) f)
	          (padd (pshift (cmul (car (cmul c x f)) y f) (degree (cmul c x f)) f)
		        (pmul (pstrip (cdr (cmul c x f)) f) y f)
			f)))
  :hints (("Goal" :use (cmul-pmul-4 cmul-pmul-5 cmul-pmul-6))))

(local-defthmd hack-3
  (implies (and (not (equal c (fzero f))))
           (iff (consp (cdr x))
	        (consp (cdr (cmul c x f)))))
  :hints (("Goal" :expand ((CMUL C X F) (cmul c (cdr x) f)))))

(local-defthmd cmul-pmul-8
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (consp (cdr x))
		(not (equal y (pzero f)))
		(equal (cmul c (pmul (pstrip (cdr x) f) y f) f)
		       (pmul (cmul c (pstrip (cdr x) f) f) y f)))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :use (cmul-pmul-7 hack-3))))
           
(local-defthmd cmul-pmul-9
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (not (consp (cdr x)))
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f) 
	          (cmul (car (cmul c x f)) y f)))
  :hints (("Goal" :in-theory (enable pzero cmul-cmul-*)
                  :expand ((cmul c x f))
                  :use ((:instance polyp-def (p x))))))

(local-defthmd cmul-pmul-10
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (not (consp (cdr x)))
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f) 
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (cmul-pmul-9 hack-3))))

(local-defthmd cmul-pmul-11
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pmul (pzero f) y f) f) 
	          (pmul (cmul c (pzero f) f) y f)))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd cmul-pmul-12
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f) (polyp y f) (not (consp (cdr x)))
		(not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f) 
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :use (cmul-pmul-10 cmul-pmul-11))))

(local-defthmd cmul-pmul-13
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (polyp x f) (polyp y f)
		(not (equal y (pzero f))))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :induct (pmul-induct x y f))
          ("Subgoal *1/3" :use (cmul-pmul-12))
          ("Subgoal *1/2" :use (cmul-pmul-8))
          ("Subgoal *1/1" :in-theory (enable pzero))))

(defthmd cmul-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :use (cmul-pmul-13) :in-theory (enable pzero))))

;; A special case of cmul-pmul:

(defthmd pmul-const
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(polyp x f))
	   (equal (pmul (list c) x f)
	          (cmul c x f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (pzero-id-2-*))))

(defthmd pmul-const-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (pmul (list c) (pmul x y f) f)
	          (pmul (pmul (list c) x f) y f)))
  :hints (("Goal" :in-theory (enable cmul-pmul-*)
                  :use (pmul-const
                        (:instance pmul-const (x (pmul x y f)))))))

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

(local-defthmd pshift-pmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (consp (cdr x))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (polyp-car-nonzero
		        (:instance cmul-pshift-* (c (car x)) (x y))
		        (:instance polyp-def (p x))))))

(local-defthmd pshift-pmul-2
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pshift (pmul x y f) k f)
	          (padd (pshift (pshift (cmul (car x) y f) (degree x) f) k f)
                        (pshift (pmul (pstrip (cdr x) f) y f) k f)
                        f)))
  :hints (("Goal" :in-theory (enable pzero polyp-pstrip)
                  :use (pmul-nonzero-*
		        (:instance polyp-def (p x))
		        (:instance polyp-def (p y))
		        (:instance padd-pshift-* (x (pshift (cmul (car x) y f) (degree x) f))
			                       (y (pmul (pstrip (cdr x) f) y f)))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))
			(:instance polyp-pshift (x (cmul (car x) y f)) (k (degree x)))
		        (:instance polyp-cmul-* (c (car x)) (x y))))))

(local-defthmd pshift-pmul-3
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pshift (pshift (cmul (car x) y f) (degree x) f) k f)
	          (pshift (cmul (car x) y f) (+ (degree x) k) f)))
  :hints (("Goal" :in-theory (enable pzero polyp-pstrip)
                  :use ((:instance pshift-pshift (x (cmul (car x) y f)) (k (degree x)) (l k))
		        (:instance polyp-def (p x))
		        (:instance polyp-cmul-* (c (car x)) (x y))))))

(local-defthmd pshift-pmul-4
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pshift (cmul (car x) y f) (+ (degree x) k) f)
	          (cmul (car x) (pshift y (+ (degree x) k) f) f)))
  :hints (("Goal" :use ((:instance polyp-def (p x))
		        (:instance cmul-pshift-* (c (car x)) (x y) (k (+ (degree x) k)))))))

(local-defthmd pshift-pmul-5
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pshift y (+ (degree x) k) f)
	          (pshift (pshift y k f) (degree x) f)))
  :hints (("Goal" :use ((:instance pshift-pshift (x y) (l (degree x)))))))

(local-defthmd pshift-pmul-6
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (cmul (car x) (pshift (pshift y k f) (degree x) f) f)
	          (pshift (cmul (car x) (pshift y k f) f)(degree x) f)))
  :hints (("Goal" :use ((:instance polyp-def (p x))
			(:instance polyp-pshift (x y))
                        (:instance cmul-pshift-* (c (car x)) (x (pshift y k f)) (k (degree x)))))))

(local-defthmd pshift-pmul-7
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pshift (pmul (pstrip (cdr x) f) y f) k f)
		       (pmul (pstrip (cdr x) f) (pshift y k f) f)))
           (equal (pshift (pmul x y f) k f)
                  (padd (pshift (cmul (car x) (pshift y k f) f) (degree x) f)
                        (pmul (pstrip (cdr x) f) (pshift y k f) f)
                        f)))
  :hints (("Goal" :use (pshift-pmul-2 pshift-pmul-3 pshift-pmul-4 pshift-pmul-5 pshift-pmul-6))))

(local-defthmd pshift-pmul-8
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pshift (pmul (pstrip (cdr x) f) y f) k f)
		       (pmul (pstrip (cdr x) f) (pshift y k f) f)))
           (equal (pshift (pmul x y f) k f)
                  (pmul x (pshift y k f) f)))
  :hints (("Goal" :use (pshift-pmul-7 (:instance pshift-nonzero (x y)))
                  :expand ((pmul x (pshift y k f) f)))))

(local-defthmd pshift-pmul-9
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pstrip (cdr x) f) (pzero f)))
	   (equal (pshift (pmul x y f) k f)
	          (pshift (pshift (cmul (car x) y f) (degree x) f) k f)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use ((:instance pzero-id-2-* (x (pshift (cmul (car x) y f) (degree x) f)))
		        (:instance polyp-def (p x))
		        (:instance polyp-def (p y))
			(:instance field-integral-domain-* (x (car x)) (y (car y)))
			(:instance polyp-pshift (x (cmul (car x) y f)) (k (degree x)))
		        (:instance polyp-cmul-* (c (car x)) (x y))))))

(local-defthmd pshift-pmul-10
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pstrip (cdr x) f) (pzero f)))
	   (equal (pshift (pmul x y f) k f)
	          (pshift (cmul (car x) (pshift y k f) f) (degree x) f)))
  :hints (("Goal" :use (pshift-pmul-9 pshift-pmul-3 pshift-pmul-4 pshift-pmul-5 pshift-pmul-6))))

(local-defthmd pshift-pmul-11
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pstrip (cdr x) f) (pzero f)))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f)))
  :hints (("Goal" :use (pshift-pmul-10
                        (:instance pshift-nonzero (x y)))
		  :expand ((pmul x (pshift y k f) f)))))

(defthmd pshift-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f)))
  :hints (("Goal" :induct (pmul-induct x y f))
          ("Subgoal *1/2" :use (pshift-pmul-1
	                        (:instance polyp-def (p x))
	                        (:instance pshift-nonzero (x y))))
	  ("Subgoal *1/1" :use (pshift-pmul-11 pshift-pmul-8))))

;; Combine pshift-pmul with pmul-comm-*:

(defthmd pshift-pmul-comm
  (implies (and (fieldp f) (field-axioms-p f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul (pshift x k f) y f)))
  :hints (("Goal" :use (pmul-comm-* polyp-pshift
                        (:instance pshift-pmul-* (x y) (y x))			
			(:instance pmul-comm-* (x (pshift x k f)))))))


;; Let c != (fzero f) and m = (monomial c k f) = (pshift (list c) k f).

;;    (pmul (pmul m x f) y f) = (pmul (pmul (pshift (list c) k f) x f) y f)
;;                            = (pmul (pshift (pmul (list c) x f) k f) y f)   [pshift-pmul-comm]
;;                            = (pshift (pmul (pmul (list c) x f) y f) k f)   [pshift-pmul-comm]
;;                            = (pshift (pmul (list c) (pmul x y f) f) k f)   [pmul-const-assoc]
;;                            = (pmul (pshift (list c) k f) (pmul x y f) f)   [pshift-pmul-comm]
;;                            = (pmul m (pmul x y f) f)

(local-defthmd pmul-monomial-assoc-1
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(not (equal x (pzero f))) (not (equal y (pzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (let ((m (monomial c k f)))
	     (equal (pmul (pmul m x f) y f)
	            (pmul (pshift (pmul (list c) x f) k f) y f))))
  :hints (("Goal" :in-theory (enable polyp pzero monomial)
                  :use (pmul-const-assoc
                        (:instance pshift-pmul-comm (x (list c)) (y x))))))

(local-defthmd pmul-monomial-assoc-2
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(not (equal x (pzero f))) (not (equal y (pzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (equal (pmul (pshift (pmul (list c) x f) k f) y f)
	          (pshift (pmul (pmul (list c) x f) y f) k f)))
  :hints (("Goal" :in-theory (enable polyp pzero monomial)
                  :use ((:instance pmul-nonzero-* (y (list c)))
		        (:instance field-integral-domain-* (x c) (y (car x)))
                        (:instance pshift-pmul-comm (x (pmul (list c) x f)))))))

(local-defthmd pmul-monomial-assoc-3
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(not (equal x (pzero f))) (not (equal y (pzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (equal (pshift (pmul (pmul (list c) x f) y f) k f)
	          (pshift (pmul (list c) (pmul x y f) f) k f)))
  :hints (("Goal" :in-theory (enable polyp pzero monomial)
                  :use (pmul-const-assoc
		        (:instance pmul-nonzero-* (y (list c)))
		        (:instance field-integral-domain-* (x c) (y (car x)))))))

(local-defthmd pmul-monomial-assoc-4
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
		(not (equal x (pzero f))) (not (equal y (pzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (equal (pshift (pmul (list c) (pmul x y f) f) k f)
	          (pmul (pshift (list c) k f) (pmul x y f) f)))
  :hints (("Goal" :in-theory (enable polyp pzero monomial)
                  :use (pmul-nonzero-*
                        (:instance pshift-pmul-comm (x (list c)) (y (pmul x y f)))
		        (:instance field-integral-domain-* (x c) (y (car x)))))))

(defthmd pmul-monomial-assoc
  (implies (and (fieldp f) (field-axioms-p f)
                (feltp c f) (not (equal c (fzero f)))
                (natp k) (polyp x f) (polyp y f))
	   (let ((m (monomial c k f)))
	     (equal (pmul (pmul m x f) y f)
	            (pmul m (pmul x y f) f))))
  :hints (("Goal" :in-theory (enable monomial)
                  :use (pmul-monomial-assoc-1 pmul-monomial-assoc-2 pmul-monomial-assoc-3 pmul-monomial-assoc-4))))

;; If z is a constant, then

;;    (x * y) * z = z * (x * y) = z * (y * x) = (z * y) * x = x * (z * y) = x * (y * z).

;; Assume z is not constant and (x * y) * z" = x * (y * z").  Then

;;    (x * y) * z = (x * y) * (z' + z")
;;                = (x * y) * z' + (x * y) * z"
;;                = x * (y * z') + x * (y * z")
;;                = x * (y * z' + y * z")
;;                = x * (y * (z' + z"))
;;                = x * (y * z)

(local-defthmd pmul-assoc-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (consp (cdr z))))
           (equal (pmul x (pmul y z f) f)
	          (pmul (pmul x y f) z f)))
  :hints (("Goal" :use (pmul-comm-*
                        (:instance polyp-def (p z))
                        (:instance pmul-const-assoc (c (car z)) (x y) (y x))
			(:instance pmul-comm-* (x (pmul x y f)) (y z))
			(:instance pmul-comm-* (x z))
			(:instance pmul-comm-* (y (pmul z y f)))
			(:instance pmul-comm-* (x z))))))

(local-defthmd pmul-assoc-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (consp (cdr z))
		(equal (pmul x (pmul y (tail z f) f) f)
	               (pmul (pmul x y f) (tail z f) f)))
           (equal (pmul (pmul x y f) z f)
	          (padd (pmul (pmul x y f) (head z f) f)
		        (pmul (pmul x y f) (tail z f) f)
			f)))
  :hints (("Goal" :use ((:instance pdecomp (x z))
                        (:instance pdistrib-* (x (pmul x y f)) (y (head z f)) (z (tail z f)))))))

(local-defthmd pmul-assoc-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (consp (cdr z))
		(equal (pmul x (pmul y (tail z f) f) f)
	               (pmul (pmul x y f) (tail z f) f)))
           (equal (padd (pmul (pmul x y f) (head z f) f)
		        (pmul (pmul x y f) (tail z f) f)
			f)
	          (padd (pmul x (pmul y (head z f) f) f)
		        (pmul x (pmul y (tail z f) f) f)
			f)))
  :hints (("Goal" :in-theory (e/d (head monomial) (polyp-head))
                  :use (pmul-comm-*
		        (:instance polyp-def (p z))
			(:instance polyp-head (x z))
                        (:instance pmul-comm-* (x (head z f)) (y (pmul x y f)))
                        (:instance pmul-comm-* (y (pmul (head z f) y f)))
                        (:instance pmul-comm-* (x (head z f)))
			(:instance pmul-monomial-assoc (c (car z)) (k (degree z)) (x y) (y x))))))

(local-defthmd pmul-assoc-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (consp (cdr z))
		(equal (pmul x (pmul y (tail z f) f) f)
	               (pmul (pmul x y f) (tail z f) f)))
           (equal (padd (pmul x (pmul y (head z f) f) f)
		        (pmul x (pmul y (tail z f) f) f)
			f)
		  (pmul x (padd (pmul y (head z f) f) (pmul y (tail z f) f) f) f)))
  :hints (("Goal" :in-theory (e/d (head monomial) (polyp-head))
                  :use ((:instance polyp-def (p z))
			(:instance polyp-head (x z))
                        (:instance pdistrib-* (y (pmul y (head z f) f)) (z (pmul y (tail z f) f)))))))

(local-defthmd pmul-assoc-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (consp (cdr z))
		(equal (pmul x (pmul y (tail z f) f) f)
	               (pmul (pmul x y f) (tail z f) f)))
           (equal (padd (pmul y (head z f) f) (pmul y (tail z f) f) f)
	          (pmul y z f)))
  :hints (("Goal" :in-theory (e/d (head monomial) (polyp-head))
                  :use ((:instance pdecomp (x z))
		        (:instance polyp-def (p z))
			(:instance polyp-head (x z))
                        (:instance pdistrib-* (x y) (y (head z f)) (z (tail z f)))))))

(local-defthmd pmul-assoc-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (consp (cdr z))
		(equal (pmul x (pmul y (tail z f) f) f)
	               (pmul (pmul x y f) (tail z f) f)))
           (equal (pmul (pmul x y f) z f)
	          (pmul x (pmul y z f) f)))
  :hints (("Goal" :use (pmul-assoc-2 pmul-assoc-3 pmul-assoc-4 pmul-assoc-5))))
                        
(defthmd pmul-assoc-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f))
           (equal (pmul x (pmul y z f) f)
	          (pmul (pmul x y f) z f)))
  :hints (("Goal" :induct (tail-induct z f))
          ("Subgoal *1/2" :use (pmul-assoc-1))
          ("Subgoal *1/1" :use (pmul-assoc-6))))


;;-------------------------------------------------
;; Multiplication by the Negative of a Polynomial
;;------------------------------------------------

(local-defthmd pneg-pmul-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pmul (head x f) (pneg y f) f)
	          (pneg (pmul (head x f) y f) f)))
  :hints (("Goal" :use (pmul-head
                        (:instance pmul-head (y (pneg y f)))
			(:instance polyp-def (p x))
			(:instance pneg-nonzero-* (x y))
                        (:instance pneg-pshift-* (c (car x)) (k (degree x)) (x y))))))

(local-defthmd pneg-pmul-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))) (consp (cdr x)))
	   (equal (pmul x (pneg y f) f)
	          (padd (pmul (head x f) (pneg y f) f)
	                (pmul (tail x f) (pneg y f) f)
			f)))
  :hints (("Goal" :use (pdecomp
                        (:instance pdistrib-pdecomp (y (pneg y f)))))))

(local-defthmd pneg-pmul-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pmul (tail x f) (pneg y f) f)
		       (pneg (pmul (tail x f) y f) f)))
	   (equal (pmul x (pneg y f) f)
	          (padd (pneg (pmul (head x f) y f) f)
	                (pneg (pmul (tail x f) y f) f)
			f)))
  :hints (("Goal" :use (pneg-pmul-2 pneg-pmul-3))))

(local-defthmd pneg-pmul-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pmul (tail x f) (pneg y f) f)
		       (pneg (pmul (tail x f) y f) f)))
	   (equal (pmul x (pneg y f) f)
	          (pneg (padd (pmul (head x f) y f)
	                      (pmul (tail x f) y f)
			      f)
			f)))
  :hints (("Goal" :use (pneg-pmul-4 (:instance pneg-padd-* (x (pmul (head x f) y f)) (y (pmul (tail x f) y f)))))))

(local-defthmd pneg-pmul-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))) (consp (cdr x))
		(equal (pmul (tail x f) (pneg y f) f)
		       (pneg (pmul (tail x f) y f) f)))
	   (equal (pmul x (pneg y f) f)
	          (pneg (pmul x y f) f)))
  :hints (("Goal" :use (pneg-pmul-5 pdistrib-pdecomp))))

(local-defthmd pneg-pmul-7
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (pmul x (pneg y f) f)
	          (pneg (pmul x y f) f)))
  :hints (("Goal" :induct (tail-induct x f))
          ("Subgoal *1/2" :use (pneg-pmul-1))
          ("Subgoal *1/1" :use (pneg-pmul-6))))

(defthmd pneg-pmul
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pmul x (pneg y f) f)
	          (pneg (pmul x y f) f)))
  :hints (("Goal" :use (pneg-pmul-7))))

(defthmd pmul-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (equal (pmul (pneg x f) y f)
	          (pneg (pmul x y f) f)))
  :hints (("Goal" :use (pmul-comm-*
                        (:instance pmul-comm-* (x (pneg x f)))
			(:instance pneg-pmul (x y) (y x))))))
  

;;---------------------
;; Polynomial Division
;;---------------------

(defund m (x y f)
  (let* ((c (fmul (car x) (frecip (car y) f) f))
         (m (monomial c (- (degree x) (degree y)) f)))
    m))

(defund x1 (x y f)
  (let* ((c (fmul (car x) (frecip (car y) f) f))
         (m (monomial c (- (degree x) (degree y)) f))
         (p (pmul m y f))
         (x1 (padd x (pneg p f) f)))
    x1))

(defund pdivide-alt (x y f)
  (declare (xargs :measure (len x)))
   (if (pconstp y)
       (mv (cmul (frecip (car y) f) x f) (pzero f))
     (if (< (degree x) (degree y))
         (mv (pzero f) x)
       (if (< (len (x1 x y f)) (len x))
           (mv-let (q r) (pdivide-alt (x1 x y f) y f)
	     (mv (padd q (m x y f) f) r))
         (mv () ())))))

(local-defthmd pdivide-alt-pdivide
  (equal (pdivide-alt x y f)
         (pdivide x y f))
  :hints (("Goal" :in-theory (enable pdivide-alt m x1))))

(defund pdivide-prop (x y f)
  (mv-let (q r) (pdivide-alt x y f)
    (and (polyp q f) (polyp r f)
	 (equal x (padd (pmul y q f) r f))
         (< (degree r) (degree y)))))

(local-defthmd equal-x1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (let* ((c (fmul (car x) (frecip (car y) f) f))
                  (p (pshift (cmul c y f) (- (degree x) (degree y)) f))
                  (x1 (padd x (pneg p f) f)))
 	     (equal (x1 x y f) x1)))
  :hints (("Goal" :in-theory (enable pzero monomial x1)
                  :use (degree-prem-5
		        (:instance polyp-def (p x))
		        (:instance polyp-def (p y))
			(:instance frecip-not-fzero-* (x (car y)))
			(:instance field-integral-domain-* (x (car x)) (y (frecip (car y) f)))
		        (:instance pmul-monomial-* (c (fmul (car x) (frecip (car y) f) f)) (k (- (degree x) (degree y))))))))

(local-defthmd len-x1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (< (len (x1 x y f)) (len x)))
  :hints (("Goal" :use (degree-prem-5 equal-x1))))

(local-defthmd pdivision-base-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(< (degree x) (degree y)))
	   (pdivide-prop x y f))
  :hints (("Goal" :in-theory (enable pdivide-prop pdivide-alt))))

(local-defthmd pdivision-inductive-case-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (and (polyp (m x y f) f)
	        (polyp (x1 x y f) f)
		(equal (x1 x y f)
		       (padd x (pneg (pmul (m x y f) y f) f) f))))
  :hints (("Goal" :in-theory (enable x1 m) :use (polyp-x1))))

(defund q1 (x y f)
  (pquot (x1 x y f) y f))

(defund r1 (x y f)
  (prem (x1 x y f) y f))

(local-defthmd pdivision-inductive-case-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y))
                (pdivide-prop (x1 x y f) y f))
	   (and (polyp (q1 x y f) f)
	        (polyp (r1 x y f) f)
		(equal (x1 x y f) (padd (pmul y (q1 x y f) f) (r1 x y f) f))
                (< (degree (r1 x y f)) (degree y))))
  :hints (("Goal" :in-theory (enable pdivide-alt-pdivide pdivide-prop pquot prem q1 r1))))

(local-defthmd pdivision-inductive-case-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
           (mv-let (q r) (pdivide-alt x y f)
	     (and (equal q (padd (q1 x y f) (m x y f) f))
	          (equal r (r1 x y f)))))
  :hints (("Goal" :in-theory (enable pquot prem  r1 q1 pdivide-alt)
                  :use (len-x1))
	  ("Subgoal 2.2" :in-theory (enable pdivide-alt-pdivide))
	  ("Subgoal 2.1" :in-theory (enable pdivide-alt-pdivide))))

(local-defthmd pdivision-inductive-case-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (equal (padd (x1 x y f) (pmul (m x y f) y f) f)
	          x))
  :hints (("Goal" :use (pdivision-inductive-case-1
                        (:instance padd-pneg-* (x (pmul (m x y f) y f)))
			(:instance padd-assoc-* (y (pneg (pmul (m x y f) y f) f)) (z (pmul (m x y f) y f)))
			(:instance padd-comm-* (x (pneg (pmul (m x y f) y f) f)) (y (pmul (m x y f) y f)))))))

(local-defthmd pdivision-inductive-case-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y))
                (pdivide-prop (x1 x y f) y f))
	   (equal (padd (pmul y (padd (q1 x y f) (m x y f) f) f) (r1 x y f) f)
	          x))
  :hints (("Goal" :use (pdivision-inductive-case-1 pdivision-inductive-case-2 pdivision-inductive-case-4
			(:instance padd-assoc-* (x (pmul y (q1 x y f) f)) (y (r1 x y f)) (z (pmul (m x y f) y f)))
			(:instance pmul-comm-* (x y) (y (m x y f)))
			(:instance padd-comm-* (x (r1 x y f)) (y (pmul y (m x y f) f)))
			(:instance padd-assoc-* (x (pmul y (q1 x y f) f)) (y (pmul y (m x y f) f)) (z (r1 x y f)))
			(:instance pdistrib-* (x y) (y (q1 x y f)) (z (m x y f)))))))

(local-defthmd pdivision-inductive-case
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1)
		(>= (degree x) (degree y)))
	   (and (polyp (x1 x y f) f)
	        (implies (pdivide-prop (x1 x y f) y f)
	                 (pdivide-prop x y f))))
  :hints (("Goal" :in-theory (enable pdivide-prop)
                  :use (pdivision-inductive-case-1 pdivision-inductive-case-2 pdivision-inductive-case-3 pdivision-inductive-case-5))))

(defun pdivide-alt-induct (x y f)
  (declare (xargs :measure (len x)
                  :hints (("Subgoal *1/4" :use (len-x1))
			  ("Subgoal *1/2" :use (len-x1))
			  ("Subgoal *1/1" :use (len-x1)))))
  (if (and (fieldp f) (field-axioms-p f)
           (polyp x f) (polyp y f) (>= (degree y) 1)
  	   (>= (degree x) (degree y)))
      (pdivide-alt-induct (x1 x y f) y f)
    ()))

(local-defthmd pdivision-alt
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (pdivide-prop x y f))
  :hints (("Goal" :induct (pdivide-induct x y f))  
          ("Subgoal *1/2" :use (pdivision-base-case))
          ("Subgoal *1/1" :in-theory (enable x1) :use (pdivision-inductive-case))))

(defthm pdivision-not-pconstp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (< (degree r) (degree y)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pdivide-prop pdivide-alt-pdivide)
                  :use (pdivision-alt))))

(local-defthm degree-pconstp
  (implies (polyp x f)
           (iff (pconstp x)
	        (equal (degree x) 0)))
  :hints (("Goal" :use ((:instance polyp-def (p x))))))

(in-theory (disable pconstp))

(local-defthmd degree-non-neg
  (implies (polyp x f)
           (not (equal (len x) 0)))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd pdivision-pconstp-1
  (implies (pconstp y)
           (and (equal (prem x y f) (pzero f))
	        (equal (pquot x y f)
	               (cmul (frecip (car y) f) x f))))
  :hints (("Goal" :expand ((pdivide x y f) (prem x y f) (PQUOT X y F)))))

(local-defthmd pdivision-pconstp-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (polyp x f) (not (equal y (pzero f))) (pconstp y))
	   (equal (pmul y (pquot x y f) f)
	          (cmul (car y) (cmul (frecip (car y) f) x f) f)))
  :hints (("Goal" :in-theory (enable pzero pdivision-pconstp-1)  
                  :use ((:instance pmul-constant (x y) (y (pquot x y f)))
		        (:instance polyp-def (p y))
		        (:instance polyp-cmul-* (c (frecip (car y) f)))
		        (:instance cmul-nonzero (c (frecip (car y) f)))))))

(local-defthmd pdivision-pconstp-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (polyp x f) (not (equal y (pzero f))) (pconstp y))
           (polyp (pquot x y f) f))
  :hints (("Goal" :in-theory (enable frecip-not-fzero-* pdivision-pconstp-1)  
                  :use ((:instance pmul-constant (x y) (y (pquot x y f)))
		        (:instance polyp-def (p y))
			(:instance polyp-car-nonzero (x y))
		        (:instance polyp-cmul-* (c (frecip (car y) f)))
		        (:instance cmul-nonzero (c (frecip (car y) f)))))))

(local-defthmd pdivision-pconstp-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (polyp x f) (not (equal y (pzero f))) (pconstp y))
	   (equal (cmul (car y) (cmul (frecip (car y) f) x f) f)
	          x))
  :hints (("Goal" :in-theory (enable polyp pzero pdivision-pconstp-1)  
                  :use ((:instance pmul-constant (y x) (x (pquot x y f)))
		        (:instance polyp-def (p y))
			(:instance frecip-not-fzero-* (x (car y)))
			(:instance cmul-cmul-* (c (car y)) (d (frecip (car y) f)))
		        (:instance cmul-nonzero (c (frecip (car y) f)))))))

(local-defthmd pdivision-pconstp-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (polyp x f) (pconstp y) (not (equal y (pzero f))))
           (and (equal (prem x y f) (pzero f))
	        (and (polyp (pquot x y f) f)
		     (equal (pmul y (pquot x y f) f)
	                    x))))
  :hints (("Goal" :use (pdivision-pconstp-1 pdivision-pconstp-2 pdivision-pconstp-3 pdivision-pconstp-4))))

(defthm pdivision-pconstp
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (equal r (pzero f)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable pdivide prem pquot)
                  :use (pdivision-pconstp-5))))

(defthm pdivision-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (mv-let (q r) (pdivide x y f)
	     (and (polyp q f) (polyp r f)
	          (equal x (padd (pmul y q f) r f))
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y))))))
  :rule-classes ()
  :hints (("Goal" :cases ((pconstp y))
                  :use (pdivision-not-pconstp pdivision-pconstp
                        (:instance degree-non-neg (x y))))))

(defthm pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (let ((q (pquot x y f)) (r (prem x y f)))
	     (and (polyp q f) (polyp r f)
	          (equal (padd (pmul y q f) r f) x)
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y))))))
  :hints (("Goal" :in-theory (enable pquot prem)
                  :use (pdivision-*))))

(defthm pconstp-prem-pzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
           (equal (prem x y f) (pzero f)))
  :hints (("Goal" :use (pquot-prem-*))))

(defthm polyp-pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (and (polyp (pquot x y f) f)
	        (polyp (prem x y f) f)))
  :hints (("Goal" :use (pdivision-*))))

;;------------------------------------------

;; Let Q and R denote (pquot x y f) and (prem x y f).  Then x = Q * y + R and (degree R) < (degree y).  Suppose we given polynomials
;; q and R such that x = q * y + r and (degree r) < (degree y).  Since Q * y + R = q * y + r, y * (Q - q) = r - R and the degree of
;; y * (Q - q) is less than (degree y), which implies Q - q = 0, q = Q, and r = R. 

(local-defthmd pquot-prem-unique-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (padd (padd (pmul y (pquot x y f) f)
	                      (prem x y f)
			      f)
			(pneg (prem x y f) f)
			f)
	          (pmul y (pquot x y f) f)))
  :hints (("Goal" :in-theory (enable padd-pneg-*)
                  :use ((:instance padd-assoc-* (x (pmul y (pquot x y f) f)) (y (prem x y f)) (z (pneg (prem x y f) f)))))))

(local-defthmd pquot-prem-unique-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f))
	   (equal (padd (padd (pmul y q f) r f)
	                (pneg (prem x y f) f)
			f)
		  (padd (padd r (pneg (prem x y f) f) f)
		        (pmul y q f)
			f)))
  :hints (("Goal" :use ((:instance padd-assoc-* (x (pmul y q f)) (y r) (z (pneg (prem x y f) f)))
                        (:instance padd-comm-* (x (pmul y q f)) (y (padd r (pneg (prem x y f) f) f)))))))

(local-defthmd pquot-prem-unique-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f)))
	   (equal (pmul y (pquot x y f) f)
	          (padd (padd r (pneg (prem x y f) f) f)
	                (pmul y q f)
			f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (pquot-prem-* pquot-prem-unique-1 pquot-prem-unique-2))))

(in-theory (enable padd-pneg-*))

(local-defthmd pquot-prem-unique-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f)))
           (equal (padd (pmul y (pquot x y f) f) (pneg (pmul y q f) f) f)
	          (padd r (pneg (prem x y f) f) f)))
  :hints (("Goal" :use (pquot-prem-unique-3
                        (:instance padd-assoc-* (x (padd r (pneg (prem x y f) f) f)) (y (pmul y q f)) (z (pneg (pmul y q f) f)))))))

(local-defthmd pquot-prem-unique-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f))
           (equal (padd (pmul y (pquot x y f) f) (pneg (pmul y q f) f) f)
	          (pmul y (padd (pquot x y f) (pneg q f) f) f)))
  :hints (("Goal" :use ((:instance pdistrib-* (x y) (y (pquot x y f)) (z (pneg q f)))
                        (:instance pneg-pmul (x y) (y q))))))

(local-defthmd pquot-prem-unique-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f)))
           (equal (padd r (pneg (prem x y f) f) f)
	          (pmul y (padd (pquot x y f) (pneg q f) f) f)))
  :hints (("Goal" :use (pquot-prem-unique-4 pquot-prem-unique-5))))

(local-defthmd polyp-degree-non-neg
  (implies (polyp x f)
           (>= (len x) 1))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd pquot-prem-unique-7
  (implies (and (fieldp f) (field-axioms-p f) (>= (degree y) 1)
		(polyp x f) (polyp y f) 
		(polyp q f) (polyp r f)
		(< (degree r) (degree y))
		(equal x (padd (pmul y q f) r f)))
           (< (degree (pmul y (padd (pquot x y f) (pneg q f) f) f))
	      (degree y)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (pquot-prem-unique-6 pquot-prem-*
                        (:instance degree-padd-bound-* (x r) (y (pneg (prem x y f) f)))))))

(local-defthmd pquot-prem-unique-8
  (implies (and (fieldp f) (field-axioms-p f) (>= (degree y) 1)
		(polyp x f) (polyp y f) 
		(polyp q f) (polyp r f)
		(< (degree r) (degree y))
		(equal x (padd (pmul y q f) r f)))
           (equal (padd (pquot x y f) (pneg q f) f)
	          (pzero f)))
  :hints (("Goal" :cases ((equal y (pzero f)))
                  :use (pquot-prem-unique-7
                        (:instance polyp-degree-non-neg (x (padd (pquot x y f) (pneg q f) f)))
			(:instance degree-pmul-* (x y) (y (padd (pquot x y f) (pneg q f) f)))))))

(local-defthmd pquot-prem-unique-9
  (implies (and (fieldp f) (field-axioms-p f) (>= (degree y) 1)
		(polyp x f) (polyp y f) 
		(polyp q f) (polyp r f)
		(< (degree r) (degree y))
		(equal x (padd (pmul y q f) r f)))
           (equal (pquot x y f) q))
  :hints (("Goal" :cases ((equal y (pzero f)))
                  :use (pquot-prem-unique-8 
                        (:instance pneg-pneg-* (x q))
			(:instance pneg-unique-* (x (pquot x y f)) (y (pneg q f)))))
	  ("Subgoal 1" :in-theory (enable pzero))))

(local-defthmd pquot-prem-unique-10
  (implies (and (fieldp f) (field-axioms-p f) (>= (degree y) 1)
		(polyp x f) (polyp y f) 
		(polyp q f) (polyp r f)
		(< (degree r) (degree y))
		(equal x (padd (pmul y q f) r f)))
           (equal (prem x y f) r))
  :hints (("Goal" :cases ((equal y (pzero f)))
                  :use (pquot-prem-unique-6 pquot-prem-unique-8 
                        (:instance pneg-pneg-* (x (prem x y f)))
			(:instance pneg-unique-* (x r) (y (pneg (prem x y f) f)))))
	  ("Subgoal 1" :in-theory (enable pzero))))

(local-defthmd pquot-prem-unique-11
  (implies (and (fieldp f) (field-axioms-p f) (pconstp y) (not (equal y (pzero f)))
		(polyp x f) (polyp y f) 
		(polyp q f)
		(equal x (pmul y q f)))
           (equal (padd (pquot x y f) (pneg q f) f)
	          (pzero f)))
  :hints (("Goal" :use (pquot-prem-*
                        (:instance field-integral-domain-* (x y) (y (padd (pquot x y f) (pneg q f) f)))
                        (:instance pquot-prem-unique-6 (r (pzero f)))))))

(local-defthmd pquot-prem-unique-12
  (implies (and (fieldp f) (field-axioms-p f) (pconstp y) (not (equal y (pzero f)))
		(polyp x f) (polyp y f) 
		(polyp q f)
		(equal x (pmul y q f)))
           (equal (pquot x y f) q))
  :hints (("Goal" :in-theory (enable pneg-pneg-*)
                  :use (pquot-prem-unique-11
                        (:instance pneg-unique-* (x (pquot x y f)) (y (pneg q f)))))))

(defthmd pquot-prem-unique-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f))
		(if (pconstp y)
		    (equal r (pzero f))
		  (< (degree r) (degree y))))
           (and (equal (pquot x y f) q)
	        (equal (prem x y f) r)))
  :hints (("Goal" :use (pquot-prem-* pquot-prem-unique-9 pquot-prem-unique-10 pquot-prem-unique-12))))


;;---------------------------------------------------------

(local-defthmd prem-padd-prem-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
           (equal (padd x y f)
                  (padd (pmul z (padd (pquot x z f) (pquot y z f) f) f)
                        (padd (prem x z f) (prem y z f) f)
                        f)))
  :hints (("Goal" :use ((:instance pquot-prem-* (y z))
                        (:instance pquot-prem-* (x y) (y z))
                        (:instance padd-assoc-* (x (padd (pmul z (pquot x z f) f) (prem x z f) f))
                                                (y (pmul z (pquot y z f) f))
                                                (z (prem y z f)))
                        (:instance padd-assoc-* (x (pmul z (pquot x z f) f))
                                                (y (prem x z f))
                                                (z (pmul z (pquot y z f) f)))
                        (:instance padd-comm-* (x (prem x z f)) (y (pmul z (pquot y z f) f)))
                        (:instance padd-assoc-* (x (pmul z (pquot x z f) f)) (y (pmul z (pquot y z f) f)) (z (prem x z f)))
                        (:instance padd-assoc-* (x (padd (pmul z (pquot x z f) f) (pmul z (pquot y z f) f) f))
                                                (y (prem x z f))
                                                (z (prem y z f)))
                        (:instance pdistrib-* (x z) (y (pquot x z f)) (z (pquot y z f)))))))

(local-defthmd prem-padd-prem-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
           (equal (padd x (prem y z f) f)
                  (padd (pmul z (pquot x z f) f)
                        (padd (prem x z f) (prem y z f) f)
                        f)))
 :hints (("goal" :use ((:instance pquot-prem-* (y z))
                       (:instance padd-assoc-* (x (pmul z (pquot x z f) f)) (y (prem x z f)) (z (prem y z f)))))))

(local-defthmd prem-padd-prem-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
           (equal (prem (padd x (prem y z f) f) z f)
                  (prem (padd x y f) z f)))
  :hints (("goal" :use (prem-padd-prem-1  prem-padd-prem-2
                       (:instance pquot-prem-* (y z))
                       (:instance pquot-prem-* (x y) (y z))
                       (:instance degree-padd-bound-* (x (prem x z f)) (y (prem y z f)))
                       (:instance pquot-prem-unique-* (y z)
                                                      (x (padd x y f))
                                                      (q (padd (pquot x z f) (pquot y z f) f))
                                                      (r (padd (prem x z f) (prem y z f) f)))
                       (:instance pquot-prem-unique-* (y z)
                                                      (x (padd x (prem y z f) f))
                                                      (q (pquot x z f))
                                                      (r (padd (prem x z f) (prem y z f) f)))))))

(defthmd prem-padd-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd x (prem y z f) f) z f)
                  (prem (padd x y f) z f)))
  :hints (("goal" :use (prem-padd-prem-3  (:instance polyp-degree-non-neg (x z))))))

(defthmd prem-padd-prem-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd (prem x z f) y f) z f)
                  (prem (padd x y f) z f)))
  :hints (("goal" :use (padd-comm-*
                        (:instance padd-comm-* (x (prem x z f)))
			(:instance prem-padd-prem-* (x y) (y x))))))


;;---------------------------------------------------------

(defthm len-pzero
  (equal (len (pzero f)) 1)
  :hints (("Goal" :in-theory (enable pzero))))

(defthmd prem-equal-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(< (degree x) (degree y)))
	   (equal (prem x y f)
	          x))
  :hints (("Goal" :use (polyp-degree-non-neg (:instance pquot-prem-unique-* (q (pzero f)) (r x))))))


;;---------------------------------------------------------

(defthmd prem+mult-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp a f))
	   (equal (prem (padd (pmul y a f) x f) y f)
	          (prem x y f)))
  :hints (("Goal" :use (pquot-prem-*
                        (:instance pquot-prem-unique-* (x (padd (pmul y a f) x f)) (q (padd a (pquot x y f) f)) (r (prem x y f)))
                        (:instance padd-assoc-* (x (pmul y a f)) (y (pmul y (pquot x y f) f)) (z (prem x y f)))
			(:instance pdistrib-* (x y) (y a) (z (pquot x y f)))))))
	          

;;---------------------------------------------------------

(local-defthmd prem-pmul-prem-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1))
	   (equal (pmul x y f)
	          (padd (pmul z
		              (padd (padd (pmul (pquot x z f) (pmul z (pquot y z f) f) f)
		                          (pmul (pquot x z f) (prem y z f) f)
					  f)
				    (pmul (pquot y z f) (prem x z f) f)
				    f)
			     f)
		       (pmul (prem x z f) (prem y z f) f)
		       f)))
  :hints (("Goal" :use ((:instance pquot-prem-* (y z))
                        (:instance pquot-prem-* (x y) (y z))
			(:instance pdistrib-2-* (x (padd (pmul z (pquot y z f) f) (prem y z f) f)) (y (pmul z (pquot x z f) f)) (z (prem x z f)))
			(:instance pdistrib-* (x (pmul z (pquot x z f) f)) (y (pmul z (pquot y z f) f)) (z (prem y z f)))
			(:instance pdistrib-* (x (prem x z f)) (y (pmul z (pquot y z f) f)) (z (prem y z f)))
			(:instance pmul-assoc-* (x z) (y (pquot x z f)) (z (pmul z (pquot y z f) f)))
                        (:instance pmul-assoc-* (x z) (y (pquot x z f)) (z (prem y z f)))
			(:instance pmul-assoc-* (x z) (y (pquot y z f)) (z (prem x z f)))
			(:instance pmul-comm-* (x (prem x z f)) (y (pmul z (pquot y z f) f)))
			(:instance pdistrib-* (x z) (y (pmul (pquot x z f) (pmul z (pquot y z f) f) f)) (z (pmul (pquot x z f) (prem y z f) f)))
			(:instance padd-assoc-* (x (pmul z (padd (pmul (pquot x z f) (pmul z (pquot y z f) f) f) (pmul (pquot x z f) (prem y z f) f) f) f))
			                        (y (pmul z (pmul (pquot y z f) (prem x z f) f) f))
						(z (pmul (prem x z f) (prem y z f) f)))
			(:instance pdistrib-* (x z) (y (padd (pmul (pquot x z f) (pmul z (pquot y z f) f) f) (pmul (pquot x z f) (prem y z f) f) f))
			                            (z (pmul (pquot y z f) (prem x z f) f)))))))

(local-defthmd prem-pmul-prem-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
	   (equal (pmul x (prem y z f) f)
	          (padd (pmul z (pmul (pquot x z f) (prem y z f) f) f)
		        (pmul (prem x z f) (prem y z f) f)
			f)))
  :hints (("Goal" :use ((:instance pquot-prem-* (y z))
                        (:instance pdistrib-2-* (x (prem y z f)) (y (pmul z (pquot x z f) f)) (z (prem x z f)))
			(:instance pmul-assoc-* (x z) (y (pquot x z f)) (z (prem y z f)))))))

(local-defthmd prem-pmul-prem-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
	   (equal (prem (pmul x y f) z f)
	          (prem (pmul (prem x z f) (prem y z f) f) z f)))
  :hints (("Goal" :use (prem-pmul-prem-1
                        (:instance prem+mult-* (y z) (x (pmul (prem x z f) (prem y z f) f))
			                     (a (padd (padd (pmul (pquot x z f) (pmul z (pquot y z f) f) f)
		                                            (pmul (pquot x z f) (prem y z f) f)
					                    f)
				                      (pmul (pquot y z f) (prem x z f) f)
				                      f)))))))

(local-defthmd prem-pmul-prem-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (>= (degree z) 1) (not (equal z (pzero f))))
	   (equal (prem (pmul x (prem y z f) f) z f)
	          (prem (pmul (prem x z f) (prem y z f) f) z f)))
  :hints (("Goal" :use (prem-pmul-prem-2
                        (:instance prem+mult-* (y z) (x (pmul (prem x z f) (prem y z f) f))
			                     (a (pmul (pquot x z f) (prem y z f) f)))))))

(defthmd prem-pmul-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul x (prem y z f) f) z f)
	          (prem (pmul x y f) z f)))
  :hints (("Goal" :use (prem-pmul-prem-3 prem-pmul-prem-4
                        (:instance polyp-degree-non-neg (x z))))))
			
(defthmd prem-pmul-prem-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul (prem x z f) y f) z f)
	          (prem (pmul x y f) z f)))
  :hints (("Goal" :use (pmul-comm-*
                        (:instance pmul-comm-* (x (prem x z f)))
			(:instance prem-pmul-prem-* (x y) (y x))))))
			

;;---------------------------------------------------------

(defthmd prem-padd-prem-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	  (equal (prem (padd (prem x z f) (prem y z f) f) z f)
	         (padd (prem x z f) (prem y z f) f)))
  :hints (("Goal" :use ((:instance pquot-prem-* (y z))
                        (:instance pquot-prem-* (y z) (x y))
			(:instance degree-padd-bound-* (x (prem x z f)) (y (prem y z f)))
			(:instance prem-equal-* (x (padd (prem x z f) (prem y z f) f)) (y z))))))
  

;;---------------------------------------------------------

(defthmd pquot-prem-pzero
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp y f) (not (equal y (pzero f))))
	   (and (equal (pquot (pzero f) y f) (pzero f))
	        (equal (prem (pzero f) y f) (pzero f))))
  :hints (("Goal" :cases ((pconstp y))
                  :use ((:instance pquot-prem-unique-* (x (pzero f)) (q (pzero f)) (r (pzero f)))
		        (:instance polyp-degree-non-neg (x y))))))

(local-defthmd prem-pneg-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (padd (prem (pneg x f) y f) (prem x y f) f)
	          (pzero f)))
  :hints (("Goal" :use (pquot-prem-pzero
                        (:instance prem-padd-prem-* (x (prem (pneg x f) y f)) (y x) (z y))
                        (:instance prem-padd-prem-comm-* (x (pneg x f)) (y x) (z y))
			(:instance prem-padd-prem-prem-* (z y) (x (pneg x f)) (y x))
			(:instance padd-comm-* (y (pneg x f)))))))

(defthmd prem-pneg-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (equal (prem (pneg x f) y f)
	          (pneg (prem x y f) f)))
  :hints (("Goal" :use (prem-pneg-1
                        (:instance pneg-unique-* (y (prem x y f)) (x (prem (pneg x f) y f)))))))
			

;;---------------------------------------------------------

(defthmd pquot-prem-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot (cmul c x f) y f)
	               (cmul c (pquot x y f) f))
		(equal (prem (cmul c x f) y f)
	               (cmul c (prem x y f) f))))
  :hints (("Goal" :in-theory (enable polyp-cmul-*)
                  :cases ((pconstp y))
		  :use (pquot-prem-*
                        (:instance pquot-prem-unique-* (x (cmul c x f)) (q (cmul c (pquot x y f) f)) (r (cmul c (prem x y f) f)))
			(:instance cmul-padd-* (x (pmul y (pquot x y f) f)) (y (prem x y f)))
			(:instance pmul-comm-* (x (pquot x y f)))
			(:instance cmul-pmul-* (x (pquot x y f)))
			(:instance pmul-comm-* (x (cmul c (pquot x y f) f)))))			
	  ("Subgoal 1.2" :in-theory (enable pzero))
	  ("Subgoal 1.1" :in-theory (enable pzero))))

(local-defthmd cmul-pquot-prem-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f))))
	   (equal (pmul (cmul c x f) (cmul d y f) f)
	          (cmul (fmul c d f) (pmul x y f) f)))
  :hints (("Goal" :in-theory (enable polyp-cmul-*)
                  :use (pmul-comm-*
                        (:instance cmul-pmul-* (y (cmul d y f)))
                        (:instance pmul-comm-* (y (cmul d y f)))
			(:instance cmul-pmul-* (c d) (x y) (y x))
                        (:instance cmul-cmul-* (x (pmul x y f)))))))

(local-defthm polyp-gpolyp
  (implies (polyp x f)
           (gpolyp x f))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd cmul-pquot-prem-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp q f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (equal (pmul (cmul (frecip c f) q f) (cmul c y f) f)
	          (pmul q y f)))
  :hints (("Goal" :use ((:instance cmul-pquot-prem-1 (c (frecip c f)) (d c) (x q))
                        (:instance frecip-not-fzero-* (x c))
                        (:instance fmul-comm-* (x c) (y (frecip c f)))))))

(local-defthmd cmul-pquot-prem-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp q f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (equal (pmul (cmul c y f) (cmul (frecip c f) q f) f)
	          (pmul y q f)))
  :hints (("Goal" :in-theory (enable polyp-cmul-*)
                  :use (cmul-pquot-prem-2
                        (:instance frecip-not-fzero-* (x c))
                        (:instance pmul-comm-* (x q))
                        (:instance pmul-comm-* (x (cmul c y f)) (y (cmul (frecip c f) q f)))))))

(in-theory (disable pquot-prem-*))

(local-defthmd cmul-pquot-prem-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (padd (pmul (cmul c y f) (cmul (frecip c f) (pquot x y f) f) f)
	                     (prem x y f)
			     f)
		       x)
		(if (pconstp y)
		    (equal (prem x y f) (pzero f))
		  (< (degree (prem x y f))
		     (degree (cmul c y f))))))
  :hints (("Goal" :in-theory (enable polyp-cmul-*)
                  :use (pquot-prem-*
		        (:instance cmul-pquot-prem-3 (q (pquot x y f)))))))

(defthmd cmul-pquot-prem-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot x (cmul c y f) f)
	               (cmul (frecip c f) (pquot x y f) f))
		(equal (prem x (cmul c y f) f)
		       (prem x y f))))
  :hints (("Goal" :in-theory (enable polyp-cmul-*)
                  :use (cmul-pquot-prem-4
		        (:instance degree-pconstp (x (cmul c y f)))
                        (:instance frecip-not-fzero-* (x c))
			(:instance cmul-nonzero (x y))
                        (:instance pquot-prem-unique-* (y (cmul c y f)) (q (cmul (frecip c f) (pquot x y f) f)) (r (prem x y f)))))))

(defthmd cmul-divides-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
           (iff (pdivides (cmul c y f) x f)
	        (pdivides y x f)))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use (cmul-pquot-prem-*))))

(defthmd pconstp-pdivides-*
  (implies (pconstp y)
	   (pdivides y x f))
  :hints (("Goal" :in-theory (enable prem pdivides)
                  :expand ((pdivide x y f)))))

(defthm pzero-pdivides-*
  (pdivides (pzero f) x f)
  :hints (("Goal" :use ((:instance pconstp-pdivides-* (y (pzero f))))
                  :in-theory (enable pconstp pzero))))

(defthmd pdivides-pzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (pdivides x (pzero f) f))
  :hints (("Goal" :in-theory (enable pzero prem pdivides)
                  :use ((:instance polyp-def (p x)))
                  :expand ((PDIVIDE (LIST (FZERO F)) X F) (LEN X) (LEN (CDR X)) (PREM (LIST (FZERO F)) X F)))))

(in-theory (disable pquot-prem-*))

;;--------------
;; Divisibility
;;--------------

(local-defthmd pdivides-cmul-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (iff (pdivides y x f)
	        (pdivides y (cmul c x f) f)))
  :hints (("Goal" :in-theory (enable pdivides pzero pquot-prem-cmul-*)
                  :use ((:instance cmul-nonzero (x (prem x y f)))))))

(defthmd pdivides-cmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (iff (pdivides y x f)
	        (pdivides y (cmul c x f) f)))
  :hints (("Goal" :use (pdivides-cmul-1))))

(defthmd pdivides-pquot-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (equal x (pzero f)))
		(pdivides x y f))
	   (equal (pmul x (pquot y x f) f)
	          y))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use ((:instance pquot-prem-* (x y) (y x))))))

(defthmd pdivides-self-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f))
	   (pdivides x x f))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use (polyp-degree-non-neg
                        (:instance pquot-prem-unique-* (y x) (q (pone f)) (r (pzero f)))
                        (:instance pconstp-pdivides-* (y x))))
	  ("Subgoal 2" :in-theory (enable pzero))
	  ("Subgoal 1" :in-theory (enable pzero))))

(defthmd pdivides-multiple-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (pdivides x (pmul x y f) f))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use (polyp-degree-non-neg
                        (:instance pconstp-pdivides-*  (y x) (x  (pmul x y f)))
			(:instance pquot-prem-unique-* (y x) (x (pmul x y f)) (q y) (r (pzero f)))))
	  ("subgoal 1" :in-theory (enable pzero))))

(local-defthmd pdivides-padd-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (equal (padd y z f)
	          (padd (padd (pmul x (pquot y x f) f) (prem y x f) f)
		        (padd (pmul x (pquot z x f) f) (prem z x f) f)
			f)))
  :hints (("Goal" :use ((:instance pquot-prem-* (y x) (x y))
                        (:instance pquot-prem-* (y x) (x z))))))

(local-defthmd pdivides-padd-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (equal (padd (padd (pmul x (pquot y x f) f) (prem y x f) f)
		        (padd (pmul x (pquot z x f) f) (prem z x f) f)
			f)
		  (padd (padd (padd (pmul x (pquot y x f) f) (prem y x f) f) (pmul x (pquot z x f) f) f)
		        (prem z x f)
			f)))
  :hints (("Goal" :use ((:instance padd-assoc-* (x (padd (pmul x (pquot y x f) f) (prem y x f) f)) (y (pmul x (pquot z x f) f)) (z (prem z x f)))))))

(local-defthmd pdivides-padd-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (equal (padd (padd (pmul x (pquot y x f) f) (prem y x f) f) (pmul x (pquot z x f) f) f)
	          (padd (padd (pmul x (pquot y x f) f) (pmul x (pquot z x f) f) f) (prem y x f) f)))
  :hints (("Goal" :use ((:instance padd-assoc-* (x (pmul x (pquot y x f) f)) (y (prem y x f)) (z (pmul x (pquot z x f) f)))
                        (:instance padd-comm-* (x (prem y x f)) (y (pmul x (pquot z x f) f)))
			(:instance padd-assoc-* (x (pmul x (pquot y x f) f)) (y (pmul x (pquot z x f) f)) (z (prem y x f)))))))

(local-defthmd pdivides-padd-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (equal (padd (padd (padd (pmul x (pquot y x f) f) (pmul x (pquot z x f) f) f) (prem y x f) f)
	                (prem z x f) f)
		  (padd (pmul x (padd (pquot y x f) (pquot z x f) f) f)
		        (padd (prem y x f) (prem z x f) f)
			f)))
  :hints (("Goal" :use ((:instance padd-assoc-* (x (padd (pmul x (pquot y x f) f) (pmul x (pquot z x f) f) f)) (y (prem y x f)) (z (prem z x f)))
                        (:instance pdistrib-* (y (pquot y x f)) (z (pquot z x f)))))))

(local-defthmd pdivides-padd-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (equal (padd y z f)
		  (padd (pmul x (padd (pquot y x f) (pquot z x f) f) f)
		        (padd (prem y x f) (prem z x f) f)
			f)))
  :hints (("Goal" :use (pdivides-padd-1 pdivides-padd-2 pdivides-padd-3 pdivides-padd-4))))

(local-defthmd pdivides-padd-6
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f)))
		(pdivides x y f) (pdivides x z f))
	   (pdivides x (padd y z f) f))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use (pdivides-padd-5
                        (:instance pquot-prem-unique-* (y x) (x (padd y z f)) (q (padd (pquot y x f) (pquot z x f) f)) (r (pzero f)))))
	  ("Subgoal 1" :use (polyp-degree-non-neg) :in-theory (enable pzero))))

(defthmd pdivides-padd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f) (pdivides x z f))
	   (pdivides x (padd y z f) f))
  :hints (("Goal" :use (pdivides-padd-6))))

(defthmd pdivides-pmul-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f))
	   (pdivides x (pmul y z f) f))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use (degree-pconstp
                        (:instance pquot-prem-* (y x) (x y))
                        (:instance pmul-assoc-* (y (pquot y x f)))
			(:instance pconstp-pdivides-* (y x) (x (pmul y z f)))
			(:instance pdivides-multiple-* (y (pmul (pquot y x f) z f)))))))

(defthm degree-pzero
  (equal (len (pzero f)) 1)
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd pdivides-transitive-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal y (pzero f))) (not (equal x (pzero f)))
		(pdivides x y f) (pdivides y z f))
	   (pdivides x z f))
  :hints (("Goal" :use (pdivides-pquot-* degree-pconstp
                        (:instance pdivides-pquot-* (x y) (y z))
			(:instance pconstp-pdivides-* (y x) (x z))
                        (:instance pmul-assoc-* (y (pquot y x f)) (z (pquot z y f)))
			(:instance pdivides-multiple-* (y (pmul (pquot y x f) (pquot z y f) f)))))))

(defthmd pdivides-transitive-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal y (pzero f)))
		(pdivides x y f) (pdivides y z f))
	   (pdivides x z f))
  :hints (("Goal" :use (pdivides-transitive-1))))

(defthmd pdivides-prem-equal-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (iff (pdivides x (padd y (pneg z f) f) f)
		(equal (prem y x f) (prem z x f))))
  :hints (("Goal" :in-theory (enable pdivides pneg-pneg-*)
                  :use ((:instance prem-padd-prem-* (z x) (x y) (y (pneg z f)))
                        (:instance prem-padd-prem-comm-* (z x) (x y) (y (prem (pneg z f) x f)))
			(:instance prem-padd-prem-prem-* (z x) (x y) (y (pneg z f)))
			(:instance prem-pneg-* (x z) (y x))
                        (:instance pneg-unique-* (x (prem y x f)) (y (pneg (prem z x f) f)))))))
			
(defthmd pdivides-degree-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (pdivides x y f) (not (equal y (pzero f))))
	   (<= (degree x) (degree y)))
  :hints (("Goal" :cases ((equal x (pzero f)))
                  :use (pdivides-pquot-*
                        (:instance polyp-degree-non-neg (x y))
                        (:instance polyp-degree-non-neg (x (pquot y x f)))
                        (:instance degree-pmul-* (y (pquot y x f)))))))


;;-------------------------
;; Greatest Common Divisor
;;-------------------------

(defun pgcd-induct (p q f)
  (declare (xargs :measure (+ (len p) (len q))))
  (if (or (pconstp p) (pconstp q))
      ()
    (if (>= (degree p) (degree q))
        (let* ((c (fmul (car p) (frecip (car q) f) f))
               (a (monomial c (- (degree p) (degree q)) f))
               (pnew (padd p (pneg (pmul a q f) f) f)))
          (and (< (len pnew) (len p))
               (pgcd-induct pnew q f)))
      (let* ((c (fmul (car q) (frecip (car p) f) f))
             (a (monomial c (- (degree q) (degree p)) f))
            (qnew (padd q (pneg (pmul a p f) f) f)))
        (and (< (len qnew) (len q))
             (pgcd-induct p qnew f))))))

(in-theory (disable len-pzero))

(local-defthmd pgcd-aux-nonzero
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (not (equal (pgcd-aux x y f) (pzero f))))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((PGCD-AUX X Y F))
			  :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/2" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))))

(local-defthm polyp-pgcd-aux
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (polyp (pgcd-aux x y f) f))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((PGCD-AUX X Y F))
			  :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/3" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))
          ("Subgoal *1/2" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))))

(local-defthmd pgcd-aux-divides-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp g f) (polyp x f) (polyp y f) (polyp p f) (not (equal g (pzero f))) (not (equal x (pzero f)))
                (pdivides g x f) (pdivides g (padd y (pneg p f) f) f) (pdivides x p f))
	   (pdivides g y f))
  :hints (("Goal" :use ((:instance pdivides-padd-* (x g) (y (padd y (pneg p f) f)) (z p))
                        (:instance padd-assoc-* (x y) (y (pneg p f)) (z p))
			(:instance padd-comm-* (x p) (y (pneg p f)))
			(:instance pdivides-transitive-* (x g) (y x) (z p))))))

(local-defthmd pgcd-aux-divides-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp g f) (polyp x f) (polyp y f) (polyp m f) (not (equal g (pzero f))) (not (equal x (pzero f)))
                (pdivides g x f) (pdivides g (padd y (pneg (pmul m x f) f) f) f))
	   (pdivides g y f))
  :hints (("Goal" :use ((:instance pgcd-aux-divides-1 (p (pmul m x f)))
                        (:instance pdivides-multiple-* (y m))
			(:instance pmul-comm-* (y m))))))

(local-defthmd pgcd-aux-divides
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (and (pdivides (pgcd-aux x y f) x f)
	        (pdivides (pgcd-aux x y f) y f)))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((PGCD-AUX X Y F))
			  :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))
				(:instance pgcd-aux-divides-2 (g (pgcd-aux x y f)) (m (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F)))))
          ("Subgoal *1/3" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))
				(:instance pgcd-aux-divides-2 (g (pgcd-aux x y f)) (m (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F)))))
          ("Subgoal *1/2" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))
				(:instance pgcd-aux-divides-2 (x y) (y x) (g (pgcd-aux x y f)) (m (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F)))))
	  ("Subgoal *1/1" :use (pdivides-self-* pconstp-pdivides-* pdivides-pzero-*
	                        (:instance pdivides-self-* (x y))
	                        (:instance pdivides-pzero-* (x y))
				(:instance pconstp-pdivides-* (x y) (y x))))))

(local-defthmd divides-pgcd-aux-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (polyp m f)
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (padd y (pneg (pmul m x f) f) f) f))
  :hints (("Goal" :use ((:instance pneg-pmul (y m))
                        (:instance pmul-comm-* (y m))
			(:instance pdivides-pmul-* (x z) (y x) (z (pneg m f)))
			(:instance pdivides-padd-* (x z) (z (pneg (pmul m x f) f)))))))

(local-defthmd divides-pgcd-aux
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (pgcd-aux x y f) f))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((PGCD-AUX X Y F))
			  :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))
				(:instance divides-pgcd-aux-1 (m (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F)))))
          ("Subgoal *1/3" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))
				(:instance divides-pgcd-aux-1 (m (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F)))))
          ("Subgoal *1/2" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))
				(:instance divides-pgcd-aux-1 (x y) (y x) (m (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F)))))))

(local-defthmd pgcd-aux-linear-combination-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp s f) (polyp m f))
	   (equal (pmul s (pneg (pmul m x f) f) f)
	          (pmul (pneg (pmul m s f) f) x f)))
  :hints (("Goal" :use ((:instance pneg-pmul (x s) (y (pmul m x f)))
                        (:instance pmul-assoc-* (x s) (y m) (z x))
			(:instance pmul-comm-* (x m) (y s))
			(:instance pmul-pneg-* (x (pmul m s f)) (y x))))))

(local-defthmd pgcd-aux-linear-combination-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp r f) (polyp s f) (polyp m f))
	   (equal (padd (pmul r x f)
	                (pmul s (padd y (pneg (pmul m x f) f) f) f)
			f)
		  (padd (pmul (padd r (pneg (pmul m s f) f) f) x f)
		        (pmul s y f)
			f)))
  :hints (("Goal" :use (pgcd-aux-linear-combination-1
                        (:instance pdistrib-* (x s) (z (pneg (pmul m x f) f)))
                        (:instance padd-comm-* (x (pmul s y f)) (y (pmul (pneg (pmul m s f) f) x f)))
			(:instance padd-assoc-* (x (pmul r x f)) (y (pmul (pneg (pmul m s f) f) x f)) (z (pmul s y f)))
			(:instance pdistrib-2-* (y r) (z (pneg (pmul m s f) f)))))))

(local-defthmd pgcd-aux-linear-combination-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp r f) (polyp s f) (polyp m f))
	   (equal (padd (pmul r (padd x (pneg (pmul m y f) f) f) f)
	                (pmul s y f)
			f)
		  (padd (pmul r x f)
		        (pmul (padd s (pneg (pmul m r f) f) f) y f)
			f)))
  :hints (("Goal" :use ((:instance pgcd-aux-linear-combination-2 (r s) (s r) (x y) (y x))
                        (:instance padd-comm-* (x (pmul s y f)) (y (pmul r (padd x (pneg (pmul m y f) f) f) f)))
			(:instance padd-comm-* (x (pmul r x f)) (y (pmul (padd s (pneg (pmul m r f) f) f) y f)))))))

(local-defthm polyp-r-s-aux
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (and (polyp (rp-aux x y f) f)
	        (polyp (sp-aux x y f) f)))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((rp-aux x y f) (sp-aux x y f))
			  :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/3" :expand ((rp-aux x y f) (sp-aux x y f))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))
          ("Subgoal *1/2" :expand ((rp-aux x y f) (sp-aux x y f))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))))

(local-defthmd pgcd-aux-linear-combination-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (not (pconstp x)) (<= (degree x) (degree y)))
	   (polyp (monomial (fmul (car y) (frecip (car x) f) f) (- (degree y) (degree x)) f) f))
  :hints (("Goal" :use (polyp-car-nonzero polyp-degree-non-neg
                        (:instance polyp-car-nonzero (x y))
			(:instance frecip-not-fzero-* (x (car x)))
			(:instance field-integral-domain-* (x (car y)) (y (frecip (car x) f)))))))
  
(local-defthmd pgcd-aux-linear-combination
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f))
	   (let ((r (rp-aux x y f))
	         (s (sp-aux x y f)))
	     (and (polyp r f)
	          (polyp s f)
	  	  (equal (padd (pmul r x f) (pmul s y f) f)
		         (pgcd-aux x y f)))))
  :hints (("Goal" :induct (pgcd-induct x y f))
          ("Subgoal *1/5" :use (polyp-degree-non-neg len-pzero
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))))
          ("Subgoal *1/4" :expand ((PGCD-AUX X Y F))
			  :use (polyp-degree-non-neg len-pzero pgcd-aux-linear-combination-4
	                        (:instance degree-decreasing (x y) (y x))
	                        (:instance polyp-x1 (x y) (y x))
				(:instance polyp-r-s-aux (y (PADD Y (PNEG (PMUL (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F) X F) F) F)))
			        (:instance pgcd-aux-linear-combination-2 (s (SP-AUX X (PADD Y (PNEG (PMUL (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F) X F) F) F) F))
				                                         (r (RP-AUX X (PADD Y (PNEG (PMUL (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F) X F) F) F) F))
									 (m (MONOMIAL (FMUL (CAR Y) (FRECIP (CAR X) F) F) (+ (- (LEN X)) (LEN Y)) F)))))
          ("Subgoal *1/3" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))))
          ("Subgoal *1/2" :expand ((PGCD-AUX X Y F))
			  :use (len-pzero degree-decreasing polyp-x1
			        (:instance polyp-degree-non-neg (x y))
			        (:instance pgcd-aux-linear-combination-4 (x y) (y x))				
				(:instance polyp-r-s-aux (x (PADD X (PNEG (PMUL (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F) Y F) F) F)))
			        (:instance pgcd-aux-linear-combination-3 (s (SP-AUX (PADD X (PNEG (PMUL (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F) Y F) F) F) y f))
				                                         (r (RP-AUX (PADD X (PNEG (PMUL (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F) Y F) F) F) y f))
									 (m (MONOMIAL (FMUL (CAR X) (FRECIP (CAR Y) F) F) (+ (LEN X) (- (LEN Y))) F)))))))

(local-defthmd pgcd-aux-pzero-pzero
  (equal (pgcd-aux (pzero f) (pzero f) f)
         (pzero f)))

(local-defthmd car-pgcd-aux-nonzero
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (let* ((c (car (pgcd-aux x y f)))
	          (r (frecip c f)))
	     (and (feltp c f)
	          (not (equal c (fzero f)))
		  (feltp r f)
		  (not (equal r (fzero f))))))
  :hints (("Goal" :use (pgcd-aux-nonzero polyp-pgcd-aux
                        (:instance polyp-car-nonzero (x (pgcd-aux x y f)))
			(:instance frecip-not-fzero-* (x (car (pgcd-aux x y f))))))))

(defthmd polyp-pgcd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (polyp (pgcd x y f) f))
  :hints (("Goal" :in-theory (enable pgcd)
                  :use (pgcd-aux-nonzero polyp-pgcd-aux car-pgcd-aux-nonzero
                        (:instance polyp-cmul-* (c (frecip (car (pgcd-aux x y f)) f)) (x (pgcd-aux x y f)))))))

(defthmd pgcd-monic-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (monicp (pgcd x y f) f))
  :hints (("Goal" :in-theory (enable pgcd monicp)
                  :use (pgcd-aux-nonzero polyp-pgcd-aux car-pgcd-aux-nonzero
                        (:instance car-cmul (c (frecip (car (pgcd-aux x y f)) f)) (x (pgcd-aux x y f)))
			(:instance polyp-def (p (pgcd-aux x y f)))
			(:instance fmul-comm-* (x (car (pgcd-aux x y f))) (y (frecip (car (pgcd-aux x y f)) f)))))))

(defthmd pgcd-nonzero-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (not (equal (pgcd x y f) (pzero f))))
  :hints (("Goal" :in-theory (enable pzero monicp)
                  :use (pgcd-monic-*))))

(defthmd pgcd-divides-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (pdivides (pgcd x y f) x f)
	        (pdivides (pgcd x y f) y f)))
  :hints (("Goal" :in-theory (enable pgcd)
                  :use (pgcd-aux-divides pgcd-aux-nonzero car-pgcd-aux-nonzero
                        (:instance cmul-divides-* (c (frecip (car (pgcd-aux x y f)) f)) (y (pgcd-aux x y f)))
                        (:instance cmul-divides-* (c (frecip (car (pgcd-aux x y f)) f)) (y (pgcd-aux x y f)) (x y))))))
			
(defthmd divides-pgcd-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f)
                (not (and (equal x (pzero f)) (equal y (pzero f))))
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (pgcd x y f) f))
  :hints (("Goal" :in-theory (enable pgcd)
                  :use (divides-pgcd-aux pgcd-aux-nonzero car-pgcd-aux-nonzero
                        (:instance pdivides-cmul-* (y z) (c (frecip (car (pgcd-aux x y f)) f)) (x (pgcd-aux x y f)))))))

(defthmd pgcd-linear-combination-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (let ((r (rp x y f))
	         (s (sp x y f)))
	     (and (polyp r f)
	          (polyp s f)
	  	  (equal (padd (pmul r x f) (pmul s y f) f)
		         (pgcd x y f)))))
  :hints (("Goal" :in-theory (enable polyp-cmul-* rp sp pgcd)
                  :use (pgcd-aux-linear-combination pgcd-aux-nonzero car-pgcd-aux-nonzero
                        (:instance cmul-padd-*  (c (frecip (car (pgcd-aux x y f)) f)) (x (pmul (rp-aux x y f) x f)) (y (pmul (sp-aux x y f) y f)))
			(:instance cmul-pmul-* (c (frecip (car (pgcd-aux x y f)) f)) (x (rp-aux x y f)) (y x))
			(:instance cmul-pmul-* (c (frecip (car (pgcd-aux x y f)) f)) (x (sp-aux x y f)))))))

(local-defthmd pgcd-comm-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (pdivides (pgcd x y f) (pgcd y x f) f)
	        (pdivides (pgcd y x f) (pgcd x y f) f)
		(equal (degree (pgcd x y f)) (degree (pgcd y x f)))))
  :hints (("Goal" :use (pgcd-divides-* polyp-pgcd-* pgcd-nonzero-*
                        (:instance pgcd-nonzero-* (x y) (y x))
                        (:instance polyp-pgcd-* (x y) (y x))
                        (:instance pgcd-divides-* (x y) (y x))
			(:instance divides-pgcd-* (z (pgcd y x f)))
			(:instance divides-pgcd-* (x y) (y x) (z (pgcd x y f)))
			(:instance pdivides-degree-* (x (pgcd x y f)) (y (pgcd y x f)))
			(:instance pdivides-degree-* (x (pgcd y x f)) (y (pgcd x y f)))))))

(local-defthmd pgcd-comm-2
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (polyp (pquot (pgcd x y f) (pgcd y x f) f) f)
	        (equal (pgcd x y f) (pmul (pgcd y x f) (pquot (pgcd x y f) (pgcd y x f) f) f))
	        (equal (degree (pquot (pgcd x y f) (pgcd y x f) f)) 0)
		(equal (car (pquot (pgcd x y f) (pgcd y x f) f)) (fone f))))
  :hints (("Goal" :in-theory (enable monicp)
                  :use (pgcd-nonzero-* pgcd-comm-1 polyp-pgcd-* pgcd-monic-*
                        (:instance pgcd-nonzero-* (x y) (y x))
                        (:instance polyp-pgcd-* (x y) (y x))
			(:instance polyp-car-nonzero (x (pquot (pgcd x y f) (pgcd y x f) f)))
			(:instance pdivides-pquot-* (y (pgcd x y f)) (x (pgcd y x f)))
			(:instance degree-pmul-* (x (pgcd y x f)) (y (pquot (pgcd x y f) (pgcd y x f) f)))
			(:instance car-pmul-* (x (pgcd y x f)) (y (pquot (pgcd x y f) (pgcd y x f) f)))
			(:instance pgcd-monic-* (x y) (y x))))))

(local-defthmd hack-4
  (implies (and (true-listp x) (consp x) (not (consp (cdr x))))
           (equal (list (car x)) x)))

(local-defthmd pgcd-comm-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (equal (degree x) 0) (equal (car x) (fone f)))
	   (equal (pone f) x))
  :hints (("Goal" :in-theory (e/d (polyp pone) (true-listp-gpolyp))
                  :use (hack-4 true-listp-gpolyp len))))

(defthmd pgcd-comm-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (equal (pgcd x y f) (pgcd y x f)))
  :hints (("Goal" :use (pgcd-comm-2
                        (:instance pgcd-comm-3 (x (pquot (pgcd x y f) (pgcd y x f) f)))
                        (:instance polyp-pgcd-* (x y) (y x))))))

(defund precip (x f)
  (list (frecip (car x) f)))

(defthmd pmul-precip-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (pconstp x) (not (equal x (pzero f))))
           (let ((r (precip x f)))
	     (and (polyp r f)
	          (pconstp r)
		  (not (equal r (pzero f)))
		  (equal (pmul x r f) (pone f)))))
  :hints (("Goal" :in-theory (enable polyp pconstp precip pone pzero)
                  :use ((:instance frecip-not-fzero-* (x (car x)))))))

(local-defthmd pdivides-equal-degree-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (equal (degree x) (degree y))
		(not (equal x (pzero f))) (not (equal y (pzero f)))
		(pdivides x y f))
	   (pdivides y x f))
  :hints (("Goal" :use (pdivides-pquot-*
		        (:instance degree-pmul-* (y (pquot y x f)))
			(:instance pmul-precip-* (x (pquot y x f)))
			(:instance degree-pconstp (x (pquot y x f)))
			(:instance pmul-assoc-* (y (pquot y x f)) (z (precip (pquot y x f) f)))
			(:instance pdivides-multiple-* (x y) (y (precip (pquot y x f) f)))))))

(defthmd pdivides-equal-degree-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (equal (degree x) (degree y))
		(pdivides x y f))
	   (pdivides y x f))
  :hints (("Goal" :in-theory (enable pdivides-pzero-*)
                  :use (pdivides-equal-degree-1))))

(defthmd irreduciblep-no-factor-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f)
		(irreduciblep p f)
		(< (degree x) (degree p))
		(pdivides x p f))
	   (pconstp x))
  :hints (("Goal" :in-theory (enable irreduciblep reduciblep)
                  :use (degree-pconstp polyp-degree-non-neg
		        (:instance pfactor (q x))))))
                        
(local-defthmd pgcd-irreduciblep-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f)
		(irreduciblep p f) (not (pdivides p x f)))
	   (pconstp (pgcd p x f)))
  :hints (("Goal" :use ((:instance pgcd-divides-* (x p) (y x))
                        (:instance pdivides-equal-degree-* (x (pgcd p x f)) (y p))
			(:instance polyp-pgcd-* (x p) (y x))
			(:instance pgcd-nonzero-* (x p) (y x))
			(:instance pdivides-degree-* (x (pgcd p x f)) (y p))
			(:instance pdivides-transitive-* (x p) (y (pgcd p x f)) (z x))
			(:instance irreduciblep-no-factor-* (x (pgcd p x f)))))))

(defthmd pgcd-irreduciblep-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f)
		(irreduciblep p f) (not (pdivides p x f)))
	   (equal (pgcd p x f) (pone f)))
  :hints (("Goal" :in-theory (enable pone pconstp monicp)
                  :use (pgcd-irreduciblep-1
		        (:instance polyp-pgcd-* (x p) (y x))
			(:instance polyp-def (p (pgcd p x f)))
		        (:instance pgcd-monic-* (x p) (y x))))))
		       
 (local-defthmd peuclid-1
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f) (polyp y f) (polyp r f) (polyp s f)
		(pdivides p (pmul x y f) f))
	   (pdivides p (pmul (padd (pmul r p f) (pmul s x f) f)
	                     y f)
		       f))
  :hints (("Goal" :use ((:instance pdistrib-2-* (x y) (y (pmul r p f)) (z (pmul s x f)))
                        (:instance pmul-comm-* (x r) (y p))
			(:instance pmul-assoc-* (x p) (y r) (z y))
			(:instance pmul-assoc-* (x s) (y x) (z y))
			(:instance pmul-comm-* (x (pmul x y f)) (y s))
			(:instance pdivides-multiple-* (x p) (y (pmul r y f)))
			(:instance pdivides-pmul-* (x p) (y (pmul x y f)) (z s))
			(:instance pdivides-padd-* (x p) (y (pmul (pmul r p f) y f)) (z (pmul (pmul s x f) y f)))))))

(defthmd peuclid-*
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp p f) (polyp x f) (polyp y f)
		(irreduciblep p f) (pdivides p (pmul x y f) f))
	   (or (pdivides p x f) (pdivides p y f)))
  :hints (("Goal" :use (pgcd-irreduciblep-*
                        (:instance peuclid-1 (r (rp p x f)) (s (sp p x f)))
			(:instance pgcd-linear-combination-* (x p) (y x))))))

(defthm irreduciblep-car-field
  (implies (and (fieldp f) (consp f))
           (and (polyp (car f) (cdr f))
	        (not (pconstp (car f)))
		(not (equal (car f) (pzero (cdr f))))
		(irreduciblep (car f) (cdr f))))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use ((:instance degree-pconstp (x (car f)))))))

(defthmd degree-car-field
  (implies (and (fieldp f) (consp f))
           (>= (degree (car f))2))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use ((:instance degree-pconstp (x (car f)))))))


;;----------------------------------------------------------------------------------------------------------
;;                                                Step 4
;;----------------------------------------------------------------------------------------------------------

(defthm fzero-id-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
           (equal (fadd (fzero f) x f)
	          x))
  :hints (("Goal" :in-theory (enable feltp fzero polyp fadd padd)
                  :use ((:instance faddl-fzero (f (cdr f)))))))

(defthm fone-id-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f))
           (equal (fmul (fone f) x f) x))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :expand ((prem x (car f) (cdr f)) (pdivide x (car f) (cdr f)))
		  :use (fone-id-1))))

(defthm fadd-closed-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (feltp (fadd x y f) f))
  :hints (("Goal" :in-theory (enable fadd padd polyp feltp)
                  :use (consp-faddl
		        (:instance gpolyp-faddl (f (cdr f)))
			(:instance feltp-pstrip (x (faddl x y (cdr f))))
		        (:instance len-faddl (f (cdr f)))))))

(defthm feltp-fneg-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)) (feltp x f))
           (feltp (fneg x f) f))
  :hints (("Goal" :in-theory (enable feltp fneg polyp gpolyp)
                  :use ((:instance gpolyp-pneg (f (cdr f)))
		        (:instance fneg-fzero-* (f (cdr f)) (x (car x)))))))

(defthm fadd-fneg-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)) (feltp x f))
           (equal (fadd x (fneg x f) f)
	          (fzero f)))
  :hints (("Goal" :in-theory (enable pzero feltp fzero fneg fadd polyp padd)
                  :use ((:instance faddl-pneg (f (cdr f)))))))

(defthmd fadd-comm-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (equal (fadd x y f) (fadd y x f)))
  :hints (("Goal" :in-theory (enable fadd padd polyp feltp)
                  :use ((:instance faddl-comm (f (cdr f)))))))

(defthmd fadd-assoc-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f) (feltp z f))
           (equal (fadd x (fadd y z f) f)
	          (fadd (fadd x y f) z f)))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :use (fadd-faddl-assoc
		        (:instance faddl-assoc (f (cdr f)))))))

(defthm fmul-closed-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (feltp y f))
           (feltp (fmul x y f) f))
  :hints (("Goal" :in-theory (enable fieldp feltp)
                  :expand ((fmul x y f))
                  :use ((:instance degree-prem-* (x (pmul x y (cdr f))) (y (car f)) (f (cdr f)))))))

(defthmd fdistrib-**
   (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                 (feltp x f) (feltp y f) (feltp z f))
            (equal (fmul x (fadd y z f) f)
                   (fadd (fmul x y f) (fmul x z f) f)))
  :hints (("Goal" :in-theory (enable degree-prem-* fieldp feltp fadd fmul)
                  :use ((:instance pdistrib-* (f (cdr f)))
		        (:instance degree-pconstp (x (car f)))
                        (:instance prem-padd-prem-comm-* (f (cdr f)) (z (car f)) (x (pmul x y (cdr f))) (y (pmul x z (cdr f))))
                        (:instance prem-padd-prem-* (f (cdr f)) (z (car f)) (x (pmul x y (cdr f))) (y (pmul x z (cdr f))))
                        (:instance prem-padd-prem-* (f (cdr f)) (z (car f)) (x (prem (pmul x y (cdr f)) (car f) (cdr f))) (y (pmul x z (cdr f))))
                        (:instance prem-padd-prem-prem-* (f (cdr f)) (z (car f)) (x (pmul x y (cdr f))) (y (pmul x z (cdr f))))))))

 (defthmd fmul-comm-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
           (feltp x f) (feltp y f))
           (equal (fmul x y f) (fmul y x f)))
  :hints (("Goal" :in-theory (enable feltp fmul)
                  :use ((:instance pmul-comm-* (f (cdr f)))
			(:instance polyp-def (p x))
			(:instance polyp-def (p y))))))

(defthmd fmul-assoc-**
   (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                 (feltp x f) (feltp y f) (feltp z f))
            (equal (fmul x (fmul y z f) f)
                   (fmul (fmul x y f) z f)))
  :hints (("Goal" :in-theory (enable fieldp feltp fmul)
                  :use ((:instance pmul-assoc-* (f (cdr f)))
                        (:instance prem-pmul-prem-* (y (pmul y z (cdr f))) (z (car f)) (f (cdr f)))
                        (:instance prem-pmul-prem-comm-* (x (pmul x y (cdr f))) (y z) (z (car f)) (f (cdr f)))))))

(defthmd feltp-frecip-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (feltp (frecip x f) f))
  :hints (("Goal" :in-theory (enable pquot-prem-* feltp frecip)
                  :use ((:instance pgcd-linear-combination-* (y (car f)) (f (cdr f)))
		        (:instance degree-pconstp (x (car f)) (f (cdr f)))
                        (:instance degree-prem-* (x (rp x (car f) (cdr f))) (y (car f)) (f (cdr f)))))))

(local-defthmd fmul-frecip-1
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (equal (pgcd x (car f) (cdr f)) (pone (cdr f))))
  :hints (("Goal" :in-theory (enable pzero fzero feltp)
                  :use ((:instance pgcd-irreduciblep-* (p (car f)) (f (cdr f)))
                        (:instance pdivides-degree-* (x (car f)) (y x) (f (cdr f)))
			(:instance pgcd-comm-* (y (car f)) (f (cdr f)))))))

(local-defthmd fmul-frecip-2
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
	   (let ((r (rp x (car f) (cdr f)))
	         (s (sp x (car f) (cdr f))))
	     (and (polyp r (cdr f))
	          (polyp s (cdr f))
		  (polyp x (cdr f))
		  (equal (padd (pmul r x (cdr f)) (pmul s (car f) (cdr f)) (cdr f))
		         (pone (cdr f))))))
  :hints (("Goal" :in-theory (enable feltp)
                  :use (fmul-frecip-1 (:instance pgcd-linear-combination-* (y (car f)) (f (cdr f)))))))

(local-defthmd fmul-frecip-3
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (padd x y f) z f)
	          (padd (prem x z f) (prem y z f) f)))
  :hints (("Goal" :use (prem-padd-prem-prem-* prem-padd-prem-*
                        (:instance prem-padd-prem-comm-* (y (prem y z f)))))))

(local-defthmd fmul-frecip-4
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp x f) (polyp s f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (pmul s z f) z f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use ((:instance pdivides-multiple-* (x z) (y s))
		        (:instance pmul-comm-* (x s) (y z))))))

(local-defthmd fmul-frecip-5
  (implies (and (fieldp f) (field-axioms-p f)
                (polyp z f) (>= (degree z) 1))
           (equal (prem (pone f) z f)
	          (pone f)))
  :hints (("Goal" :use ((:instance prem-equal-* (x (pone f)) (y z))))
          ("Goal'4'" :in-theory (enable pone))))

(local-defthmd fmul-frecip-6
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
	   (let ((r (rp x (car f) (cdr f))))
             (equal (prem (pmul r x (cdr f)) (car f) (cdr f))
	            (pone (cdr f)))))
  :hints (("Goal" :use (fmul-frecip-2 degree-car-field
                        (:instance fmul-frecip-3 (f (cdr f)) (z (car f)) (x (pmul (rp x (car f) (cdr f)) x (cdr f))) (y (pmul (sp x (car f) (cdr f)) (car f) (cdr f))))
			(:instance fmul-frecip-4 (f (cdr f)) (z (car f)) (s (sp x (car f) (cdr f))))
			(:instance fmul-frecip-5 (f (cdr f)) (z (car f)))))))

(local-defthmd fmul-frecip-7
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (equal (prem (pmul (frecip x f) x (cdr f)) (car f) (cdr f))
                  (pone (cdr f))))
  :hints (("Goal" :in-theory (enable frecip)
                  :use (fmul-frecip-2 fmul-frecip-6
                        (:instance prem-pmul-prem-comm-* (f (cdr f)) (z (car f)) (x (rp x (car f) (cdr f))) (y x))))))

(local-defthmd fmul-frecip-8
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (equal (fmul (frecip x f) x f)
	          (fone f)))
  :hints (("Goal" :in-theory (enable pone fone fmul)
                  :use (fmul-frecip-7
		        (:instance fmul (x (frecip x f)) (y x))))))

(defthmd fmul-frecip-**
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f))
                (feltp x f) (not (equal x (fzero f))))
           (equal (fmul x (frecip x f) f)
	          (fone f)))
  :hints (("Goal" :use (fmul-frecip-8 feltp-frecip-**
                        (:instance fmul-comm-** (y (frecip x f)))))))


;;----------------------------------------------------------------------------------------------------------
;;                                               Step 5
;;----------------------------------------------------------------------------------------------------------

(defthm fadd-closed-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
           (fadd-closed-p f))
  :hints (("Goal" :use (fadd-closed-p-witness-lemma
                        (:instance fadd-closed-** (x (mv-nth 0 (mv-list 2 (fadd-closed-p-witness f))))
			                          (y (mv-nth 1 (mv-list 2 (fadd-closed-p-witness f)))))))))

(defthm fmul-closed-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-closed-p f))
  :hints (("Goal" :use (fmul-closed-p-witness-lemma
                        (:instance fmul-closed-** (x (mv-nth 0 (mv-list 2 (fmul-closed-p-witness f))))
			                          (y (mv-nth 1 (mv-list 2 (fmul-closed-p-witness f)))))))))

(defthm fadd-comm-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-comm-p f))
  :hints (("Goal" :use (fadd-comm-p-witness-lemma
                        (:instance fadd-comm-** (x (mv-nth 0 (mv-list 2 (fadd-comm-p-witness f))))
			                        (y (mv-nth 1 (mv-list 2 (fadd-comm-p-witness f)))))))))

(defthm fmul-comm-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-comm-p f))
  :hints (("Goal" :use (fmul-comm-p-witness-lemma
                        (:instance fmul-comm-** (x (mv-nth 0 (mv-list 2 (fmul-comm-p-witness f))))
			                        (y (mv-nth 1 (mv-list 2 (fmul-comm-p-witness f)))))))))

(defthm fadd-assoc-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-assoc-p f))
  :hints (("Goal" :use (fadd-assoc-p-witness-lemma
                        (:instance fadd-assoc-** (x (mv-nth 0 (mv-list 3 (fadd-assoc-p-witness f))))
			                         (y (mv-nth 1 (mv-list 3 (fadd-assoc-p-witness f))))
			                         (z (mv-nth 2 (mv-list 3 (fadd-assoc-p-witness f)))))))))

(defthm fmul-assoc-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-assoc-p f))
  :hints (("Goal" :use (fmul-assoc-p-witness-lemma
                        (:instance fmul-assoc-** (x (mv-nth 0 (mv-list 3 (fmul-assoc-p-witness f))))
			                         (y (mv-nth 1 (mv-list 3 (fmul-assoc-p-witness f))))
			                         (z (mv-nth 2 (mv-list 3 (fmul-assoc-p-witness f)))))))))

(defthm feltp-fzero-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fzero-p f))
  :hints (("Goal" :use (feltp-fzero-p-witness-lemma feltp-fzero))))

(defthm feltp-fone-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fone-p f))
  :hints (("Goal" :use (feltp-fone-p-witness-lemma feltp-fone))))

(defthm fzero-id-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fzero-id-p f))
  :hints (("Goal" :use (fzero-id-p-witness-lemma
                        (:instance fzero-id-** (x (fzero-id-p-witness f)))))))

(defthm fone-id-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fone-id-p f))
  :hints (("Goal" :use (fone-id-p-witness-lemma
                        (:instance fone-id-** (x (fone-id-p-witness f)))))))

(defthm fone-fzero-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fone-fzero-p f))
  :hints (("Goal" :use (fone-fzero-p-witness-lemma fone-fzero))))

(defthm feltp-fneg-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-fneg-p f))
  :hints (("Goal" :use (feltp-fneg-p-witness-lemma
                        (:instance feltp-fneg-** (x (feltp-fneg-p-witness f)))))))

(defthm fadd-fneg-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fadd-fneg-p f))
  :hints (("Goal" :use (fadd-fneg-p-witness-lemma
                        (:instance fadd-fneg-** (x (fadd-fneg-p-witness f)))))))

(defthm feltp-frecip-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (feltp-frecip-p f))
  :hints (("Goal" :use (feltp-frecip-p-witness-lemma
                        (:instance feltp-frecip-** (x (feltp-frecip-p-witness f)))))))

(defthm fmul-frecip-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fmul-frecip-p f))
  :hints (("Goal" :use (fmul-frecip-p-witness-lemma
                        (:instance fmul-frecip-** (x (fmul-frecip-p-witness f)))))))

(defthm fdistrib-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
	   (fdistrib-p f))
  :hints (("Goal" :use (fdistrib-p-witness-lemma
                        (:instance fdistrib-** (x (mv-nth 0 (mv-list 3 (fdistrib-p-witness f))))
			                       (y (mv-nth 1 (mv-list 3 (fdistrib-p-witness f))))
			                       (z (mv-nth 2 (mv-list 3 (fdistrib-p-witness f)))))))))
						  
(defthmd field-axioms-p-step
  (implies (and (fieldp f) (consp f) (field-axioms-p (cdr f)))
           (field-axioms-p f))
  :hints (("Goal" :use (field-axioms-p))))


;;----------------------------------------------------------------------------------------------------------
;;                                               Step 6
;;----------------------------------------------------------------------------------------------------------

;; An immediate consequence of Steps 2 and 5 by induction:

(defthm field-axioms-p-fieldp
  (implies (fieldp f) (field-axioms-p f))
  :hints (("Goal" :induct (len f))
          ("Subgoal *1/2" :in-theory (enable fieldp) :use (field-axioms-p-fbasep))
          ("Subgoal *1/1" :use (field-axioms-p-step))))
                  

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
	   (equal (fadd (fadd x y f) z f) (fadd x (fadd y z f) f)))
  :hints (("Goal" :use (fadd-assoc-*))))

(defthmd fmul-assoc
  (implies (and (fieldp f) (feltp x f) (feltp y f) (feltp z f))
	   (equal (fmul (fmul x y f) z f) (fmul x (fmul y z f) f)))
  :hints (("Goal" :use (fmul-assoc-*))))

(defthm feltp-fzero
  (implies (fieldp f)
           (feltp (fzero f) f)))

(defthm feltp-fone
  (implies (fieldp f)
           (feltp (fone f) f))
  :hints (("Goal" :in-theory (enable field-axioms-p))))

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
		       (fadd (fmul x y f) (fmul x z f) f)))
  :hints (("Goal" :use (fdistrib-*))))

;;---------------------------------
;; Additional properties of fields
;;---------------------------------

(defthmd fneg-fzero
  (implies (and (fieldp f) (feltp x f))
           (iff (equal (fneg x f) (fzero f))
                (equal x (fzero f))))
  :hints (("Goal" :use (fneg-fzero-*))))

(defthm fzero-id-2
  (implies (and (fieldp f) (feltp x f))
	   (equal (fadd x (fzero f) f) x)))

(defthmd fzero-unique
  (implies (and (fieldp f)
                (feltp x f) (feltp y f) (equal (fadd x y f) (fzero f)))
	   (equal (fneg y f) x))
  :hints (("Goal" :use (fzero-unique-*))))

(defthm fneg-fneg
  (implies (and (fieldp f) (feltp x f))
           (equal (fneg (fneg x f) f)
	          x))
  :hints (("Goal" :use (fneg-fneg-*))))

(defthm fone-id-2
  (implies (and (fieldp f) (feltp x f))
	   (equal (fmul x (fone f) f) x)))

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
	          (fmul x (fneg y f) f)))
  :hints (("Goal" :use (fneg-fmul-*))))

(defthm field-integral-domain
  (implies (and (fieldp f)
                (feltp x f)
		(feltp y f)
		(equal (fmul x y f) (fzero f)))
	   (or (equal x (fzero f))
	       (equal y (fzero f))))
  :rule-classes ()
  :hints (("Goal" :use (field-integral-domain-*))))

(defthmd frecip-not-fzero
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (frecip x f) (fzero f))))
  :hints (("Goal" :use (frecip-not-fzero-*))))

;;------------------------
;; Polynomial ring axioms
;;------------------------

(defthm polyp-pone
  (implies (fieldp f)
           (polyp (pone f) f)))

(defthm pzero-id
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (padd (pzero f) x f)
	          x)))

(defthm pzero-id-2
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (padd x (pzero f) f)
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
	          (pzero f)))
  :hints (("Goal" :use (padd-pneg-*))))

(defthmd pneg-unique
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (equal (padd x y f) (pzero f)))
	   (equal (pneg y f) x))
  :hints (("Goal" :use (pneg-unique-*))))

(defthm padd-closed
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
           (polyp (padd x y f) f)))

(defthmd padd-comm
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
           (equal (padd x y f) (padd y x f)))
  :hints (("Goal" :use (padd-comm-*))))

(defthmd padd-assoc
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f))
           (equal (padd x (padd y z f) f)
	          (padd (padd x y f) z f)))
  :hints (("Goal" :use (padd-assoc-*))))

(defthm pone-id
  (implies (and (fieldp f) 
                (polyp x f))
	   (equal (pmul (pone f) x f)
	          x)))

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
	          (pmul (pmul x y f) z f)))
  :hints (("Goal" :use (pmul-assoc-*))))

(defthmd pdistrib
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul x (padd y z f) f)
	          (padd (pmul x y f) (pmul x z f) f)))
  :hints (("Goal" :use (pdistrib-*))))

;;-------------------------------------------
;; Additional properties of polynomial rings
;;-------------------------------------------

(defthm pone-id-2
  (implies (and (fieldp f)
                (polyp x f))
	   (equal (pmul x (pone f) f)
	          x))
  :hints (("Goal" :use (pone-id-2-*))))

(defthmd pneg-pneg
  (implies (and (fieldp f)
                (polyp x f))
	   (equal (pneg (pneg x f) f)
	          x))
  :hints (("Goal" :use (pneg-pneg-*))))

(defthm pneg-pzero
  (implies (and (fieldp f))
           (equal (pneg (pzero f) f) (pzero f)))
  :hints (("Goal" :use (pneg-pzero-*))))

(defthmd pneg-nonzero
  (implies (and (fieldp f)
                (polyp x f)
	        (equal (pneg x f) (pzero f)))
	   (equal (pzero f) x))
  :hints (("Goal" :use (pneg-nonzero-*))))

(defthmd pneg-padd
  (implies (and (fieldp f)
                (polyp x f) (polyp y f))
	   (equal (pneg (padd x y f) f)
	          (padd (pneg x f) (pneg y f) f)))
  :hints (("Goal" :use (pneg-padd-*))))

(defthmd pmul-pneg
  (implies (and (fieldp f)
                (polyp x f) (polyp y f))
	   (equal (pmul (pneg x f) y f)
	          (pneg (pmul x y f) f)))
  :hints (("Goal" :use (pmul-pneg-*))))

(defthmd pdistrib-2
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f))
	   (equal (pmul (padd y z f) x f)
	          (padd (pmul y x f) (pmul z x f) f)))
  :hints (("Goal" :use (pdistrib-2-*))))

(defthmd degree-padd-bound
  (<= (degree (padd x y f))
      (max (degree x) (degree y)))
  :hints (("Goal" :use (degree-padd-bound-*))))

(defthmd degree-padd-diff
  (implies (and (polyp x f) (polyp y f) (not (= (degree x) (degree y))))
           (equal (degree (padd x y f))
	          (max (degree x) (degree y))))
  :hints (("Goal" :use (degree-padd-diff-*))))

(defthmd degree-padd-less
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
		(= (degree x) (degree y)) (posp (degree x))
		(equal (car y) (fneg (car x) f)))
	   (< (degree (padd x y f)) (degree x)))
  :hints (("Goal" :use (degree-padd-less-*))))

(defthm degree-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
           (equal (degree (pmul x y f))
	          (+ (degree x) (degree y))))
  :hints (("Goal" :use (degree-pmul-*))))

(defthm pmul-nonzero
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(not (equal x (pzero f)))
		(not (equal y (pzero f))))
	   (not (equal (pmul x y f) (pzero f))))
  :hints (("Goal" :use (pmul-nonzero-*))))

(defthmd car-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (equal (car (pmul x y f))
	          (fmul (car x) (car y) f)))
  :hints (("Goal" :use (car-pmul-*))))

(defthmd degree-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (>= (degree y) 1))
	   (and (polyp (prem x y f) f)
	        (< (degree (prem x y f))
		   (degree y))))
  :hints (("Goal" :use (degree-prem-*))))

(defund precip (x f)
  (list (frecip (car x) f)))

(defthmd pmul-precip
  (implies (and (fieldp f)
                (polyp x f) (pconstp x) (not (equal x (pzero f))))
           (let ((r (precip x f)))
	     (and (polyp r f)
	          (pconstp r)
		  (not (equal r (pzero f)))
		  (equal (pmul x r f) (pone f)))))
  :hints (("Goal" :use (pmul-precip-*))))

;;-------------------------------------------
;; Multiplication by constants and monomials
;;-------------------------------------------

(defthmd polyp-cmul
  (implies (and (fieldp f) 
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (let ((p (cmul c x f)))
	     (and (polyp p f)
	          (equal (degree p) (degree x))
		  (equal (car p) (fmul c (car x) f)))))
  :hints (("Goal" :use (polyp-cmul-*))))

(defthmd cmul-cmul
  (implies (and (fieldp f)
                (feltp c f) (not (equal c (fzero f)))
		(feltp d f) (not (equal d (fzero f)))
                (polyp x f))
	   (equal (cmul c (cmul d x f) f)
	          (cmul (fmul c d f) x f)))
  :hints (("Goal" :use (cmul-cmul-*))))

(defthmd cmul-append
  (implies (not (equal c (fzero f)))
           (equal (cmul c (append l m) f)
                  (append (cmul c l f) (cmul c m f)))))

(defthmd pneg-cmul
  (implies (and (fieldp f)
                (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (cmul c x f) f)
	          (cmul c (pneg x f) f)))
  :hints (("Goal" :use (pneg-cmul-*))))

(defthmd cmul-pmul
  (implies (and (fieldp f)
                (feltp c f) (polyp x f) (polyp y f))
	   (equal (cmul c (pmul x y f) f)
	          (pmul (cmul c x f) y f)))
  :hints (("Goal" :use (cmul-pmul-*))))

(defthmd cmul-padd
  (implies (and (fieldp f)
		(polyp x f) (polyp y f) (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (padd x y f) f)
	          (padd (cmul c x f) (cmul c y f) f)))
  :hints (("Goal" :use (cmul-padd-*))))

(defthmd pmul-constant
  (implies (and (polyp x f) (not (consp (cdr x)))
		(polyp y f) (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pmul x y f)
	          (cmul (car x) y f))))

(defun fzero-list (k f)
  (if (zp k)
      ()
    (cons (fzero f) (fzero-list (1- k) f))))

(defthm pneg-fzero-list
  (implies (and (fieldp f) (natp k))
           (equal (pneg (fzero-list k f) f)
	          (fzero-list k f)))
  :hints (("Goal" :use (pneg-fzero-list-*))))

(defthmd pshift-rewrite
  (implies (and (polyp x f) (natp k))
           (equal (pshift x k f)
	          (append x (fzero-list k f)))))

(defthmd pneg-pshift
  (implies (and (fieldp f)
                (natp k) (polyp x f) (feltp c f) (not (equal c (fzero f))))
           (equal (pneg (pshift (cmul c x f) k f) f)
	          (pshift (cmul c (pneg x f) f) k f)))
  :hints (("Goal" :use (pneg-pshift-*))))

(defthmd cmul-pshift
  (implies (and (fieldp f)
                (polyp x f) (natp k)
                (feltp c f) (not (equal c (fzero f))))
	   (equal (cmul c (pshift x k f) f)
	          (pshift (cmul c x f) k f)))
  :hints (("Goal" :use (cmul-pshift-*))))

(defthm polyp-pshift
  (implies (and (fieldp f) (natp k) (polyp x f) (not (equal x (pzero f))))
           (let ((p (pshift x k f)))
             (and (polyp p f)
	          (equal (degree p) (+ k (degree x)))
		  (equal (car p) (car x))))))

(defthmd padd-pshift
  (implies (and (fieldp f)
		(polyp x f) (polyp y f) (natp k)
		(not (equal (padd x y f) (pzero f))))
	   (equal (padd (pshift x k f) (pshift y k f) f)
	          (pshift (padd x y f) k f)))
  :hints (("Goal" :use (padd-pshift-*))))

(defthmd pshift-pmul
  (implies (and (fieldp f)
                (natp k) (polyp x f) (polyp y f)
		(not (equal x (pzero f))) (not (equal y (pzero f))))
	   (equal (pshift (pmul x y f) k f)
	          (pmul x (pshift y k f) f)))
  :hints (("Goal" :use (pshift-pmul-*))))

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
	          (pshift (cmul c y f) k f)))
  :hints (("Goal" :use (pmul-monomial-*))))

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
  :rule-classes ()
  :hints (("Goal" :use (pdivision-*))))

(defthm pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (let ((q (pquot x y f)) (r (prem x y f)))
	     (and (polyp q f) (polyp r f)
	          (equal (padd (pmul y q f) r f) x)
		  (if (pconstp y)
		      (equal r (pzero f))
		    (< (degree r) (degree y))))))
  :hints (("Goal" :use (pquot-prem-*))))

(defthm polyp-pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (and (polyp (pquot x y f) f)
	        (polyp (prem x y f) f)))
  :hints (("Goal" :use (polyp-pquot-prem-*))))

(defthm pconstp-prem-pzero
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (pconstp y) (not (equal y (pzero f))))
           (equal (prem x y f) (pzero f)))
  :hints (("Goal" :use (pconstp-prem-pzero-*))))

(defthmd prem-padd-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd x (prem y z f) f) z f)
                  (prem (padd x y f) z f)))
  :hints (("Goal" :use (prem-padd-prem-*))))

(defthmd prem-padd-prem-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
           (equal (prem (padd (prem x z f) y f) z f)
                  (prem (padd x y f) z f)))
  :hints (("Goal" :use (prem-padd-prem-comm-*))))

(defthmd pquot-prem-unique
 (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(polyp q f) (polyp r f)
		(equal x (padd (pmul y q f) r f))
		(if (pconstp y)
		    (equal r (pzero f))
		  (< (degree r) (degree y))))
           (and (equal (pquot x y f) q)
	        (equal (prem x y f) r)))
   :hints (("Goal" :use (pquot-prem-unique-*))))

(defthmd prem-equal
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(< (degree x) (degree y)))
	   (equal (prem x y f)
	          x))
  :hints (("Goal" :use (prem-equal-*))))

(defthmd prem+mult
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp a f))
	   (equal (prem (padd (pmul y a f) x f) y f)
	          (prem x y f)))
  :hints (("Goal" :use (prem+mult-*))))

(defthmd prem-padd-prem-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	  (equal (prem (padd (prem x z f) (prem y z f) f) z f)
	         (padd (prem x z f) (prem y z f) f)))
  :hints (("Goal" :use (prem-padd-prem-prem-*))))

(defthmd prem-pmul-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul x (prem y z f) f) z f)
	          (prem (pmul x y f) z f)))
  :hints (("Goal" :use (prem-pmul-prem-*))))
			
(defthmd prem-pmul-prem-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal z (pzero f))))
	   (equal (prem (pmul (prem x z f) y f) z f)
	          (prem (pmul x y f) z f)))
  :hints (("Goal" :use (prem-pmul-prem-comm-*))))

(defthmd cmul-pquot-prem
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot x (cmul c y f) f)
	               (cmul (frecip c f) (pquot x y f) f))
		(equal (prem x (cmul c y f) f)
		       (prem x y f))))
  :hints (("Goal" :use (cmul-pquot-prem-*))))

(defthmd pquot-prem-cmul
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
	   (and (equal (pquot (cmul c x f) y f)
	               (cmul c (pquot x y f) f))
		(equal (prem (cmul c x f) y f)
	               (cmul c (prem x y f) f))))
  :hints (("Goal" :use (pquot-prem-cmul-*))))

;;--------------
;; Divisibility
;;--------------

(defthmd pdivides-cmul
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
		(feltp c f) (not (equal c (fzero f))))
	   (iff (pdivides y x f)
	        (pdivides y (cmul c x f) f)))
   :hints (("Goal" :use (pdivides-cmul-*))))

(defthmd cmul-divides
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (not (equal y (pzero f)))
		(feltp c f) (not (equal c (fzero f))))
           (iff (pdivides (cmul c y f) x f)
	        (pdivides y x f)))
  :hints (("Goal" :use (cmul-divides-*))))

(defthmd pconstp-pdivides
  (implies (pconstp y)
	   (pdivides y x f))
  :hints (("Goal" :use (pconstp-pdivides-*))))

(defthmd pdivides-pzero
  (implies (and (fieldp f) 
                (polyp x f))
	   (pdivides x (pzero f) f))
  :hints (("Goal" :use (pdivides-pzero-*))))

(defthmd pdivides-equal-degree
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (equal (degree x) (degree y))
		(pdivides x y f))
	   (pdivides y x f))
  :hints (("Goal" :use (pdivides-equal-degree-*))))

(defthm pzero-pdivides
  (pdivides (pzero f) x f)
  :hints (("Goal" :use (pzero-pdivides-*))))

(defthmd pdivides-pquot
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (not (equal x (pzero f)))
		(pdivides x y f))
	   (equal (pmul x (pquot y x f) f)
	          y))
  :hints (("Goal" :use (pdivides-pquot-*))))

(defthmd pdivides-self
  (implies (and (fieldp f) 
                (polyp x f))
	   (pdivides x x f))
  :hints (("Goal" :use (pdivides-self-*))))

(defthmd pdivides-multiple
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f))
	   (pdivides x (pmul x y f) f))
  :hints (("Goal" :use (pdivides-multiple-*))))

(defthmd pdivides-padd
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f) (pdivides x z f))
	   (pdivides x (padd y z f) f))
  :hints (("Goal" :use (pdivides-padd-*))))

(defthmd pdivides-pmul
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
		(pdivides x y f))
	   (pdivides x (pmul y z f) f))
  :hints (("Goal" :use (pdivides-pmul-*))))

(defthmd pdivides-transitive
  (implies (and (fieldp f)
                (polyp x f) (polyp y f) (polyp z f) (not (equal y (pzero f)))
		(pdivides x y f) (pdivides y z f))
	   (pdivides x z f))
  :hints (("Goal" :use (pdivides-transitive-*))))

(defthmd pdivides-prem-equal
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f) (not (equal x (pzero f))))
	   (iff (pdivides x (padd y (pneg z f) f) f)
		(equal (prem y x f) (prem z x f))))
  :hints (("Goal" :use (pdivides-prem-equal-*))))

(defthmd pdivides-degree
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (pdivides x y f) (not (equal y (pzero f))))
	   (<= (degree x) (degree y)))
  :hints (("Goal" :use (pdivides-degree-*))))

;;-------------------------
;; Greatest common divisor
;;-------------------------

(defthmd polyp-pgcd
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (polyp (pgcd x y f) f))
  :hints (("Goal" :use (polyp-pgcd-*))))

(defthmd pgcd-monic
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))) (not (equal y (pzero f))))
           (monicp (pgcd x y f) f))
  :hints (("Goal" :use (pgcd-monic-*))))

(defthmd pgcd-nonzero
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))) (not (equal y (pzero f))))
	   (not (equal (pgcd x y f) (pzero f))))
  :hints (("Goal" :use (pgcd-nonzero-*))))

(defthmd pgcd-divides
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (and (pdivides (pgcd x y f) x f)
	        (pdivides (pgcd x y f) y f)))
  :hints (("Goal" :use (pgcd-divides-*))))

(defthmd divides-pgcd
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f) (polyp z f)
                (not (and (equal x (pzero f)) (equal y (pzero f))))
		(pdivides z x f) (pdivides z y f))
	   (pdivides z (pgcd x y f) f))
  :hints (("Goal" :use (divides-pgcd-*))))

(defthmd pgcd-comm
  (implies (and (fieldp f)
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (equal (pgcd x y f) (pgcd y x f)))
  :hints (("Goal" :use (pgcd-comm-*))))

(defthmd pgcd-linear-combination
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (and (equal x (pzero f)) (equal y (pzero f)))))
	   (let ((r (rp x y f))
	         (s (sp x y f)))
	     (and (polyp r f)
	          (polyp s f)
	  	  (equal (padd (pmul r x f) (pmul s y f) f)
		         (pgcd x y f)))))
  :hints (("Goal" :use (pgcd-linear-combination-*))))

;;-------------------------
;; Irreducuble polynomials
;;-------------------------

(defthmd irreduciblep-no-factor
  (implies (and (fieldp f)
                (polyp p f) (polyp x f)
		(irreduciblep p f)
		(< (degree x) (degree p))
		(pdivides x p f))
	   (pconstp x))
  :hints (("Goal" :use (irreduciblep-no-factor-*))))

(defthmd peuclid
  (implies (and (fieldp f) 
                (polyp p f) (polyp x f) (polyp y f)
		(irreduciblep p f) (pdivides p (pmul x y f) f))
	   (or (pdivides p x f) (pdivides p y f)))
  :hints (("Goal" :use (peuclid-*))))

(defthmd pgcd-irreduciblep
  (implies (and (fieldp f) 
                (polyp p f) (polyp x f)
		(irreduciblep p f) (not (pdivides p x f)))
	   (equal (pgcd p x f) (pone f)))
  :hints (("Goal" :use (pgcd-irreduciblep-*))))
